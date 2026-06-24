//! A tiny, synchronous HTTP/1.1 reader/writer over `std::net`. This is deliberately
//! minimal: the server is loopback-only and thin, so a dependency-free request parser with
//! a hard body-size cap is simpler to audit than pulling in an async stack.

use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;

pub struct Request {
    pub method: String,
    pub path: String,
    pub body: Vec<u8>,
}

pub enum ReadError {
    /// Malformed request line/headers.
    Malformed,
    /// Body exceeded the configured maximum.
    TooLarge,
    /// Underlying socket error.
    Io,
}

/// Read one request from the stream, rejecting bodies larger than `max_body`.
pub fn read_request(stream: &TcpStream, max_body: usize) -> Result<Request, ReadError> {
    let mut reader = BufReader::new(stream);

    // Request line.
    let mut line = String::new();
    if reader.read_line(&mut line).map_err(|_| ReadError::Io)? == 0 {
        return Err(ReadError::Malformed);
    }
    let mut parts = line.split_whitespace();
    let method = parts.next().ok_or(ReadError::Malformed)?.to_string();
    let path = parts.next().ok_or(ReadError::Malformed)?.to_string();

    // Headers, collecting Content-Length.
    let mut content_length = 0usize;
    loop {
        let mut header = String::new();
        if reader.read_line(&mut header).map_err(|_| ReadError::Io)? == 0 {
            break;
        }
        let trimmed = header.trim_end();
        if trimmed.is_empty() {
            break; // end of headers
        }
        if let Some((name, value)) = trimmed.split_once(':') {
            if name.trim().eq_ignore_ascii_case("content-length") {
                content_length = value.trim().parse().map_err(|_| ReadError::Malformed)?;
            }
        }
    }

    if content_length > max_body {
        return Err(ReadError::TooLarge);
    }

    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body).map_err(|_| ReadError::Io)?;

    Ok(Request { method, path, body })
}

/// Write a JSON response with the given status code.
pub fn write_json(stream: &mut TcpStream, status: u16, body: &str) {
    let reason = match status {
        200 => "OK",
        400 => "Bad Request",
        404 => "Not Found",
        405 => "Method Not Allowed",
        408 => "Request Timeout",
        413 => "Payload Too Large",
        500 => "Internal Server Error",
        _ => "OK",
    };
    let response = format!(
        "HTTP/1.1 {status} {reason}\r\n\
         Content-Type: application/json\r\n\
         Content-Length: {}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        body.len()
    );
    let _ = stream.write_all(response.as_bytes());
    let _ = stream.flush();
}

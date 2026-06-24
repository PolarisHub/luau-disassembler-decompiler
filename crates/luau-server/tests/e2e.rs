//! End-to-end test: spawn the real server binary, POST bytecode, and check the JSON.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use base64::engine::general_purpose::STANDARD as BASE64;
use base64::Engine;
use serde_json::Value;

/// Kills the child server when dropped so a failing assertion never leaks a process.
struct ServerGuard(Child);
impl Drop for ServerGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn free_port() -> u16 {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    l.local_addr().unwrap().port()
}

fn corpus_bytes(name: &str) -> Vec<u8> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
        .join("bytecode")
        .join(name);
    std::fs::read(p).unwrap()
}

fn start_server() -> (ServerGuard, String) {
    let port = free_port();
    let addr = format!("127.0.0.1:{port}");
    let child = Command::new(env!("CARGO_BIN_EXE_luau-server"))
        .arg(&addr)
        .spawn()
        .expect("spawn server");
    let guard = ServerGuard(child);

    // Wait until it accepts connections.
    let deadline = Instant::now() + Duration::from_secs(10);
    while Instant::now() < deadline {
        if TcpStream::connect(&addr).is_ok() {
            return (guard, addr);
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    panic!("server did not start listening on {addr}");
}

/// Minimal HTTP client: send a request, return (status, body).
fn request(addr: &str, method: &str, path: &str, body: &str) -> (u16, String) {
    let mut stream = TcpStream::connect(addr).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let req = format!(
        "{method} {path} HTTP/1.1\r\nHost: localhost\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    stream.write_all(req.as_bytes()).unwrap();

    let mut raw = Vec::new();
    stream.read_to_end(&mut raw).unwrap();
    let text = String::from_utf8_lossy(&raw);
    let status: u16 = text
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let body = text.split("\r\n\r\n").nth(1).unwrap_or("").to_string();
    (status, body)
}

fn post_bytecode(addr: &str, path: &str, bytecode: &[u8]) -> (u16, Value) {
    let payload = serde_json::json!({ "bytecode": BASE64.encode(bytecode) }).to_string();
    let (status, body) = request(addr, "POST", path, &payload);
    let json = serde_json::from_str(&body).unwrap_or(Value::Null);
    (status, json)
}

#[test]
fn end_to_end_disassemble_decompile_health_and_errors() {
    let (_guard, addr) = start_server();
    let bytecode = corpus_bytes("03_if_else.luauc");

    // /health
    let (status, body) = request(&addr, "GET", "/health", "");
    assert_eq!(status, 200, "health body: {body}");
    let health: Value = serde_json::from_str(&body).unwrap();
    assert_eq!(health["status"], "ok");

    // /disassemble
    let (status, json) = post_bytecode(&addr, "/disassemble", &bytecode);
    assert_eq!(status, 200, "disasm: {json}");
    assert_eq!(json["version"], 7);
    assert!(json["protos"].as_array().unwrap().len() >= 2);
    let listing = json["protos"][0]["listing"].as_str().unwrap();
    assert!(listing.contains("JUMPIFNOTLT"), "listing: {listing}");

    // /decompile
    let (status, json) = post_bytecode(&addr, "/decompile", &bytecode);
    assert_eq!(status, 200, "decompile: {json}");
    assert!(json["source"].as_str().unwrap().contains("function"));
    assert!(json["partial"].is_boolean());

    // Bad base64 -> structured 400.
    let (status, body) = request(&addr, "POST", "/disassemble", r#"{"bytecode":"!!!notb64"}"#);
    assert_eq!(status, 400, "expected 400, body: {body}");
    let json: Value = serde_json::from_str(&body).unwrap();
    assert_eq!(json["error"]["stage"], "request");

    // Garbage bytecode -> structured parse error with an offset.
    let (status, json) = post_bytecode(&addr, "/disassemble", &[0x02, 0x00, 0x00]);
    assert_eq!(status, 400, "garbage: {json}");
    assert_eq!(json["error"]["stage"], "parse");

    // Unknown route -> 404.
    let (status, _) = request(&addr, "GET", "/nope", "");
    assert_eq!(status, 404);
}

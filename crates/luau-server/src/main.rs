//! `luau-server`: a thin, loopback-only HTTP server exposing the disassembler and
//! decompiler. It only wires the library crates together and handles I/O, limits, and
//! errors. Bytecode in (base64), analysis out (JSON).
//!
//! Endpoints:
//!   GET  /health      -> { status, version, bytecode_versions }
//!   POST /disassemble -> { version, protos:[...], diagnostics }
//!   POST /decompile   -> { source, partial, per_proto, diagnostics }

mod http;

use std::net::{TcpListener, TcpStream};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use base64::engine::general_purpose::STANDARD as BASE64;
use base64::Engine;
use serde_json::{json, Value};

use luau_bytecode::{LBC_VERSION_MAX, LBC_VERSION_MIN};

/// The result of handling a request: an HTTP status and a JSON body, or a structured error.
type Handled = Result<(u16, String), ApiError>;

/// Maximum request body (base64 bytecode). Generous for real chunks, bounded against abuse.
const MAX_BODY: usize = 16 * 1024 * 1024;
/// Per-request analysis budget. Parsing/analysis is linear and bounded, so this is a
/// backstop, not the normal path.
const TIME_BUDGET: Duration = Duration::from_secs(10);

fn main() {
    let addr = std::env::args()
        .nth(1)
        .or_else(|| std::env::var("LUAU_SERVER_ADDR").ok())
        .unwrap_or_else(|| "127.0.0.1:7331".to_string());

    // Loopback only. Refuse to bind a non-loopback address even if asked.
    if !is_loopback(&addr) {
        eprintln!("refusing to bind non-loopback address {addr}; use 127.0.0.1");
        std::process::exit(1);
    }

    let listener = match TcpListener::bind(&addr) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("bind {addr}: {e}");
            std::process::exit(1);
        }
    };
    println!("luau-server listening on http://{addr}");

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                thread::spawn(move || handle_connection(stream));
            }
            Err(e) => eprintln!("accept error: {e}"),
        }
    }
}

fn is_loopback(addr: &str) -> bool {
    addr.starts_with("127.") || addr.starts_with("localhost:") || addr.starts_with("[::1]")
}

fn handle_connection(mut stream: TcpStream) {
    let request = match http::read_request(&stream, MAX_BODY) {
        Ok(r) => r,
        Err(http::ReadError::TooLarge) => {
            return reply_error(&mut stream, 413, "request", "request body too large", None);
        }
        Err(_) => {
            return reply_error(&mut stream, 400, "request", "malformed HTTP request", None);
        }
    };

    // A panic anywhere in handling must become a structured 500, never crash the process.
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        route(&request.method, &request.path, &request.body)
    }));

    match outcome {
        Ok(Ok((status, body))) => http::write_json(&mut stream, status, &body),
        Ok(Err(err)) => reply_error(
            &mut stream,
            err.status,
            &err.stage,
            &err.message,
            err.offset,
        ),
        Err(_) => reply_error(
            &mut stream,
            500,
            "internal",
            "internal error (panic caught)",
            None,
        ),
    }
}

struct ApiError {
    status: u16,
    stage: String,
    message: String,
    offset: Option<usize>,
}

fn err(status: u16, stage: &str, message: impl Into<String>) -> ApiError {
    ApiError {
        status,
        stage: stage.to_string(),
        message: message.into(),
        offset: None,
    }
}

fn route(method: &str, path: &str, body: &[u8]) -> Handled {
    match (method, path) {
        ("GET", "/health") => Ok((200, health_json())),
        ("POST", "/disassemble") => run_budgeted(body.to_vec(), handle_disassemble),
        ("POST", "/decompile") => run_budgeted(body.to_vec(), handle_decompile),
        ("GET", _) | ("POST", _) => Err(err(404, "request", format!("no route for {path}"))),
        _ => Err(err(405, "request", "method not allowed")),
    }
}

/// Run a handler on a worker thread with a time budget. The worker owns the input bytes.
fn run_budgeted(body: Vec<u8>, handler: fn(&[u8]) -> Handled) -> Handled {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let result = handler(&body);
        let _ = tx.send(result);
    });
    match rx.recv_timeout(TIME_BUDGET) {
        Ok(result) => result,
        Err(_) => Err(err(408, "timeout", "analysis exceeded time budget")),
    }
}

fn health_json() -> String {
    json!({
        "status": "ok",
        "service": "luau-server",
        "bytecode_versions": { "min": LBC_VERSION_MIN, "max": LBC_VERSION_MAX },
    })
    .to_string()
}

/// Decode the `{ bytecode: base64, options? }` request body into raw bytecode + options.
fn decode_request(body: &[u8]) -> Result<(Vec<u8>, Value), ApiError> {
    let value: Value = serde_json::from_slice(body)
        .map_err(|e| err(400, "request", format!("invalid JSON: {e}")))?;
    let b64 = value
        .get("bytecode")
        .and_then(|v| v.as_str())
        .ok_or_else(|| err(400, "request", "missing string field `bytecode` (base64)"))?;
    let bytes = BASE64
        .decode(b64.trim())
        .map_err(|e| err(400, "request", format!("invalid base64: {e}")))?;
    let options = value.get("options").cloned().unwrap_or(Value::Null);
    Ok((bytes, options))
}

fn option_bool(options: &Value, key: &str, default: bool) -> bool {
    options
        .get(key)
        .and_then(|v| v.as_bool())
        .unwrap_or(default)
}

/// Turn a reader error into an ApiError carrying the byte offset.
fn reader_error(e: luau_bytecode::Error) -> ApiError {
    use luau_bytecode::ErrorKind;
    let stage = match e.kind {
        ErrorKind::CompileError { .. } => "compile-error-input",
        _ => "parse",
    };
    ApiError {
        status: 400,
        stage: stage.to_string(),
        message: e.to_string(),
        offset: Some(e.offset),
    }
}

fn handle_disassemble(body: &[u8]) -> Handled {
    let (bytes, options) = decode_request(body)?;
    let (module, multiplier) = luau_bytecode::parse_normalized(&bytes).map_err(reader_error)?;
    let disasm = luau_disasm::disassemble(&module);

    let include_listing = option_bool(&options, "include_disassembly", true);
    let protos: Vec<Value> = disasm
        .protos
        .iter()
        .map(|p| {
            let listing = if include_listing {
                Some(proto_listing_text(p))
            } else {
                None
            };
            json!({
                "index": p.index,
                "name": p.name,
                "num_params": p.num_params,
                "num_upvalues": p.num_upvalues,
                "is_vararg": p.is_vararg,
                "max_stack_size": p.max_stack_size,
                "line_defined": p.line_defined,
                "instruction_count": p.lines.len(),
                "listing": listing,
            })
        })
        .collect();

    let response = json!({
        "version": module.version,
        "types_version": module.types_version,
        "main_proto": module.main_proto,
        "proto_count": module.protos.len(),
        "opcode_multiplier": multiplier,
        "protos": protos,
        "diagnostics": opcode_diagnostics(multiplier),
    });
    Ok((200, response.to_string()))
}

/// A diagnostic noting opcode deobfuscation, when it happened.
fn opcode_diagnostics(multiplier: u32) -> Vec<String> {
    if multiplier == 1 {
        Vec::new()
    } else {
        vec![format!(
            "deobfuscated Roblox-encoded opcodes (decode multiplier {multiplier})"
        )]
    }
}

fn handle_decompile(body: &[u8]) -> Handled {
    let (bytes, options) = decode_request(body)?;
    let (module, multiplier) = luau_bytecode::parse_normalized(&bytes).map_err(reader_error)?;
    let result = luau_decompile::decompile(&module);

    let per_proto: Vec<Value> = result
        .per_proto
        .iter()
        .map(|p| {
            json!({
                "index": p.index,
                "name": p.name,
                "partial": p.partial,
                "notes": p.notes,
            })
        })
        .collect();

    let mut response = json!({
        "source": result.source,
        "partial": result.partial,
        "opcode_multiplier": multiplier,
        "per_proto": per_proto,
        "diagnostics": opcode_diagnostics(multiplier),
    });

    // Optionally include the raw disassembly alongside the decompile.
    if option_bool(&options, "include_disassembly", false) {
        let disasm = luau_disasm::disassemble(&module);
        response["disassembly"] = Value::String(disasm.to_string());
    }

    Ok((200, response.to_string()))
}

/// Render one proto's instruction listing (PC, label, text, line) as text.
fn proto_listing_text(p: &luau_disasm::ProtoDisasm) -> String {
    let mut out = String::new();
    for line in &p.lines {
        let label = match line.label {
            Some(id) => format!("L{id}:"),
            None => String::new(),
        };
        let anno = match line.line_no {
            Some(n) => format!("  ; line {n}"),
            None => String::new(),
        };
        out.push_str(&format!(
            "{:>5}  {:<5}{}{}\n",
            line.pc, label, line.text, anno
        ));
    }
    out
}

fn reply_error(
    stream: &mut TcpStream,
    status: u16,
    stage: &str,
    message: &str,
    offset: Option<usize>,
) {
    let body = json!({
        "error": { "stage": stage, "message": message, "offset": offset },
    });
    http::write_json(stream, status, &body.to_string());
}

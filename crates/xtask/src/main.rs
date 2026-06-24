//! Developer CLI for eyeballing bytecode.
//!
//! Usage:
//!   cargo run -p xtask -- disasm <file.luauc>   # resolved instruction listing
//!   cargo run -p xtask -- cfg    <file.luauc>   # per-proto basic-block + dominator listing

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: xtask <disasm|cfg> <file.luauc>");
        return ExitCode::FAILURE;
    }
    let cmd = args[1].as_str();
    let path = &args[2];

    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let module = match luau_bytecode::parse_and_validate(&bytes) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("parse {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    match cmd {
        "disasm" => print!("{}", luau_disasm::disassemble(&module)),
        "cfg" => {
            for (i, proto) in module.protos.iter().enumerate() {
                let name = module
                    .resolve(proto.debug_name)
                    .map(|c| c.into_owned())
                    .unwrap_or_else(|| "??".to_string());
                println!("== Function {i} ({name}) ==");
                print!("{}", luau_ir::block_listing(&module, proto));
                println!();
            }
        }
        other => {
            eprintln!("unknown command: {other}");
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}

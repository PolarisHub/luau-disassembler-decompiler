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

    // Parse only (no validation): `robloxmap` deliberately works on bytecode whose opcodes
    // don't validate against the open-source numbering.
    let mut module = match luau_bytecode::parse(&bytes) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("parse {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    // Deobfuscate Roblox opcode encoding (no-op for standard bytecode).
    if cmd != "robloxmap" {
        let d = luau_bytecode::normalize_opcodes(&mut module);
        if d != 1 {
            eprintln!("-- opcode multiplier: {d} (Roblox-encoded bytecode)");
        }
    }

    match cmd {
        // Brute-force the opcode decode multiplier (Roblox encodes opcodes as op*K mod 256).
        "robloxmap" => {
            use luau_bytecode::opcode::{insn_op, Opcode};
            let mut found = false;
            for d in (1u32..256).step_by(2) {
                let mut ok = true;
                let mut count = 0usize;
                'protos: for proto in &module.protos {
                    let code = &proto.code;
                    let mut pc = 0;
                    while pc < code.len() {
                        let real = (insn_op(code[pc]) as u32).wrapping_mul(d) & 0xff;
                        match Opcode::from_u8(real as u8) {
                            Some(op) => {
                                pc += op.length().max(1);
                                count += 1;
                            }
                            None => {
                                ok = false;
                                break 'protos;
                            }
                        }
                    }
                    if pc != code.len() {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    println!("decode multiplier D={d} validates all {count} instructions across {} protos", module.protos.len());
                    found = true;
                }
            }
            if !found {
                println!("no single opcode multiplier validates; encoding is not a simple multiply");
            }
        }
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
        "decompile" => {
            let result = luau_decompile::decompile(&module);
            print!("{}", result.source);
            eprintln!("\n-- partial: {}", result.partial);
        }
        other => {
            eprintln!("unknown command: {other}");
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}

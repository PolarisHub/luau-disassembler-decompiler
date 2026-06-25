//! Developer CLI for eyeballing bytecode.
//!
//! Usage:
//!   cargo run -p xtask -- disasm     <file.luauc>   # resolved instruction listing
//!   cargo run -p xtask -- cfg        <file.luauc>   # per-proto CFG + dominators
//!   cargo run -p xtask -- decompile  <file.luauc>   # reconstructed Luau
//!   cargo run -p xtask -- robloxmap  <file.luauc>   # probe opcode decode multipliers

use std::process::ExitCode;

fn usage() {
    eprintln!("usage: xtask <disasm|cfg|decompile|robloxmap> <file.luauc>");
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        usage();
        return ExitCode::FAILURE;
    }
    let cmd = args[1].as_str();
    let path = &args[2];
    if !matches!(cmd, "disasm" | "cfg" | "decompile" | "robloxmap") {
        eprintln!("unknown command: {cmd}");
        usage();
        return ExitCode::FAILURE;
    }

    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let module = if cmd == "robloxmap" {
        // Parse only (no validation): `robloxmap` deliberately works on bytecode whose
        // opcodes don't validate against the open-source numbering.
        match luau_bytecode::parse(&bytes) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("parse {path}: {e}");
                return ExitCode::FAILURE;
            }
        }
    } else {
        match luau_bytecode::parse_normalized(&bytes) {
            Ok((m, multiplier)) => {
                if multiplier != 1 {
                    eprintln!("-- opcode multiplier: {multiplier} (Roblox-encoded bytecode)");
                }
                m
            }
            Err(e) => {
                eprintln!("parse/validate {path}: {e}");
                return ExitCode::FAILURE;
            }
        }
    };

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
                println!(
                    "no single opcode multiplier validates; encoding is not a simple multiply"
                );
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
            for report in &result.per_proto {
                if report.partial || !report.notes.is_empty() {
                    let name = report.name.as_deref().unwrap_or("??");
                    eprintln!(
                        "-- proto {} ({name}) partial: {}",
                        report.index, report.partial
                    );
                    for note in &report.notes {
                        eprintln!("--   note: {note}");
                    }
                }
            }
        }
        _ => unreachable!("validated command"),
    }
    ExitCode::SUCCESS
}

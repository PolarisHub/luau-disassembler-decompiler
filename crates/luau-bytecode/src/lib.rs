//! `luau-bytecode`: an exact, validated reader for Luau bytecode (the compiled chunk).
//!
//! Bytes in, a typed [`Module`] out. This crate does no analysis — it only deserializes
//! and validates, mirroring `VM/src/lvmload.cpp` from Luau 0.726. The input is untrusted,
//! so every read is bounds-checked and every fallible operation returns [`Result`]: the
//! reader never panics, never reads out of bounds, and never allocates on an unchecked
//! length field.
//!
//! Supported bytecode versions: [`LBC_VERSION_MIN`]..=[`LBC_VERSION_MAX`] (3..=11).

mod error;
mod model;
mod parse;
mod reader;
mod validate;

pub mod opcode;

pub use error::{Error, ErrorKind, Result};
pub use model::*;
pub use parse::parse;
pub use validate::validate;

/// Parse and then validate a chunk in one call.
pub fn parse_and_validate(data: &[u8]) -> Result<Module> {
    let module = parse(data)?;
    validate(&module)?;
    Ok(module)
}

/// Parse, normalize opcodes (handling Roblox's opcode obfuscation), then validate.
/// Returns the module and the detected opcode multiplier (1 for standard/open-source
/// bytecode, otherwise the value used to deobfuscate, e.g. 203 for Roblox).
pub fn parse_normalized(data: &[u8]) -> Result<(Module, u32)> {
    let mut module = parse(data)?;
    let multiplier = normalize_opcodes(&mut module);
    validate(&module)?;
    Ok((module, multiplier))
}

/// Detect the opcode decode multiplier: the odd `D` such that `realOp = encodedOp * D mod
/// 256` makes every instruction in every proto a known opcode with a synced program counter.
///
/// Open-source Luau bytecode uses `D = 1`. Roblox obfuscates opcodes by multiplying them by
/// a constant (`encoded = real * 227 mod 256`), so its bytecode decodes with `D = 203`
/// (227's inverse mod 256). The multiplier can change between Roblox versions, so we brute-
/// force it per chunk (128 candidates) rather than hard-coding one — `D = 1` is preferred
/// when it validates so normal bytecode is never altered.
pub fn detect_opcode_multiplier(module: &Module) -> u32 {
    let validates = |d: u32| -> bool {
        for proto in &module.protos {
            let code = &proto.code;
            let mut pc = 0;
            while pc < code.len() {
                let real = (opcode::insn_op(code[pc]) as u32).wrapping_mul(d) & 0xff;
                match opcode::Opcode::from_u8(real as u8) {
                    Some(op) => pc += op.length().max(1),
                    None => return false,
                }
                if pc > code.len() {
                    return false;
                }
            }
            if pc != code.len() {
                return false;
            }
        }
        true
    };

    if validates(1) {
        return 1;
    }
    let mut first = None;
    for d in (1u32..256).step_by(2) {
        if validates(d) {
            // Prefer Roblox's well-known constant when ambiguous; otherwise take the first
            // multiplier that validates the whole module.
            if d == 203 {
                return 203;
            }
            first.get_or_insert(d);
        }
    }
    first.unwrap_or(1)
}

/// Rewrite each instruction's opcode byte to the standard numbering using the detected
/// multiplier, so the rest of the pipeline (disassembler, IR, decompiler) sees open-source
/// opcodes. AUX words are left untouched. Returns the multiplier applied.
pub fn normalize_opcodes(module: &mut Module) -> u32 {
    let d = detect_opcode_multiplier(module);
    if d == 1 {
        return 1;
    }
    for proto in &mut module.protos {
        let n = proto.code.len();
        let mut pc = 0;
        while pc < n {
            let real = (opcode::insn_op(proto.code[pc]) as u32).wrapping_mul(d) & 0xff;
            proto.code[pc] = (proto.code[pc] & 0xffff_ff00) | real;
            let len = opcode::Opcode::from_u8(real as u8)
                .map(|o| o.length())
                .unwrap_or(1)
                .max(1);
            pc += len;
        }
    }
    d
}

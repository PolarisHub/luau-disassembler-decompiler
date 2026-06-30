//! Post-parse validation of instruction operands.
//!
//! [`parse`](crate::parse) already validates everything needed for memory safety (string,
//! constant, and proto indices in the serialized structures). This pass is the semantic
//! check the spec asks for: walk each proto's instruction stream using the opcode length
//! table (proving the PC stays synced across AUX words), and range-check the constant /
//! child-proto / register operands carried *inside* instructions.

use crate::error::{Error, ErrorKind, Result};
use crate::model::Module;
use crate::opcode::*;

/// Validate every proto in the module. Returns the first problem found, or `Ok` if the
/// whole module is internally consistent.
pub fn validate(module: &Module) -> Result<()> {
    for proto in &module.protos {
        validate_proto(proto)?;
    }
    Ok(())
}

fn validate_proto(proto: &crate::model::Proto) -> Result<()> {
    let code = &proto.code;
    let size_k = proto.constants.len() as u32;
    let size_p = proto.child_protos.len() as u32;
    let max_reg = proto.max_stack_size as u32;

    let mut pc = 0usize;
    while pc < code.len() {
        let word = code[pc];
        let op = Opcode::from_u8(insn_op(word)).ok_or_else(|| {
            // An unknown opcode means we cannot know the instruction length, so the stream
            // is no longer decodable. We support every opcode through version 11, so this
            // is genuinely malformed input.
            Error::new(pc, ErrorKind::UnknownOpcode { op: insn_op(word) })
        })?;

        let len = op.length();
        // The AUX word (when len == 2) must be inside the code array.
        if pc + len > code.len() {
            return Err(Error::new(
                pc,
                ErrorKind::UnexpectedEof {
                    needed: len,
                    available: code.len() - pc,
                },
            ));
        }
        let aux = if len == 2 { Some(code[pc + 1]) } else { None };

        check_operands(pc, op, word, aux, size_k, size_p, max_reg)?;

        pc += len;
    }
    Ok(())
}

fn const_oob(pc: usize, index: u32, count: u32) -> Error {
    Error::new(pc, ErrorKind::ConstantIndexOutOfRange { index, count })
}

fn reg_oob(pc: usize, index: u32, count: u32) -> Error {
    Error::new(pc, ErrorKind::RegisterIndexOutOfRange { index, count })
}

fn check_operands(
    pc: usize,
    op: Opcode,
    word: u32,
    aux: Option<u32>,
    size_k: u32,
    size_p: u32,
    max_reg: u32,
) -> Result<()> {
    use Opcode::*;

    // Constant-index operands carried in the D field.
    let d_is_const = matches!(op, LOADK | DUPTABLE | DUPCLOSURE | GETIMPORT);
    if d_is_const {
        let k = insn_d(word) as u32;
        if k >= size_k {
            return Err(const_oob(pc, k, size_k));
        }
    }

    // Constant-index operands carried in the C field (0..255 range opcodes).
    let c_is_const = matches!(
        op,
        ADDK | SUBK | MULK | DIVK | MODK | POWK | ANDK | ORK | IDIVK
    );
    if c_is_const {
        let k = insn_c(word) as u32;
        if k >= size_k {
            return Err(const_oob(pc, k, size_k));
        }
    }

    // Constant-index operands carried in the B field.
    if matches!(op, SUBRK | DIVRK) {
        let k = insn_b(word) as u32;
        if k >= size_k {
            return Err(const_oob(pc, k, size_k));
        }
    }

    // Constant-index operands carried in the AUX word.
    if let Some(aux) = aux {
        let aux_const: Option<u32> = match op {
            GETGLOBAL | SETGLOBAL | GETTABLEKS | SETTABLEKS | NAMECALL | LOADKX | FASTCALL2K
            | NEWCLASSMEMBER => Some(aux),
            JUMPXEQKN | JUMPXEQKS => Some(aux_kv(aux)),
            GETUDATAKS | SETUDATAKS | NAMECALLUDATA => Some(aux_kv16(aux)),
            _ => None,
        };
        if let Some(k) = aux_const {
            if k >= size_k {
                return Err(const_oob(pc, k, size_k));
            }
        }
    }

    // Child-proto index in NEWCLOSURE.
    if op == NEWCLOSURE {
        let idx = insn_d(word) as u32;
        if idx >= size_p {
            return Err(Error::new(
                pc,
                ErrorKind::ProtoIndexOutOfRange {
                    index: idx,
                    count: size_p,
                },
            ));
        }
    }

    // NEWCLASSMEMBER uses C as the initial member value register.
    if op == NEWCLASSMEMBER {
        let c = insn_c(word) as u32;
        if max_reg > 0 && c >= max_reg {
            return Err(reg_oob(pc, c, max_reg));
        }
    }

    // Register range check for the A field, for opcodes where A is unambiguously a target
    // or source register (it must address a slot within the declared frame). We skip
    // opcodes whose A is not a register (CAPTURE: capture type; FASTCALL*: builtin id;
    // PREPVARARGS: fixed-arg count; JUMPX/COVERAGE/JUMP: no A register).
    if a_is_register(op) {
        let a = insn_a(word) as u32;
        if max_reg > 0 && a >= max_reg {
            return Err(reg_oob(pc, a, max_reg));
        }
    }

    Ok(())
}

/// Whether the A field of this opcode is a register index (vs. a tag/count/builtin id).
/// Conservative: only opcodes where A is definitely a register, so validation never
/// produces a false positive on a non-register field.
fn a_is_register(op: Opcode) -> bool {
    use Opcode::*;
    matches!(
        op,
        LOADNIL
            | LOADB
            | LOADN
            | LOADK
            | MOVE
            | GETGLOBAL
            | SETGLOBAL
            | GETUPVAL
            | SETUPVAL
            | CLOSEUPVALS
            | GETIMPORT
            | GETTABLE
            | SETTABLE
            | GETTABLEKS
            | SETTABLEKS
            | GETTABLEN
            | SETTABLEN
            | NEWCLOSURE
            | NAMECALL
            | CALL
            | RETURN
            | JUMPIF
            | JUMPIFNOT
            | JUMPIFEQ
            | JUMPIFLE
            | JUMPIFLT
            | JUMPIFNOTEQ
            | JUMPIFNOTLE
            | JUMPIFNOTLT
            | ADD
            | SUB
            | MUL
            | DIV
            | MOD
            | POW
            | ADDK
            | SUBK
            | MULK
            | DIVK
            | MODK
            | POWK
            | AND
            | OR
            | ANDK
            | ORK
            | CONCAT
            | NOT
            | MINUS
            | LENGTH
            | NEWTABLE
            | DUPTABLE
            | SETLIST
            | FORNPREP
            | FORNLOOP
            | FORGLOOP
            | FORGPREP_INEXT
            | FORGPREP_NEXT
            | FORGPREP
            | GETVARARGS
            | DUPCLOSURE
            | LOADKX
            | SUBRK
            | DIVRK
            | JUMPXEQKNIL
            | JUMPXEQKB
            | JUMPXEQKN
            | JUMPXEQKS
            | IDIV
            | IDIVK
            | GETUDATAKS
            | SETUDATAKS
            | NAMECALLUDATA
            | NEWCLASSMEMBER
            | CMPPROTO
    )
}

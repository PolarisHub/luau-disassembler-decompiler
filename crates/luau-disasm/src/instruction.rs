//! Render a single instruction to the exact text `BytecodeBuilder::dumpInstruction`
//! produces, and compute the jump-target labels for a proto the same way
//! `dumpCurrentFunction` does. Matching this format lets us diff our listing directly
//! against `luau-compile --text`.

use luau_bytecode::opcode::*;
use luau_bytecode::{capture_type, Module, Proto};

use crate::constant::render_constant_at;

/// One label id per PC (`Some(id)` when that PC is a jump target), assigned as sequential
/// integers in PC order — identical to Luau's labelling.
pub fn compute_labels(proto: &Proto) -> Vec<Option<u32>> {
    let code = &proto.code;
    let n = code.len();
    let mut is_target = vec![false; n];

    let mut pc = 0;
    while pc < n {
        let insn = code[pc];
        let len = match Opcode::from_u8(insn_op(insn)) {
            Some(op) => {
                if let Some(t) = jump_target(insn, pc) {
                    if t < n {
                        is_target[t] = true;
                    }
                }
                op.length()
            }
            None => 1,
        };
        pc += len.max(1);
    }

    let mut labels = vec![None; n];
    let mut next = 0u32;
    for (i, target) in is_target.iter().enumerate() {
        if *target {
            labels[i] = Some(next);
            next += 1;
        }
    }
    labels
}

fn label_str(labels: &[Option<u32>], target: Option<usize>) -> String {
    match target.and_then(|t| labels.get(t).copied().flatten()) {
        Some(id) => format!("L{id}"),
        None => "L?".to_string(),
    }
}

/// Render the instruction at `pc` (no trailing newline), matching `dumpInstruction`.
pub fn format_instruction(
    module: &Module,
    proto: &Proto,
    pc: usize,
    labels: &[Option<u32>],
) -> String {
    let code = &proto.code;
    let insn = code[pc];
    let aux = code.get(pc + 1).copied().unwrap_or(0);
    let a = insn_a(insn);
    let b = insn_b(insn);
    let c = insn_c(insn);
    let d = insn_d(insn);

    let op = match Opcode::from_u8(insn_op(insn)) {
        Some(op) => op,
        None => return format!("DATA 0x{insn:08X}"),
    };

    let k = |idx: usize| render_constant_at(module, proto, idx);
    let target = label_str(labels, jump_target(insn, pc));

    use Opcode::*;
    match op {
        NOP => "NOP".to_string(),
        BREAK => "BREAK".to_string(),
        LOADNIL => format!("LOADNIL R{a}"),
        LOADB => {
            if c != 0 {
                format!("LOADB R{a} {b} +{c}")
            } else {
                format!("LOADB R{a} {b}")
            }
        }
        LOADN => format!("LOADN R{a} {d}"),
        LOADK => format!("LOADK R{a} K{d} [{}]", k(d as usize)),
        MOVE => format!("MOVE R{a} R{b}"),
        GETGLOBAL => format!("GETGLOBAL R{a} K{aux} [{}]", k(aux as usize)),
        SETGLOBAL => format!("SETGLOBAL R{a} K{aux} [{}]", k(aux as usize)),
        GETUPVAL => format!("GETUPVAL R{a} {b}"),
        SETUPVAL => format!("SETUPVAL R{a} {b}"),
        CLOSEUPVALS => format!("CLOSEUPVALS R{a}"),
        GETIMPORT => format!("GETIMPORT R{a} {d} [{}]", k(d as usize)),
        GETTABLE => format!("GETTABLE R{a} R{b} R{c}"),
        SETTABLE => format!("SETTABLE R{a} R{b} R{c}"),
        GETTABLEKS => format!("GETTABLEKS R{a} R{b} K{aux} [{}]", k(aux as usize)),
        SETTABLEKS => format!("SETTABLEKS R{a} R{b} K{aux} [{}]", k(aux as usize)),
        GETTABLEN => format!("GETTABLEN R{a} R{b} {}", c as u32 + 1),
        SETTABLEN => format!("SETTABLEN R{a} R{b} {}", c as u32 + 1),
        NEWCLOSURE => format!("NEWCLOSURE R{a} P{d}"),
        NAMECALL => format!("NAMECALL R{a} R{b} K{aux} [{}]", k(aux as usize)),
        CALL => format!("CALL R{a} {} {}", b as i32 - 1, c as i32 - 1),
        CALLFB => format!("CALLFB R{a} {} {} [{aux}]", b as i32 - 1, c as i32 - 1),
        RETURN => format!("RETURN R{a} {}", b as i32 - 1),
        JUMP => format!("JUMP {target}"),
        JUMPBACK => format!("JUMPBACK {target}"),
        JUMPIF => format!("JUMPIF R{a} {target}"),
        JUMPIFNOT => format!("JUMPIFNOT R{a} {target}"),
        JUMPIFEQ => format!("JUMPIFEQ R{a} R{aux} {target}"),
        JUMPIFLE => format!("JUMPIFLE R{a} R{aux} {target}"),
        JUMPIFLT => format!("JUMPIFLT R{a} R{aux} {target}"),
        JUMPIFNOTEQ => format!("JUMPIFNOTEQ R{a} R{aux} {target}"),
        JUMPIFNOTLE => format!("JUMPIFNOTLE R{a} R{aux} {target}"),
        JUMPIFNOTLT => format!("JUMPIFNOTLT R{a} R{aux} {target}"),
        ADD => format!("ADD R{a} R{b} R{c}"),
        SUB => format!("SUB R{a} R{b} R{c}"),
        MUL => format!("MUL R{a} R{b} R{c}"),
        DIV => format!("DIV R{a} R{b} R{c}"),
        MOD => format!("MOD R{a} R{b} R{c}"),
        POW => format!("POW R{a} R{b} R{c}"),
        IDIV => format!("IDIV R{a} R{b} R{c}"),
        ADDK => format!("ADDK R{a} R{b} K{c} [{}]", k(c as usize)),
        SUBK => format!("SUBK R{a} R{b} K{c} [{}]", k(c as usize)),
        MULK => format!("MULK R{a} R{b} K{c} [{}]", k(c as usize)),
        DIVK => format!("DIVK R{a} R{b} K{c} [{}]", k(c as usize)),
        MODK => format!("MODK R{a} R{b} K{c} [{}]", k(c as usize)),
        POWK => format!("POWK R{a} R{b} K{c} [{}]", k(c as usize)),
        IDIVK => format!("IDIVK R{a} R{b} K{c} [{}]", k(c as usize)),
        SUBRK => format!("SUBRK R{a} K{b} [{}] R{c}", k(b as usize)),
        DIVRK => format!("DIVRK R{a} K{b} [{}] R{c}", k(b as usize)),
        AND => format!("AND R{a} R{b} R{c}"),
        OR => format!("OR R{a} R{b} R{c}"),
        ANDK => format!("ANDK R{a} R{b} K{c} [{}]", k(c as usize)),
        ORK => format!("ORK R{a} R{b} K{c} [{}]", k(c as usize)),
        CONCAT => format!("CONCAT R{a} R{b} R{c}"),
        NOT => format!("NOT R{a} R{b}"),
        MINUS => format!("MINUS R{a} R{b}"),
        LENGTH => format!("LENGTH R{a} R{b}"),
        NEWTABLE => {
            let hash_size = if b == 0 { 0 } else { 1u32 << (b - 1) };
            format!("NEWTABLE R{a} {hash_size} {aux}")
        }
        DUPTABLE => format!("DUPTABLE R{a} {d}"),
        SETLIST => format!("SETLIST R{a} R{b} {} [{aux}]", c as i32 - 1),
        FORNPREP => format!("FORNPREP R{a} {target}"),
        FORNLOOP => format!("FORNLOOP R{a} {target}"),
        FORGPREP => format!("FORGPREP R{a} {target}"),
        FORGLOOP => {
            let count = aux as u8;
            let inext = if (aux as i32) < 0 { " [inext]" } else { "" };
            format!("FORGLOOP R{a} {target} {count}{inext}")
        }
        FORGPREP_INEXT => format!("FORGPREP_INEXT R{a} {target}"),
        FORGPREP_NEXT => format!("FORGPREP_NEXT R{a} {target}"),
        GETVARARGS => format!("GETVARARGS R{a} {}", b as i32 - 1),
        DUPCLOSURE => format!("DUPCLOSURE R{a} K{d} [{}]", k(d as usize)),
        LOADKX => format!("LOADKX R{a} K{aux} [{}]", k(aux as usize)),
        JUMPX => format!("JUMPX {target}"),
        FASTCALL => format!("FASTCALL {a} {target}"),
        FASTCALL1 => format!("FASTCALL1 {a} R{b} {target}"),
        FASTCALL2 => format!("FASTCALL2 {a} R{b} R{aux} {target}"),
        FASTCALL2K => format!("FASTCALL2K {a} R{b} K{aux} {target} [{}]", k(aux as usize)),
        FASTCALL3 => format!(
            "FASTCALL3 {a} R{b} R{} R{} {target}",
            aux_a(aux),
            aux_b(aux)
        ),
        COVERAGE => "COVERAGE".to_string(),
        CAPTURE => {
            let kind = match a {
                capture_type::VAL => "VAL",
                capture_type::REF => "REF",
                capture_type::UPVAL => "UPVAL",
                _ => "",
            };
            let prefix = if a == capture_type::UPVAL { 'U' } else { 'R' };
            format!("CAPTURE {kind} {prefix}{b}")
        }
        JUMPXEQKNIL => {
            let not = if aux_not(aux) { " NOT" } else { "" };
            format!("JUMPXEQKNIL R{a} {target}{not}")
        }
        JUMPXEQKB => {
            let not = if aux_not(aux) { " NOT" } else { "" };
            format!("JUMPXEQKB R{a} {} {target}{not}", aux & 1)
        }
        JUMPXEQKN => {
            let not = if aux_not(aux) { " NOT" } else { "" };
            let kv = aux_kv(aux);
            format!("JUMPXEQKN R{a} K{kv} {target}{not} [{}]", k(kv as usize))
        }
        JUMPXEQKS => {
            let not = if aux_not(aux) { " NOT" } else { "" };
            let kv = aux_kv(aux);
            format!("JUMPXEQKS R{a} K{kv} {target}{not} [{}]", k(kv as usize))
        }
        GETUDATAKS => {
            let kv = aux_kv16(aux);
            format!("GETUDATAKS R{a} R{b} K{kv} [{}]", k(kv as usize))
        }
        SETUDATAKS => {
            let kv = aux_kv16(aux);
            format!("SETUDATAKS R{a} R{b} K{kv} [{}]", k(kv as usize))
        }
        NAMECALLUDATA => {
            let kv = aux_kv16(aux);
            format!("NAMECALLUDATA R{a} R{b} K{kv} [{}]", k(kv as usize))
        }
        NEWCLASSMEMBER => format!("NEWCLASSMEMBER R{a} R{c} [{}]", k(aux as usize)),
        CMPPROTO => format!("CMPPROTO R{a} #{aux} {target}"),
        // Pseudo-instructions the compiler never emits in serialized code; render plainly.
        NATIVECALL => "NATIVECALL".to_string(),
        PREPVARARGS => format!("PREPVARARGS {a}"),
    }
}

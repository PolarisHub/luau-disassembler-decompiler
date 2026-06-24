//! `luau-disasm`: turn a parsed [`Module`] into a resolved, human-readable instruction
//! listing per proto.
//!
//! Operands are fully resolved: constants are inlined, imports become dotted paths,
//! NAMECALL shows the method name, jump offsets become `Lk` labels, and (when present)
//! debug line numbers are attached. Every instruction is numbered by PC.
//!
//! The per-instruction text matches `BytecodeBuilder::dumpInstruction` exactly, so
//! [`Disassembly::luau_text`] can be diffed against `luau-compile --text` as an oracle.

mod constant;
mod format;
mod instruction;

pub use constant::{render_constant, render_constant_at};
pub use instruction::{compute_labels, format_instruction};

use std::fmt;

use luau_bytecode::opcode::{insn_op, Opcode};
use luau_bytecode::{Module, Proto};

/// A disassembled module: one [`ProtoDisasm`] per proto, in serialized order (which is the
/// same order `luau-compile --text` prints as `Function 0`, `Function 1`, ...).
#[derive(Debug, Clone)]
pub struct Disassembly {
    pub protos: Vec<ProtoDisasm>,
}

#[derive(Debug, Clone)]
pub struct ProtoDisasm {
    pub index: usize,
    pub name: Option<String>,
    pub num_params: u8,
    pub num_upvalues: u8,
    pub is_vararg: bool,
    pub max_stack_size: u8,
    pub line_defined: u32,
    pub lines: Vec<InsnLine>,
}

#[derive(Debug, Clone)]
pub struct InsnLine {
    pub pc: usize,
    pub label: Option<u32>,
    /// Rendered instruction text (matches `dumpInstruction`).
    pub text: String,
    /// Source line, when line info is present.
    pub line_no: Option<i32>,
    /// PREPVARARGS is a real instruction but Luau's dump omits it; we keep it but flag it
    /// so the oracle comparison can skip it too.
    pub is_prepvarargs: bool,
}

/// Disassemble every proto in the module.
pub fn disassemble(module: &Module) -> Disassembly {
    let protos = module
        .protos
        .iter()
        .enumerate()
        .map(|(i, proto)| disassemble_proto(module, proto, i))
        .collect();
    Disassembly { protos }
}

fn disassemble_proto(module: &Module, proto: &Proto, index: usize) -> ProtoDisasm {
    let labels = compute_labels(proto);
    let mut lines = Vec::new();

    let mut pc = 0;
    while pc < proto.code.len() {
        let op = Opcode::from_u8(insn_op(proto.code[pc]));
        let len = op.map(|o| o.length()).unwrap_or(1).max(1);
        let text = format_instruction(module, proto, pc, &labels);
        let line_no = proto.line_info.as_ref().and_then(|li| li.line_for_pc(pc));

        lines.push(InsnLine {
            pc,
            label: labels.get(pc).copied().flatten(),
            text,
            line_no,
            is_prepvarargs: op == Some(Opcode::PREPVARARGS),
        });

        pc += len;
    }

    ProtoDisasm {
        index,
        name: module.resolve(proto.debug_name).map(|c| c.into_owned()),
        num_params: proto.num_params,
        num_upvalues: proto.num_upvalues,
        is_vararg: proto.is_vararg,
        max_stack_size: proto.max_stack_size,
        line_defined: proto.line_defined,
        lines,
    }
}

impl Disassembly {
    /// Render just the instruction lines, label-prefixed, in Luau's `dumpInstruction`
    /// format and ordering (PREPVARARGS omitted). This is what we diff against the
    /// instruction lines extracted from `luau-compile --text`.
    pub fn luau_text(&self) -> String {
        let mut out = String::new();
        for proto in &self.protos {
            for line in &proto.lines {
                if line.is_prepvarargs {
                    continue;
                }
                if let Some(id) = line.label {
                    out.push_str(&format!("L{id}: "));
                }
                out.push_str(&line.text);
                out.push('\n');
            }
        }
        out
    }
}

/// Human-readable listing: a header per proto plus numbered, labelled instructions with
/// source line annotations. This is the snapshot deliverable.
impl fmt::Display for Disassembly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for proto in &self.protos {
            let name = proto.name.as_deref().unwrap_or("??");
            writeln!(f, "Function {} ({}):", proto.index, name)?;
            writeln!(
                f,
                "; params={} upvals={} vararg={} stack={} line={}",
                proto.num_params,
                proto.num_upvalues,
                proto.is_vararg,
                proto.max_stack_size,
                proto.line_defined
            )?;
            for line in &proto.lines {
                let label = match line.label {
                    Some(id) => format!("L{id}:"),
                    None => String::new(),
                };
                let line_anno = match line.line_no {
                    Some(n) => format!("  ; line {n}"),
                    None => String::new(),
                };
                writeln!(
                    f,
                    "{:>5}  {:<5}{}{}",
                    line.pc, label, line.text, line_anno
                )?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

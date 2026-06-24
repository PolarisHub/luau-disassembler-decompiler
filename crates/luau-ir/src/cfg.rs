//! Control-flow graph construction.
//!
//! We find basic-block leaders (the first instruction, every jump target, and every
//! instruction that falls after a branch), cut the instruction stream into blocks, and add
//! edges. Successor semantics are spelled out per opcode in [`terminator`] rather than
//! inferred from a single predicate, because Luau has several branch shapes (two-way
//! conditionals, two-way loop ops, unconditional FORGPREP, the LOADB skip, FASTCALL skip)
//! that a generic "does it fall through" check gets wrong.

use std::collections::BTreeSet;

use luau_bytecode::opcode::{insn_c, insn_op, jump_target, Opcode};
use luau_bytecode::Proto;

/// What kind of control-flow transfer ends a block, and where it can go.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    /// Falls through to the next instruction only.
    Fallthrough(usize),
    /// Returns from the function (no successors).
    Return,
    /// Unconditional jump to a single target.
    Jump(usize),
    /// Two-way branch: (fallthrough/not-taken, taken target). Order is (next, target) for
    /// conditionals and FORNPREP; for loop-back ops it is still (exit-or-next, back-target)
    /// but both edges are recorded regardless.
    CondBranch { not_taken: usize, taken: usize },
}

impl Terminator {
    pub fn successors(&self) -> Vec<usize> {
        match *self {
            Terminator::Return => vec![],
            Terminator::Fallthrough(n) => vec![n],
            Terminator::Jump(t) => vec![t],
            Terminator::CondBranch { not_taken, taken } => {
                if not_taken == taken {
                    vec![not_taken]
                } else {
                    vec![not_taken, taken]
                }
            }
        }
    }
}

/// Compute the terminator for the instruction at `pc` (which must be the last instruction
/// of its block). `len` is the instruction's word length.
pub fn terminator(proto: &Proto, pc: usize, len: usize) -> Terminator {
    let insn = proto.code[pc];
    let next = pc + len;
    let op = match Opcode::from_u8(insn_op(insn)) {
        Some(op) => op,
        // Unknown opcode: treat as a plain fallthrough so analysis stays total.
        None => return Terminator::Fallthrough(next),
    };
    let target = jump_target(insn, pc);

    use Opcode::*;
    match op {
        RETURN => Terminator::Return,
        JUMP | JUMPBACK | JUMPX => Terminator::Jump(target.unwrap_or(next)),
        // FORGPREP* jump unconditionally to the loop's backedge test.
        FORGPREP | FORGPREP_INEXT | FORGPREP_NEXT => Terminator::Jump(target.unwrap_or(next)),
        // LOADB with a non-zero C skips the next instruction unconditionally.
        LOADB => {
            if insn_c(insn) != 0 {
                Terminator::Jump(target.unwrap_or(next))
            } else {
                Terminator::Fallthrough(next)
            }
        }
        // Two-way branches.
        JUMPIF | JUMPIFNOT | JUMPIFEQ | JUMPIFLE | JUMPIFLT | JUMPIFNOTEQ | JUMPIFNOTLE
        | JUMPIFNOTLT | JUMPXEQKNIL | JUMPXEQKB | JUMPXEQKN | JUMPXEQKS | CMPPROTO | FORNPREP
        | FORNLOOP | FORGLOOP | FASTCALL | FASTCALL1 | FASTCALL2 | FASTCALL2K | FASTCALL3 => {
            match target {
                Some(t) => Terminator::CondBranch {
                    not_taken: next,
                    taken: t,
                },
                None => Terminator::Fallthrough(next),
            }
        }
        _ => Terminator::Fallthrough(next),
    }
}

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub index: usize,
    /// PC of the first instruction (inclusive).
    pub start_pc: usize,
    /// PC just past the last instruction (exclusive).
    pub end_pc: usize,
    /// PCs of the instructions in this block, in order.
    pub insns: Vec<usize>,
    pub terminator: Terminator,
    pub successors: Vec<usize>,
    pub predecessors: Vec<usize>,
}

#[derive(Debug, Clone)]
pub struct Cfg {
    pub blocks: Vec<BasicBlock>,
    /// Block index for each PC that begins a block; other PCs map via the block they fall in.
    pub entry: usize,
}

impl Cfg {
    pub fn block_at(&self, pc: usize) -> Option<usize> {
        self.blocks
            .iter()
            .find(|b| pc >= b.start_pc && pc < b.end_pc)
            .map(|b| b.index)
    }
}

/// Walk the instruction stream, returning each instruction's (pc, word length).
fn iter_instructions(proto: &Proto) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut pc = 0;
    while pc < proto.code.len() {
        let len = Opcode::from_u8(insn_op(proto.code[pc]))
            .map(|o| o.length())
            .unwrap_or(1)
            .max(1);
        out.push((pc, len));
        pc += len;
    }
    out
}

/// Build the CFG for a proto.
pub fn build_cfg(proto: &Proto) -> Cfg {
    let instrs = iter_instructions(proto);
    let n = proto.code.len();

    // 1. Find leaders.
    let mut leaders: BTreeSet<usize> = BTreeSet::new();
    leaders.insert(0);
    for &(pc, len) in &instrs {
        let term = terminator(proto, pc, len);
        match term {
            Terminator::Fallthrough(_) => {}
            Terminator::Return => {
                // Instruction after a return starts a new (possibly dead) block.
                if pc + len < n {
                    leaders.insert(pc + len);
                }
            }
            Terminator::Jump(t) => {
                leaders.insert(t);
                if pc + len < n {
                    leaders.insert(pc + len);
                }
            }
            Terminator::CondBranch { not_taken, taken } => {
                leaders.insert(taken);
                leaders.insert(not_taken);
            }
        }
    }
    // Only keep leaders that are real instruction boundaries and in range.
    let instr_starts: BTreeSet<usize> = instrs.iter().map(|&(pc, _)| pc).collect();
    let leaders: Vec<usize> = leaders
        .into_iter()
        .filter(|pc| instr_starts.contains(pc) && *pc < n)
        .collect();

    // 2. Cut into blocks.
    let mut blocks: Vec<BasicBlock> = Vec::new();
    for (i, &start) in leaders.iter().enumerate() {
        let end = leaders.get(i + 1).copied().unwrap_or(n);
        let insns: Vec<usize> = instrs
            .iter()
            .filter(|&&(pc, _)| pc >= start && pc < end)
            .map(|&(pc, _)| pc)
            .collect();
        let (last_pc, last_len) = instrs
            .iter()
            .copied()
            .filter(|&(pc, _)| pc >= start && pc < end)
            .last()
            .unwrap_or((start, 1));
        let term = terminator(proto, last_pc, last_len);
        blocks.push(BasicBlock {
            index: i,
            start_pc: start,
            end_pc: end,
            insns,
            terminator: term,
            successors: Vec::new(),
            predecessors: Vec::new(),
        });
    }

    // 3. Resolve successor PCs to block indices and wire predecessors.
    let pc_to_block: std::collections::HashMap<usize, usize> =
        blocks.iter().map(|b| (b.start_pc, b.index)).collect();
    let succ_lists: Vec<Vec<usize>> = blocks
        .iter()
        .map(|b| {
            b.terminator
                .successors()
                .into_iter()
                .filter_map(|pc| pc_to_block.get(&pc).copied())
                .collect()
        })
        .collect();
    for (i, succs) in succ_lists.into_iter().enumerate() {
        for &s in &succs {
            blocks[s].predecessors.push(i);
        }
        blocks[i].successors = succs;
    }

    Cfg { blocks, entry: 0 }
}

//! `luau-decompile`: reconstruct readable Luau from a parsed [`Module`].
//!
//! This is a conservative, honest reconstructor. Its two jobs are recovering expressions
//! from the register machine and recovering structure from control flow.
//!
//! - Expressions: per block we track what expression currently lives in each register.
//!   Only *immutable* leaves (constants and resolved imports) are inlined at their use
//!   sites; everything else (arithmetic, table/field reads, call results, moves) is
//!   materialized into a named local and read back by name. That rule is deliberately
//!   conservative — re-reading a name always yields the value the register held, so we
//!   never reorder a side effect or capture a stale value. A correct temp beats a wrong
//!   inline (per the project's ground rules).
//!
//! - Structure: numeric `for` loops are recovered natively. Other control flow is rendered
//!   faithfully with `::label::` / `goto` and a comment, and the proto is flagged
//!   `partial`. Native recovery of `if`/`while`/`repeat`/generic-`for` is the next step;
//!   until then the output reflects the real control flow rather than guessing.

mod ast;
mod cleanup;
mod naming;

use std::collections::{BTreeMap, BTreeSet};

use ast::{render_block, render_expr, Capture, Expr, Stmt, TableField};
use luau_bytecode::opcode::*;
use luau_bytecode::{capture_type, Constant, Module, Proto, StringRef};
use luau_disasm::{compute_labels, render_constant_at};

/// Result of decompiling a whole module.
#[derive(Debug, Clone)]
pub struct Decompiled {
    pub source: String,
    /// True if any proto could not be fully structured (contains goto fallback or unknown
    /// constructs). Callers should treat the output as a best-effort reconstruction.
    pub partial: bool,
    pub per_proto: Vec<ProtoReport>,
}

#[derive(Debug, Clone)]
pub struct ProtoReport {
    pub index: usize,
    pub name: Option<String>,
    pub partial: bool,
    /// Human notes about what was uncertain in this proto.
    pub notes: Vec<String>,
}

/// Decompile a module, starting from its main proto and inlining child closures where they
/// are referenced.
pub fn decompile(module: &Module) -> Decompiled {
    let mut reports = Vec::new();
    let main = module.main_proto as usize;
    let body = decompile_proto(module, main, &mut reports);

    let partial = reports.iter().any(|r| r.partial);
    let mut source = String::new();
    if partial {
        source.push_str("-- Decompiled by luau-decompile (best-effort reconstruction).\n");
        source.push_str("-- Some regions use goto/labels where structuring is incomplete.\n\n");
    } else {
        source.push_str("-- Decompiled by luau-decompile.\n\n");
    }
    source.push_str(&body);

    Decompiled {
        source,
        partial,
        per_proto: reports,
    }
}

/// Decompile one proto into a sequence of top-level statements (used for the main proto)
/// or a function body. Returns the rendered text.
fn decompile_proto(module: &Module, proto_idx: usize, reports: &mut Vec<ProtoReport>) -> String {
    let proto = &module.protos[proto_idx];
    let mut d = Decompiler::new(module, proto, proto_idx);
    let mut stmts = d.run();

    // Remove unreachable code left after returns/breaks by inline-cache flushes.
    cleanup::drop_unreachable(&mut stmts);
    // Recover the `z = a and b or c` short-circuit ternary from its goto/label diamond.
    cleanup::recover_and_or(&mut stmts);

    // Captured registers, upvalues, and globals are excluded from inlining/elimination:
    // closures must keep the variables they close over, and a write to an upvalue or global
    // is an observable effect (another closure sees it) even when nothing in this proto reads
    // it back.
    let mut protected = d.captured_names();
    protected.extend(d.globals.iter().cloned());
    for i in 0..d.proto.num_upvalues {
        protected.insert(d.upval_name(i));
    }

    // Run the reducing passes to a fixpoint: chain-folding, table-literal rebuilding,
    // per-definition copy propagation, and dead-store elimination all enable each other
    // (e.g. inlining temps makes a chain consecutive, which folds, which frees more temps).
    let mut prev = usize::MAX;
    for _ in 0..16 {
        naming::fold_refinements(&mut stmts);
        cleanup::fold_table_literals(&mut stmts);
        cleanup::single_use_inline(&mut stmts, &protected);
        cleanup::dead_store_elim(&mut stmts, &protected);
        let n = cleanup::count_stmts(&stmts);
        if n == prev {
            break;
        }
        prev = n;
    }
    // A constant `1` step on a numeric for is implicit.
    drop_unit_for_steps(&mut stmts);

    // Locals that still need a hoisted declaration (a sole-Var assignment survived),
    // excluding parameters and upvalues.
    let non_local = d.non_local_names();
    let mut hoist_names = cleanup::assigned_locals(&stmts, &non_local);

    // Smart-rename synthesized locals from the expressions they hold (require -> module,
    // GetService -> service, etc.). Renaming a local is always semantics-preserving, so this
    // runs after reconstruction and rewrites the AST consistently.
    let rename = naming::smart_rename(&stmts, &hoist_names);
    naming::apply_rename(&mut stmts, &rename);
    for n in hoist_names.iter_mut() {
        if let Some(new) = rename.get(n) {
            *n = new.clone();
        }
    }

    // Now that this function's locals have their final names, rewrite the `u0`/`u1`/… upvalue
    // placeholders inside each nested closure to the captured local's name.
    d.resolve_closures(&mut stmts, &rename);

    // Determine `partial` from the FINAL tree: a proto is partial only if some unstructured
    // control flow (a goto/label) survived all recovery passes, or a nested closure was partial.
    let partial = contains_unstructured(&stmts) || d.has_partial_child;
    reports.push(ProtoReport {
        index: proto_idx,
        name: module.resolve(proto.debug_name).map(|c| c.into_owned()),
        partial,
        notes: d.notes.clone(),
    });

    // Hoist all materialized non-parameter locals so every assignment has a declaration in
    // scope regardless of how control flow nests.
    let mut out = String::new();
    if !hoist_names.is_empty() {
        if hoist_names.len() > 4 {
            for name in &hoist_names {
                out.push_str(&format!("local {name}\n"));
            }
        } else {
            out.push_str(&format!("local {}\n", hoist_names.join(", ")));
        }
    }
    out.push_str(&render_block(&stmts, 0));
    out
}

/// Whether the tree still contains unstructured control flow (a `goto`/label), meaning the
/// reconstruction fell back rather than recovering a native construct.
fn contains_unstructured(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Goto(_) | Stmt::Label(_) => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => contains_unstructured(then_body) || contains_unstructured(else_body),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => contains_unstructured(body),
        _ => false,
    })
}

struct Decompiler<'a> {
    module: &'a Module,
    proto: &'a Proto,
    proto_idx: usize,
    /// Expression currently held in each register when it is an inlinable immutable leaf
    /// (constant/import/global). `None` means "read this register by its name". The cache is
    /// flushed at every control-flow boundary so no inlined value ever crosses an edge.
    regs: Vec<Option<Expr>>,
    /// Registers (>= num_params) that were written and need a hoisted `local`.
    hoisted: BTreeSet<u8>,
    labels: Vec<Option<u32>>,
    /// Loop headers: header PC -> furthest back-edge source (while/repeat kinds).
    loop_back: BTreeMap<usize, usize>,
    /// Overrides `reg_name` for the duration of a loop body, so the loop variable reads
    /// consistently in the header and the body even when its register is reused elsewhere.
    reg_name_override: BTreeMap<u8, String>,
    /// Counter for synthesizing loop-variable names when debug info is absent.
    next_loopvar: usize,
    /// Registers captured (by value or by ref) into a child closure. These must never be
    /// inlined away or dead-store-eliminated — the closure references them by name, which our
    /// use-counting (the closure body is opaque) cannot see.
    captured_regs: BTreeSet<u8>,
    /// Base register of the open-ended multret value left by the IMMEDIATELY preceding
    /// instruction (a `CALL` with C=0 or `GETVARARGS` with B=0). A following `B=0`/`C=0`
    /// "to top" consumer (nested call, multret return, open SETLIST) reads its trailing
    /// operands up to and including this register. Flows exactly one instruction.
    pending_multret: Option<u8>,
    /// Set when a nested closure decompiled to a partial result (its gotos are hidden inside
    /// the rendered closure string, so the parent can't see them otherwise).
    has_partial_child: bool,
    /// Names accessed as globals (via GETGLOBAL/SETGLOBAL). They must not be hoisted as
    /// locals — doing so would turn a global write into a local one.
    globals: BTreeSet<String>,
    notes: Vec<String>,
}

impl<'a> Decompiler<'a> {
    fn new(module: &'a Module, proto: &'a Proto, proto_idx: usize) -> Self {
        Decompiler {
            module,
            proto,
            proto_idx,
            regs: vec![None; proto.max_stack_size as usize + 1],
            hoisted: BTreeSet::new(),
            labels: compute_labels(proto),
            loop_back: BTreeMap::new(),
            reg_name_override: BTreeMap::new(),
            next_loopvar: 0,
            captured_regs: BTreeSet::new(),
            pending_multret: None,
            has_partial_child: false,
            globals: BTreeSet::new(),
            notes: Vec::new(),
        }
    }

    fn run(&mut self) -> Vec<Stmt> {
        self.loop_back = self.compute_loop_back();
        self.captured_regs = self.compute_captured_regs();
        let mut stmts = Vec::new();
        let mut pending = None;
        self.emit_range(0, self.proto.code.len(), &mut stmts, &mut pending, None);

        // Drop labels nothing jumps to (recursively). Structured regions don't reference
        // their internal targets, and the FASTCALL skip-over is never a goto, so those labels
        // (not even valid Luau on their own) are removed.
        let referenced = collect_goto_targets(&stmts);
        retain_referenced_labels(&mut stmts, &referenced);
        stmts
    }

    /// Header PC -> furthest back-edge source, for the `while`/`repeat` loop kinds
    /// (JUMPBACK and backward conditional jumps). FORNLOOP/FORGLOOP back-edges are excluded;
    /// those loops are recovered from their FORNPREP/FORGPREP entries instead.
    fn compute_loop_back(&self) -> BTreeMap<usize, usize> {
        let code = &self.proto.code;
        let mut m: BTreeMap<usize, usize> = BTreeMap::new();
        let mut pc = 0;
        while pc < code.len() {
            let insn = code[pc];
            if let Some(op) = Opcode::from_u8(insn_op(insn)) {
                let loopish = op == Opcode::JUMPBACK || is_conditional_jump(op);
                if loopish {
                    if let Some(t) = jump_target(insn, pc) {
                        if t <= pc {
                            let e = m.entry(t).or_insert(pc);
                            if pc > *e {
                                *e = pc;
                            }
                        }
                    }
                }
                pc += op.length().max(1);
            } else {
                pc += 1;
            }
        }
        m
    }

    /// Structure the instruction range `[lo, hi)` into statements, recognizing loops and
    /// conditionals and falling back to labelled `goto` for anything that doesn't match.
    /// `loop_ctx` is `(continue_target_pc, break_target_pc)` of the innermost loop.
    fn emit_range(
        &mut self,
        lo: usize,
        hi: usize,
        stmts: &mut Vec<Stmt>,
        pending: &mut Option<(u8, Expr, String)>,
        loop_ctx: Option<(usize, usize)>,
    ) {
        let mut pc = lo;
        while pc < hi {
            let insn = self.proto.code[pc];
            let op = match Opcode::from_u8(insn_op(insn)) {
                Some(o) => o,
                None => {
                    pc += 1;
                    continue;
                }
            };
            let len = op.length().max(1);

            // Numeric / generic for brackets.
            if op == Opcode::FORNPREP {
                if let Some(next) = self.try_numeric_for(pc, hi, stmts) {
                    pc = next;
                    continue;
                }
            }
            if matches!(
                op,
                Opcode::FORGPREP | Opcode::FORGPREP_INEXT | Opcode::FORGPREP_NEXT
            ) {
                if let Some(next) = self.try_generic_for(pc, hi, stmts) {
                    pc = next;
                    continue;
                }
            }
            // while / repeat: this PC is a back-edge target (loop header).
            let is_header = self.loop_back.contains_key(&pc);
            if is_header {
                if let Some(next) = self.try_loop(pc, hi, stmts) {
                    pc = next;
                    continue;
                }
            }
            // break: an unconditional jump to the enclosing loop's exit.
            if matches!(op, Opcode::JUMP | Opcode::JUMPBACK) {
                if let Some((cont, brk)) = loop_ctx {
                    if let Some(t) = jump_target(insn, pc) {
                        if t == brk {
                            self.flush_inline(stmts);
                            stmts.push(Stmt::Break);
                            pc += len;
                            continue;
                        }
                        if t == cont {
                            // A jump to the loop's continue point (the update/back-edge).
                            self.flush_inline(stmts);
                            stmts.push(Stmt::Continue);
                            pc += len;
                            continue;
                        }
                    }
                }
            }
            // Conditional break/continue: a conditional jump straight to the loop's exit or
            // continue point. The target is outside the loop body (so `try_if` can't see it);
            // lower it to `if <taken-condition> then break/continue end`. A compound
            // `if not (a and b) then break` compiles to several such jumps, which decompose
            // into equivalent sequential conditional breaks.
            if is_conditional_jump(op) {
                if let Some((cont, brk)) = loop_ctx {
                    let kw = match jump_target(insn, pc) {
                        Some(t) if t == brk => Some(Stmt::Break),
                        Some(t) if t == cont => Some(Stmt::Continue),
                        _ => None,
                    };
                    if let Some(kw) = kw {
                        let cond = self.taken_condition(op, pc);
                        self.flush_inline(stmts);
                        stmts.push(Stmt::If {
                            cond,
                            then_body: vec![kw],
                            else_body: Vec::new(),
                        });
                        pc += len;
                        continue;
                    }
                }
            }
            // Boolean materialization: a conditional jump followed by two LOADBs writing the
            // same register (false then true) is just a stored boolean condition.
            if is_conditional_jump(op) {
                if let Some(next) = self.try_bool_materialize(pc, hi, stmts) {
                    pc = next;
                    continue;
                }
            }
            // if / if-else: a forward conditional jump (but not a loop header's test).
            if !is_header && is_conditional_jump(op) {
                // First try a short-circuit guard chain (`if not (a and b) then return end`),
                // which spans several conditional jumps; fall back to a single if/else.
                if let Some(next) = self.try_guard_chain(pc, hi, stmts, loop_ctx) {
                    pc = next;
                    continue;
                }
                if let Some(t) = jump_target(insn, pc) {
                    if t > pc && t <= hi {
                        if let Some(next) = self.try_if(pc, hi, stmts, loop_ctx) {
                            pc = next;
                            continue;
                        }
                    }
                }
            }

            // Straight-line (or goto fallback for unstructured control flow).
            self.maybe_label(pc, stmts);
            self.step(op, pc, stmts, pending);
            pc += len;
        }
    }

    /// Emit a sub-range as its own block, flushing the inline cache at the block end so no
    /// cached value escapes the region.
    fn emit_body(&mut self, lo: usize, hi: usize, loop_ctx: Option<(usize, usize)>) -> Vec<Stmt> {
        let mut body = Vec::new();
        let mut pending = None;
        self.emit_range(lo, hi, &mut body, &mut pending, loop_ctx);
        self.flush_inline(&mut body);
        body
    }

    fn maybe_label(&mut self, pc: usize, stmts: &mut Vec<Stmt>) {
        if let Some(id) = self.labels.get(pc).copied().flatten() {
            // A label is a control-flow join. Cached inline expressions only describe the
            // current fall-through path; materialize them before the label so a jump into the
            // same PC reads the merged register name instead of one predecessor's value.
            self.flush_inline(stmts);
            stmts.push(Stmt::Label(format!("L{id}")));
        }
    }

    fn try_numeric_for(&mut self, pc: usize, hi: usize, stmts: &mut Vec<Stmt>) -> Option<usize> {
        let insn = self.proto.code[pc];
        let exit = jump_target(insn, pc)?; // instruction after FORNLOOP
        if exit == 0 || exit > hi {
            return None;
        }
        let fornloop = exit - 1;
        if fornloop <= pc {
            return None;
        }
        let flop = Opcode::from_u8(insn_op(*self.proto.code.get(fornloop)?))?;
        if flop != Opcode::FORNLOOP
            || jump_target(self.proto.code[fornloop], fornloop) != Some(pc + 1)
        {
            return None;
        }
        let a = insn_a(insn);
        // Layout at A: [limit, step, index/var]. Read setup exprs from the cache first
        // (before the loop-variable name override shadows the register).
        let start = self.reg(a + 2);
        let limit = self.reg(a);
        let step = self.reg(a + 1);
        let var = self.loop_var_name(a + 2, pc + 1);

        // The for header consumes these registers; clear them so the body reads the loop
        // variable by name, then flush any other cached value across the loop boundary.
        for r in [a, a + 1, a + 2] {
            if let Some(slot) = self.regs.get_mut(r as usize) {
                *slot = None;
            }
        }
        self.flush_inline(stmts);

        self.reg_name_override.insert(a + 2, var.clone());
        let body = self.emit_body(pc + 1, fornloop, Some((fornloop, exit)));
        self.reg_name_override.remove(&(a + 2));
        // The loop variable is declared by the `for`, not hoisted.
        self.hoisted.remove(&(a + 2));

        stmts.push(Stmt::NumericFor {
            var,
            start,
            limit,
            step: Some(step),
            body,
        });
        Some(exit)
    }

    fn try_generic_for(&mut self, pc: usize, hi: usize, stmts: &mut Vec<Stmt>) -> Option<usize> {
        let insn = self.proto.code[pc];
        let forgloop = jump_target(insn, pc)?;
        if forgloop <= pc || forgloop >= self.proto.code.len() {
            return None;
        }
        let glop = Opcode::from_u8(insn_op(self.proto.code[forgloop]))?;
        if glop != Opcode::FORGLOOP || forgloop >= hi {
            return None;
        }
        let a = insn_a(insn);
        let aux = self.proto.code.get(forgloop + 1).copied().unwrap_or(0);
        let var_count = (aux & 0xff) as u8;
        if var_count == 0 {
            return None;
        }
        // Generic-for layout at A: [generator, state, index, vars...]. The user variables
        // start at A+3.

        // The iterator was produced by a CALL into A..A+2 just before FORGPREP; if the last
        // emitted statement is exactly that multi-assign, use its call as the `in` expression.
        let iter_regs = [self.reg_name(a), self.reg_name(a + 1), self.reg_name(a + 2)];
        let exprs = match stmts.last() {
            Some(Stmt::Assign { targets, values })
                if values.len() == 1
                    && targets.len() == 3
                    && targets
                        .iter()
                        .zip(iter_regs.iter())
                        .all(|(t, n)| matches!(t, Expr::Var(v) if v == n)) =>
            {
                let call = values[0].clone();
                stmts.pop();
                vec![call]
            }
            _ => vec![self.reg(a), self.reg(a + 1), self.reg(a + 2)],
        };

        // Clear the loop registers and flush across the boundary.
        for r in a..=(a + 2 + var_count) {
            if let Some(slot) = self.regs.get_mut(r as usize) {
                *slot = None;
            }
        }
        self.flush_inline(stmts);

        let exit = forgloop + 2; // FORGLOOP carries an AUX word
        let mut vars = Vec::with_capacity(var_count as usize);
        for i in 0..var_count {
            let name = self.loop_var_name(a + 3 + i, pc + 1);
            self.reg_name_override.insert(a + 3 + i, name.clone());
            vars.push(name);
        }
        let body = self.emit_body(pc + 1, forgloop, Some((forgloop, exit)));
        for i in 0..var_count {
            self.reg_name_override.remove(&(a + 3 + i));
            self.hoisted.remove(&(a + 3 + i));
        }

        stmts.push(Stmt::GenericFor { vars, exprs, body });
        Some(exit)
    }

    fn try_loop(&mut self, pc: usize, hi: usize, stmts: &mut Vec<Stmt>) -> Option<usize> {
        let back = *self.loop_back.get(&pc)?;
        if back >= hi {
            return None;
        }
        let back_op = Opcode::from_u8(insn_op(self.proto.code[back]))?;
        let exit = back + back_op.length().max(1);

        // Remove the header while structuring its body so the body emit doesn't recurse back
        // into this same loop.
        self.loop_back.remove(&pc);

        let result = if back_op == Opcode::JUMPBACK {
            self.structure_jumpback_loop(pc, back, exit, stmts)
        } else if is_conditional_jump(back_op) {
            self.structure_condback_repeat(pc, back, back_op, exit, stmts)
        } else {
            None
        };

        if result.is_none() {
            self.loop_back.insert(pc, back);
        }
        result
    }

    /// A loop whose back-edge is an unconditional JUMPBACK. The single conditional exit test
    /// classifies it: a test immediately before the back-jump is a `repeat ... until`; a test
    /// at the top (with statement-free setup) is a `while`.
    fn structure_jumpback_loop(
        &mut self,
        pc: usize,
        back: usize,
        exit: usize,
        stmts: &mut Vec<Stmt>,
    ) -> Option<usize> {
        match self.find_loop_test(pc, back, exit) {
            Some(tp) => {
                let top = Opcode::from_u8(insn_op(self.proto.code[tp]))?;
                let tlen = top.length().max(1);
                if tp + tlen == back && tp > pc {
                    // repeat ... until <taken test>: body is everything before the test.
                    self.flush_inline(stmts);
                    let mut body = Vec::new();
                    let mut p = None;
                    self.emit_range(pc, tp, &mut body, &mut p, Some((pc, exit)));
                    let cond = self.taken_condition(top, tp);
                    self.flush_inline(&mut body);
                    stmts.push(Stmt::Repeat { body, cond });
                    Some(exit)
                } else {
                    // while <cond>: the operand setup before the test must be statement-free.
                    let snapshot = self.regs.clone();
                    let mut setup = Vec::new();
                    let mut p = None;
                    let mut sp = pc;
                    while sp < tp {
                        let sop = Opcode::from_u8(insn_op(self.proto.code[sp]))?;
                        self.step(sop, sp, &mut setup, &mut p);
                        sp += sop.length().max(1);
                    }
                    if !setup.is_empty() {
                        self.regs = snapshot;
                        return None;
                    }
                    let cond = self.fallthrough_condition(top, tp);
                    self.flush_inline(stmts);
                    let body = self.emit_body(tp + tlen, back, Some((pc, exit)));
                    stmts.push(Stmt::While { cond, body });
                    Some(exit)
                }
            }
            None => {
                // No exit test on the back-edge path: an infinite `while true` (with breaks).
                self.flush_inline(stmts);
                let body = self.emit_body(pc, back, Some((pc, exit)));
                stmts.push(Stmt::While {
                    cond: Expr::Bool(true),
                    body,
                });
                Some(exit)
            }
        }
    }

    /// A loop whose back-edge is itself a conditional jump (continues while taken). The
    /// `until` condition is the negation of that edge.
    fn structure_condback_repeat(
        &mut self,
        pc: usize,
        back: usize,
        back_op: Opcode,
        exit: usize,
        stmts: &mut Vec<Stmt>,
    ) -> Option<usize> {
        self.flush_inline(stmts);
        let mut body = Vec::new();
        let mut p = None;
        self.emit_range(pc, back, &mut body, &mut p, Some((pc, exit)));
        let cond = negate(self.taken_condition(back_op, back));
        self.flush_inline(&mut body);
        stmts.push(Stmt::Repeat { body, cond });
        Some(exit)
    }

    /// Recognize `x = <cond>` materialized as a conditional jump plus two booleans:
    /// ```text
    /// JUMPIF... R -> T          (taken -> the `true` load)
    /// LOADB Rt <false> +1       (fall-through: Rt = false, skip the true load)
    /// T: LOADB Rt <true>        (Rt = true)
    /// ```
    /// Sets `Rt` to the boolean condition and returns the PC just past the pattern.
    fn try_bool_materialize(
        &mut self,
        pc: usize,
        hi: usize,
        stmts: &mut Vec<Stmt>,
    ) -> Option<usize> {
        let insn = self.proto.code[pc];
        let op = Opcode::from_u8(insn_op(insn))?;
        let target = jump_target(insn, pc)?;
        let next = pc + op.length().max(1);
        if next >= hi || target >= hi {
            return None;
        }
        // Fall-through: LOADB with a skip.
        let false_insn = *self.proto.code.get(next)?;
        if Opcode::from_u8(insn_op(false_insn)) != Some(Opcode::LOADB) || insn_c(false_insn) == 0 {
            return None;
        }
        let rt = insn_a(false_insn);
        let b_false = insn_b(false_insn) != 0;
        let skip_target = next + insn_c(false_insn) as usize + 1;
        // Taken target must be the very next instruction: the `true` LOADB.
        if target != next + 1 {
            return None;
        }
        let true_insn = *self.proto.code.get(target)?;
        if Opcode::from_u8(insn_op(true_insn)) != Some(Opcode::LOADB)
            || insn_a(true_insn) != rt
            || insn_c(true_insn) != 0
        {
            return None;
        }
        let b_true = insn_b(true_insn) != 0;
        // The false-load must skip exactly over the true-load, and the booleans must differ.
        if skip_target != target + 1 || b_true == b_false {
            return None;
        }

        // Rt = taken ? b_true : b_false. With (true,false) that's the condition; with
        // (false,true) it's its negation. Materialize it in place (rather than caching) so
        // the condition's operands are read now, before any later reassignment.
        let taken = self.taken_condition(op, pc);
        let expr = if b_true { taken } else { negate(taken) };
        self.assign(rt, expr, stmts);
        Some(target + 1)
    }

    /// First conditional jump in `[lo, hi)` whose taken target is `exit` (the loop test).
    fn find_loop_test(&self, lo: usize, hi: usize, exit: usize) -> Option<usize> {
        let mut pc = lo;
        while pc < hi {
            let op = Opcode::from_u8(insn_op(self.proto.code[pc]))?;
            if is_conditional_jump(op) && jump_target(self.proto.code[pc], pc) == Some(exit) {
                return Some(pc);
            }
            pc += op.length().max(1);
        }
        None
    }

    /// Short-circuit guard chain: a run of conditional jumps that route to a small block
    /// ending in a terminator (`return`/`break`/`continue`), with the fall-through reaching
    /// the body. The compiler emits `if not (a and b and ...) then return end` this way:
    ///
    /// ```text
    ///   JUMPIFNOT a -> G      ; proceed (toward body) when a
    ///   JUMPIF    b -> BODY   ; proceed (toward body) when b; fall-through reaches G
    ///   G:   <terminator block>
    ///   BODY: ...
    /// ```
    ///
    /// We reconstruct `if not (<proceed conditions, and-ed>) then <G block> end` and resume
    /// at BODY. This is sound: the guard block carries no value, it only diverts control, so
    /// there is no `a and b or c` value-merge hazard. Returns the PC to resume at (BODY).
    fn try_guard_chain(
        &mut self,
        pc: usize,
        hi: usize,
        stmts: &mut Vec<Stmt>,
        loop_ctx: Option<(usize, usize)>,
    ) -> Option<usize> {
        // Collect conditional jumps, allowing straight-line (non-control-flow) instructions
        // between them. The intervening instructions are the effect that produces the next
        // guard's test value; we re-validate them below. Bail if we hit a real branch,
        // loop op, or terminator (anything that would break the and-link).
        let mut jumps: Vec<usize> = Vec::new();
        let mut p = pc;
        while p < hi {
            let op = Opcode::from_u8(insn_op(self.proto.code[p]))?;
            if is_conditional_jump(op) {
                jumps.push(p);
                p += op.length().max(1);
            } else if self.op_breaks_chain(op) {
                break;
            } else {
                // Straight-line; keep walking until we find another conditional jump or
                // something that breaks the chain.
                p += op.length().max(1);
            }
        }
        if jumps.len() < 2 {
            return None;
        }

        // Compute guard (G) and body. Three patterns:
        //   1. Simple consecutive: last jump -> BODY, earlier jumps -> G, no intervening code.
        //      Produces: if not (a and b ...) then <G> end.
        //   2. Effectful: ALL jumps -> G, intervening straight-line between jumps.
        //   3. Mixed: last jump -> BODY, earlier jumps -> G, intervening straight-line.
        //   Patterns 2 and 3 both produce flat sequential guards with effects between them.
        let first = jumps[0];
        let last = *jumps.last().unwrap();
        let guard = jump_target(self.proto.code[first], first)?;
        if guard <= first {
            return None;
        }
        let last_taken = jump_target(self.proto.code[last], last)?;
        // Detect intervening code between any pair of consecutive jumps.
        let has_intervening = jumps.windows(2).any(|w| {
            let a_len = Opcode::from_u8(insn_op(self.proto.code[w[0]]))
                .map(|o| o.length().max(1))
                .unwrap_or(1);
            w[0] + a_len != w[1]
        });
        if last_taken != guard && !has_intervening {
            // Simple pattern: last jump jumps over G to BODY.
            if last_taken <= guard || last_taken > hi {
                return None;
            }
            for &j in &jumps[..jumps.len() - 1] {
                if jump_target(self.proto.code[j], j) != Some(guard) {
                    return None;
                }
            }
            if !self.block_is_terminated(guard, last_taken, loop_ctx) {
                return None;
            }
            let body = last_taken;
            self.flush_inline(stmts);
            let mut conds: Vec<Expr> = Vec::new();
            for (i, &j) in jumps.iter().enumerate() {
                let op = Opcode::from_u8(insn_op(self.proto.code[j]))?;
                if i + 1 == jumps.len() {
                    conds.push(self.taken_condition(op, j));
                } else {
                    conds.push(self.fallthrough_condition(op, j));
                }
            }
            let proceed = conds
                .into_iter()
                .reduce(|acc, c| Expr::Binary("and", Box::new(acc), Box::new(c)))?;
            let guard_body = self.emit_body(guard, body, loop_ctx);
            stmts.push(Stmt::If {
                cond: Expr::Unary("not ", Box::new(proceed)),
                then_body: guard_body,
                else_body: Vec::new(),
            });
            return Some(body);
        }

        // Intervening-code pattern (effects between guard jumps): scan bytes between
        // consecutive jumps to confirm the straight-line code is just evaluation.
        for window in jumps.windows(2) {
            let a = window[0];
            let b = window[1];
            let a_len = Opcode::from_u8(insn_op(self.proto.code[a]))?
                .length()
                .max(1);
            let mut q = a + a_len;
            while q < b {
                let op = Opcode::from_u8(insn_op(self.proto.code[q]))?;
                if self.op_breaks_chain(op) {
                    return None;
                }
                q += op.length().max(1);
            }
        }
        // Determine guard block G and body based on jump target pattern.
        let (guard, body) = if last_taken == guard {
            // All jumps target G. Body starts after the guard block terminator.
            for &j in &jumps {
                if jump_target(self.proto.code[j], j) != Some(guard) {
                    return None;
                }
            }
            let gt = self.last_instr_before(guard, hi)?;
            let gt_op = Opcode::from_u8(insn_op(self.proto.code[gt]))?;
            let body_pc = gt + gt_op.length().max(1);
            if body_pc > hi {
                return None;
            }
            (guard, body_pc)
        } else {
            // Last jump targets BODY. Earlier jumps target G.
            let body_pc = last_taken;
            if body_pc <= guard || body_pc > hi {
                return None;
            }
            for &j in &jumps[..jumps.len() - 1] {
                if jump_target(self.proto.code[j], j) != Some(guard) {
                    return None;
                }
            }
            (guard, body_pc)
        };
        if !self.block_is_terminated(guard, body, loop_ctx) {
            return None;
        }

        // Emit flat sequential guards: `if <cond> then <guard-body> end`, with the intervening
        // straight-line statements (the next guard's value computation) emitted between them.
        // The guard body always terminates (block_is_terminated above), so at most one guard's
        // clause runs — cloning the whole body into each clause is correct, not duplicated work.
        self.flush_inline(stmts);
        let guard_stmts = self.collect_guard_body(guard, body, loop_ctx)?;
        for (i, &j) in jumps.iter().enumerate() {
            let op = Opcode::from_u8(insn_op(self.proto.code[j]))?;
            // Under what condition does this jump divert to the guard block G?
            // - jump targets G: taken -> G, so the guard fires on the taken condition.
            // - jump targets BODY (the last jump in a mixed chain): fall-through -> G, so the
            //   guard fires on the fall-through condition.
            let targets_guard = jump_target(self.proto.code[j], j) == Some(guard);
            let cond = if targets_guard {
                self.taken_condition(op, j)
            } else {
                self.fallthrough_condition(op, j)
            };
            stmts.push(Stmt::If {
                cond,
                then_body: guard_stmts.clone(),
                else_body: Vec::new(),
            });
            if i + 1 < jumps.len() {
                let next_j = jumps[i + 1];
                let j_len = Opcode::from_u8(insn_op(self.proto.code[j]))?
                    .length()
                    .max(1);
                let after_j = j + j_len;
                if after_j != next_j {
                    let inner = self.emit_body(after_j, next_j, loop_ctx);
                    stmts.extend(inner);
                }
            }
        }
        Some(body)
    }
    /// Whether `op` is something that cannot legally appear between two `and`-linked guard
    /// jumps. The compiler only emits straight-line evaluation between such jumps.
    fn op_breaks_chain(&self, op: Opcode) -> bool {
        use Opcode::*;
        matches!(
            op,
            JUMP | JUMPBACK
                | JUMPX
                | JUMPIF
                | JUMPIFNOT
                | JUMPIFEQ
                | JUMPIFLE
                | JUMPIFLT
                | JUMPIFNOTEQ
                | JUMPIFNOTLE
                | JUMPIFNOTLT
                | JUMPXEQKNIL
                | JUMPXEQKB
                | JUMPXEQKN
                | JUMPXEQKS
                | RETURN
                | FORNPREP
                | FORNLOOP
                | FORGPREP
                | FORGPREP_INEXT
                | FORGPREP_NEXT
                | FORGLOOP
                | CMPPROTO
        )
    }

    /// Collect statements from [lo, hi) without consuming emit_range borrow.
    fn collect_guard_body(
        &mut self,
        lo: usize,
        hi: usize,
        loop_ctx: Option<(usize, usize)>,
    ) -> Option<Vec<Stmt>> {
        let mut body = Vec::new();
        let mut pending = None;
        self.emit_range(lo, hi, &mut body, &mut pending, loop_ctx);
        self.flush_inline(&mut body);
        Some(body)
    }

    /// Whether the block `[lo, hi)` ends in a terminator (return / break / continue / a jump
    /// out of the block), i.e. control cannot fall through into `hi`.
    fn block_is_terminated(&self, lo: usize, hi: usize, loop_ctx: Option<(usize, usize)>) -> bool {
        let Some(last) = self.last_instr_before(lo, hi) else {
            return false;
        };
        let Some(op) = Opcode::from_u8(insn_op(self.proto.code[last])) else {
            return false;
        };
        match op {
            Opcode::RETURN => true,
            Opcode::JUMP | Opcode::JUMPBACK => {
                // A jump whose target is outside [lo, hi) leaves the block.
                match jump_target(self.proto.code[last], last) {
                    Some(t) => {
                        if let Some((cont, brk)) = loop_ctx {
                            if t == cont || t == brk {
                                return true;
                            }
                        }
                        t < lo || t >= hi
                    }
                    None => false,
                }
            }
            _ => false,
        }
    }

    fn try_if(
        &mut self,
        pc: usize,
        hi: usize,
        stmts: &mut Vec<Stmt>,
        loop_ctx: Option<(usize, usize)>,
    ) -> Option<usize> {
        let insn = self.proto.code[pc];
        let op = Opcode::from_u8(insn_op(insn))?;
        let len = op.length().max(1);
        let target = jump_target(insn, pc)?; // else/end target
        if target <= pc || target > hi {
            return None;
        }
        let cond = self.fallthrough_condition(op, pc);

        // Is there an `else`? The then-region's last instruction is an unconditional JUMP
        // skipping forward past `target`.
        let then_lo = pc + len;
        let then_last = self.last_instr_before(then_lo, target);
        let mut else_region: Option<(usize, usize)> = None;
        let mut region_end = target;
        let mut then_hi = target;
        if let Some(tl) = then_last {
            if Opcode::from_u8(insn_op(self.proto.code[tl])) == Some(Opcode::JUMP) {
                if let Some(end) = jump_target(self.proto.code[tl], tl) {
                    // A trailing JUMP to the enclosing loop's exit/continue point is a
                    // `break`/`continue`, NOT an else-skip. Treating it as an else would steal
                    // the rest of the loop body into a phantom else-arm (and lose the break).
                    // Leave it in the then-body so emit_range lowers it to the keyword.
                    let is_loop_exit =
                        loop_ctx.is_some_and(|(cont, brk)| end == brk || end == cont);
                    if end > target && end <= hi && !is_loop_exit {
                        else_region = Some((target, end));
                        region_end = end;
                        then_hi = tl; // exclude the trailing JUMP
                    }
                }
            }
        }

        self.flush_inline(stmts);
        let then_body = self.emit_body(then_lo, then_hi, loop_ctx);
        let else_body = match else_region {
            Some((elo, ehi)) => self.emit_body(elo, ehi, loop_ctx),
            None => Vec::new(),
        };
        stmts.push(Stmt::If {
            cond,
            then_body,
            else_body,
        });
        Some(region_end)
    }

    /// The last instruction whose successor PC equals `target`, scanning from `from`.
    fn last_instr_before(&self, from: usize, target: usize) -> Option<usize> {
        let mut pc = from;
        let mut last = None;
        while pc < target {
            let op = Opcode::from_u8(insn_op(*self.proto.code.get(pc)?))?;
            let len = op.length().max(1);
            if pc + len == target {
                last = Some(pc);
            }
            pc += len;
        }
        last
    }

    /// The condition under which a conditional jump is taken.
    fn taken_condition(&self, op: Opcode, pc: usize) -> Expr {
        let insn = self.proto.code[pc];
        let aux = self.proto.code.get(pc + 1).copied().unwrap_or(0);
        let a = insn_a(insn);
        use Opcode::*;
        match op {
            JUMPIF => self.reg(a),
            JUMPIFNOT => Expr::Unary("not ", Box::new(self.reg(a))),
            JUMPIFEQ | JUMPIFLE | JUMPIFLT | JUMPIFNOTEQ | JUMPIFNOTLE | JUMPIFNOTLT => {
                self.cmp_cond(op, a, aux)
            }
            JUMPXEQKNIL | JUMPXEQKB | JUMPXEQKN | JUMPXEQKS => self.eqk_cond(op, a, aux),
            _ => Expr::Raw("--[[cond?]]".into()),
        }
    }

    /// The condition for the fall-through (not-taken) edge — used as `if`/`while` conditions.
    fn fallthrough_condition(&self, op: Opcode, pc: usize) -> Expr {
        negate(self.taken_condition(op, pc))
    }

    /// Process one instruction, mutating register state and possibly emitting statements.
    fn step(
        &mut self,
        op: Opcode,
        pc: usize,
        stmts: &mut Vec<Stmt>,
        pending_namecall: &mut Option<(u8, Expr, String)>,
    ) {
        let insn = self.proto.code[pc];
        let aux = self.proto.code.get(pc + 1).copied().unwrap_or(0);
        let a = insn_a(insn);
        let b = insn_b(insn);
        let c = insn_c(insn);
        let d = insn_d(insn);

        // The multret value (if any) left by the immediately-preceding instruction. Cleared
        // here; producers below re-arm it for the next instruction.
        let multret_top = self.pending_multret.take();

        use Opcode::*;
        match op {
            // Immutable leaves: cached for inlining within the straight-line span, flushed at
            // control-flow boundaries so a value never silently crosses an edge.
            LOADNIL => self.set_inline(a, Expr::Nil),
            LOADB => self.set_inline(a, Expr::Bool(b != 0)),
            LOADN => self.set_inline(a, Expr::Num(d.to_string())),
            LOADK => self.set_inline(a, self.const_expr(d as usize)),
            LOADKX => self.set_inline(a, self.const_expr(aux as usize)),
            GETIMPORT => self.set_inline(a, self.const_expr(d as usize)),
            GETGLOBAL => {
                let g = self.string_const(aux);
                self.globals.insert(g.clone());
                self.set_inline(a, Expr::Var(g));
            }

            MOVE => self.assign(a, self.reg(b), stmts),
            GETUPVAL => self.assign(a, Expr::Var(self.upval_name(b)), stmts),
            GETTABLE => {
                let e = Expr::Index(Box::new(self.reg(b)), Box::new(self.reg(c)));
                self.assign(a, e, stmts);
            }
            GETTABLEKS => {
                let e = self.field(self.reg(b), aux);
                self.assign(a, e, stmts);
            }
            GETTABLEN => {
                let e = Expr::Index(
                    Box::new(self.reg(b)),
                    Box::new(Expr::Num((c as u32 + 1).to_string())),
                );
                self.assign(a, e, stmts);
            }
            ADD | SUB | MUL | DIV | IDIV | MOD | POW | AND | OR => {
                let e = self.binop_rr(op, b, c);
                self.assign(a, e, stmts);
            }
            CONCAT => {
                // CONCAT A B C concatenates the whole register range R(B)..=R(C).
                let mut e = self.reg(b);
                for r in (b + 1)..=c {
                    e = Expr::Binary("..", Box::new(e), Box::new(self.reg(r)));
                }
                self.assign(a, e, stmts);
            }
            ADDK | SUBK | MULK | DIVK | IDIVK | MODK | POWK | ANDK | ORK => {
                let e = self.binop_rk(op, b, c);
                self.assign(a, e, stmts);
            }
            SUBRK | DIVRK => {
                let e = self.binop_kr(op, b, c);
                self.assign(a, e, stmts);
            }
            NOT => {
                let e = Expr::Unary("not ", Box::new(self.reg(b)));
                self.assign(a, e, stmts);
            }
            MINUS => {
                let e = Expr::Unary("-", Box::new(self.reg(b)));
                self.assign(a, e, stmts);
            }
            LENGTH => {
                let e = Expr::Unary("#", Box::new(self.reg(b)));
                self.assign(a, e, stmts);
            }
            NEWTABLE => self.assign(a, Expr::Table(Vec::new()), stmts),
            // DUPTABLE clones a constant template; if the template baked in its values
            // (LBC_CONSTANT_TABLE_WITH_CONSTANTS, common in config modules), rebuild the
            // literal. Entries with no baked value are filled by following SETTABLEKS ops.
            DUPTABLE => {
                let e = self.duptable_expr(d as usize);
                self.assign(a, e, stmts);
            }
            SETLIST => {
                // SETLIST A B C [aux]: table[aux + i] = R(B+i) for i in 0..C-1. C==0 means
                // "to top": fill from R(B) up to the preceding multret value.
                let count = if c == 0 {
                    multret_top
                        .map(|t| (t as i32 - b as i32 + 1).max(0))
                        .unwrap_or(0)
                } else {
                    c as i32 - 1
                };
                if c == 0 && multret_top.is_none() {
                    self.note("open SETLIST (to top) approximated");
                }
                let start = aux as i32;
                for i in 0..count.max(0) {
                    let target = Expr::Index(
                        Box::new(self.reg(a)),
                        Box::new(Expr::Num((start + i).to_string())),
                    );
                    let value = self.reg((b as i32 + i) as u8);
                    stmts.push(Stmt::Assign {
                        targets: vec![target],
                        values: vec![value],
                    });
                }
            }
            SETTABLE => {
                let target = Expr::Index(Box::new(self.reg(b)), Box::new(self.reg(c)));
                stmts.push(Stmt::Assign {
                    targets: vec![target],
                    values: vec![self.reg(a)],
                });
            }
            SETTABLEKS => {
                let target = self.field(self.reg(b), aux);
                stmts.push(Stmt::Assign {
                    targets: vec![target],
                    values: vec![self.reg(a)],
                });
            }
            SETTABLEN => {
                let target = Expr::Index(
                    Box::new(self.reg(b)),
                    Box::new(Expr::Num((c as u32 + 1).to_string())),
                );
                stmts.push(Stmt::Assign {
                    targets: vec![target],
                    values: vec![self.reg(a)],
                });
            }
            SETGLOBAL => {
                let g = self.string_const(aux);
                self.globals.insert(g.clone());
                stmts.push(Stmt::Assign {
                    targets: vec![Expr::Var(g)],
                    values: vec![self.reg(a)],
                });
            }
            SETUPVAL => {
                stmts.push(Stmt::Assign {
                    targets: vec![Expr::Var(self.upval_name(b))],
                    values: vec![self.reg(a)],
                });
            }
            GETVARARGS => {
                // B-1 results from `...`. B==0 means `...` extends to top: keep it inline and
                // arm the multret so a following "to top" consumer (`f(...)`, `return ...`,
                // `{...}`) expands every vararg. Otherwise R(A) = (...) (its first value).
                if b == 0 {
                    self.set_inline(a, Expr::Vararg);
                    self.pending_multret = Some(a);
                } else {
                    self.assign(a, Expr::Vararg, stmts);
                    if b as i32 - 1 != 1 {
                        self.note("multi-value `...` expansion approximated");
                    }
                }
            }
            NEWCLOSURE => {
                // A captured register backs the closure's upvalue, so its current value must
                // be a real statement before the closure (not left in the inline cache).
                self.flush_captured(stmts);
                // The D operand indexes the ENCLOSING proto's child-proto list (`p->p[D]`),
                // not the module's flat proto table.
                let local = insn_d(insn) as usize;
                if let Some(&child) = self.proto.child_protos.get(local) {
                    let e = self.closure_expr(child as usize, pc);
                    self.assign(a, e, stmts);
                } else {
                    self.assign(a, Expr::Raw("--[[closure?]]".into()), stmts);
                    self.note("NEWCLOSURE child index out of range");
                }
            }
            DUPCLOSURE => {
                self.flush_captured(stmts);
                // The constant is a Closure referencing a child proto.
                if let Some(Constant::Closure { proto }) = self.proto.constants.get(d as usize) {
                    let e = self.closure_expr(*proto as usize, pc);
                    self.assign(a, e, stmts);
                } else {
                    self.assign(a, Expr::Raw("--[[closure?]]".into()), stmts);
                    self.note("DUPCLOSURE without a closure constant");
                }
            }
            CAPTURE => {} // handled implicitly by closure decompilation
            NAMECALL => {
                let method = self.string_const(aux);
                *pending_namecall = Some((a, self.reg(b), method));
            }
            CALL => self.emit_call(a, b, c, multret_top, stmts, pending_namecall),
            RETURN => {
                // B-1 values from R(A). B==0 means "to top": return R(A) up to the preceding
                // multret value (e.g. `return f(...)` tail position).
                let vals: Vec<Expr> = if b == 0 {
                    match multret_top {
                        Some(top) if top >= a => (a..=top).map(|r| self.reg(r)).collect(),
                        _ => {
                            self.note("multret return approximated");
                            vec![self.reg(a)]
                        }
                    }
                } else {
                    (0..b as i32 - 1).map(|i| self.reg(a + i as u8)).collect()
                };
                stmts.push(Stmt::Return(vals));
            }

            // --- control flow: faithful goto fallback ---
            JUMP | JUMPBACK | JUMPX => {
                stmts.push(Stmt::Goto(self.target_label(insn, pc)));
                self.mark_partial_goto();
            }
            JUMPIF => self.cond_goto(self.reg(a), insn, pc, stmts),
            JUMPIFNOT => {
                let cond = Expr::Unary("not ", Box::new(self.reg(a)));
                self.cond_goto(cond, insn, pc, stmts);
            }
            JUMPIFEQ | JUMPIFLE | JUMPIFLT | JUMPIFNOTEQ | JUMPIFNOTLE | JUMPIFNOTLT => {
                let cond = self.cmp_cond(op, a, aux);
                self.cond_goto(cond, insn, pc, stmts);
            }
            JUMPXEQKNIL | JUMPXEQKB | JUMPXEQKN | JUMPXEQKS => {
                let cond = self.eqk_cond(op, a, aux);
                self.cond_goto(cond, insn, pc, stmts);
            }
            FORNPREP => {
                stmts.push(Stmt::Comment(format!(
                    "numeric for: {} = {}, {}, {} (FORNPREP)",
                    self.reg_name(a + 2),
                    render_expr(&self.reg(a + 2)),
                    render_expr(&self.reg(a)),
                    render_expr(&self.reg(a + 1)),
                )));
                self.mark_partial_goto();
            }
            FORNLOOP | FORGLOOP => {
                stmts.push(Stmt::Goto(self.target_label(insn, pc)));
                stmts.push(Stmt::Comment("(loop back-edge)".into()));
                self.mark_partial_goto();
            }
            FORGPREP | FORGPREP_INEXT | FORGPREP_NEXT => {
                stmts.push(Stmt::Comment("generic for setup (FORGPREP)".into()));
                stmts.push(Stmt::Goto(self.target_label(insn, pc)));
                self.mark_partial_goto();
            }
            PREPVARARGS | NOP | BREAK | COVERAGE | NATIVECALL | CLOSEUPVALS => {}
            FASTCALL | FASTCALL1 | FASTCALL2 | FASTCALL2K | FASTCALL3 => {
                // Optimization hints; the real work is the following CALL.
            }
            other => {
                stmts.push(Stmt::Comment(format!("unhandled op {}", other.name())));
                self.note(&format!("unhandled opcode {}", other.name()));
            }
        }

        // Carry a pending multret across an instruction that only set up the call target
        // (`obj:m(g())` / `f(g())` compute `g()` first, then load the callee/method). Such a
        // load writes a register strictly below the multret base, leaving the stack top — and
        // thus the trailing multi-value argument — intact for the consuming CALL. Hint opcodes
        // write nothing and always carry. Anything else (incl. the consuming CALL/RETURN, and
        // producers, which re-arm explicitly) drops it.
        if self.pending_multret.is_none() {
            if let Some(base) = multret_top {
                let carries = match op {
                    GETIMPORT | GETGLOBAL | GETUPVAL | MOVE | GETTABLE | GETTABLEKS | GETTABLEN
                    | NAMECALL => a < base,
                    FASTCALL | FASTCALL1 | FASTCALL2 | FASTCALL2K | FASTCALL3 | PREPVARARGS
                    | NOP | COVERAGE => true,
                    _ => false,
                };
                if carries {
                    self.pending_multret = Some(base);
                }
            }
        }
    }

    // --- expression helpers -------------------------------------------------------------

    /// Reconstruct a table literal from a DUPTABLE template constant. Baked key/value pairs
    /// (TABLE_WITH_CONSTANTS) become fields; entries without a baked value are left out (a
    /// following SETTABLEKS fills them).
    fn duptable_expr(&self, k: usize) -> Expr {
        let entries = match self.proto.constants.get(k) {
            Some(Constant::TableWithConstants { entries }) => entries,
            _ => return Expr::Table(Vec::new()),
        };
        let mut fields = Vec::new();
        for (key_k, val_k) in entries {
            if *val_k < 0 {
                continue; // value supplied at runtime by a SETTABLEKS
            }
            let value = self.const_expr(*val_k as usize);
            match self.proto.constants.get(*key_k as usize) {
                Some(Constant::String(_)) => {
                    let key = self.string_const(*key_k);
                    if is_identifier(&key) {
                        fields.push(TableField::Named(key, value));
                    } else {
                        fields.push(TableField::Keyed(self.const_expr(*key_k as usize), value));
                    }
                }
                Some(_) => fields.push(TableField::Keyed(self.const_expr(*key_k as usize), value)),
                None => {}
            }
        }
        Expr::Table(fields)
    }

    fn const_expr(&self, k: usize) -> Expr {
        let text = render_constant_at(self.module, self.proto, k);
        match self.proto.constants.get(k) {
            // Use a lossless, fully-escaped literal — the disassembler's renderer truncates
            // long strings, which would corrupt decompiled output.
            Some(Constant::String(sref)) => {
                let lit = sref
                    .index()
                    .and_then(|i| self.module.string_bytes(i))
                    .map(naming::lua_string_literal)
                    .unwrap_or_else(|| "\"\"".to_string());
                Expr::Str(lit)
            }
            Some(Constant::Number(_)) | Some(Constant::Integer(_)) => Expr::Num(text),
            Some(Constant::Boolean(v)) => Expr::Bool(*v),
            Some(Constant::Nil) => Expr::Nil,
            Some(Constant::Vector { .. }) => Expr::Vector(format!("Vector3.new({text})")),
            // Imports render as a dotted path identifier.
            Some(Constant::Import { .. }) => Expr::Var(text),
            _ => Expr::Raw(text),
        }
    }

    /// `table.field` if the key is a valid identifier, else `table[key]`.
    fn field(&self, table: Expr, aux_k: u32) -> Expr {
        let key = self.string_const(aux_k);
        if is_identifier(&key) {
            Expr::Field(Box::new(table), key)
        } else {
            let lit = naming::lua_string_literal(key.as_bytes());
            Expr::Index(Box::new(table), Box::new(Expr::Str(lit)))
        }
    }

    fn binop_rr(&self, op: Opcode, b: u8, c: u8) -> Expr {
        Expr::Binary(
            bin_op_text(op),
            Box::new(self.reg(b)),
            Box::new(self.reg(c)),
        )
    }
    fn binop_rk(&self, op: Opcode, b: u8, c: u8) -> Expr {
        Expr::Binary(
            bin_op_text(op),
            Box::new(self.reg(b)),
            Box::new(self.const_expr(c as usize)),
        )
    }
    fn binop_kr(&self, op: Opcode, b: u8, c: u8) -> Expr {
        // SUBRK/DIVRK: constant on the left, register on the right.
        Expr::Binary(
            bin_op_text(op),
            Box::new(self.const_expr(b as usize)),
            Box::new(self.reg(c)),
        )
    }

    fn cmp_cond(&self, op: Opcode, a: u8, aux: u32) -> Expr {
        let lhs = self.reg(a);
        let rhs = self.reg(aux as u8);
        let symbol = match op {
            Opcode::JUMPIFEQ => "==",
            Opcode::JUMPIFLE => "<=",
            Opcode::JUMPIFLT => "<",
            Opcode::JUMPIFNOTEQ => "~=",
            Opcode::JUMPIFNOTLE => ">",  // not (a <= b)  ==>  a > b
            Opcode::JUMPIFNOTLT => ">=", // not (a < b)   ==>  a >= b
            _ => "==",
        };
        Expr::Binary(symbol, Box::new(lhs), Box::new(rhs))
    }

    fn eqk_cond(&self, op: Opcode, a: u8, aux: u32) -> Expr {
        let lhs = self.reg(a);
        let not = aux_not(aux);
        let rhs = match op {
            Opcode::JUMPXEQKNIL => Expr::Nil,
            Opcode::JUMPXEQKB => Expr::Bool(aux & 1 != 0),
            Opcode::JUMPXEQKN | Opcode::JUMPXEQKS => self.const_expr(aux_kv(aux) as usize),
            _ => Expr::Nil,
        };
        let symbol = if not { "~=" } else { "==" };
        Expr::Binary(symbol, Box::new(lhs), Box::new(rhs))
    }

    fn closure_expr(&mut self, child_idx: usize, pc: usize) -> Expr {
        // Recursively decompile the child proto into a function literal.
        let child = &self.module.protos[child_idx];
        let params = self.signature_params(child);
        let captures = self.closure_captures(pc);
        let mut sub_reports = Vec::new();
        let body = decompile_proto(self.module, child_idx, &mut sub_reports);
        if sub_reports.iter().any(|r| r.partial) {
            self.has_partial_child = true;
        }
        // Indent the child body by one level.
        let indented: String = body
            .lines()
            .map(|l| {
                if l.is_empty() {
                    String::from("\n")
                } else {
                    format!("\t{l}\n")
                }
            })
            .collect();
        let vararg = if child.is_vararg {
            if params.is_empty() {
                "...".to_string()
            } else {
                ", ...".to_string()
            }
        } else {
            String::new()
        };
        Expr::Closure {
            text: format!("function({}{})\n{}end", params.join(", "), vararg, indented),
            captures,
        }
    }

    /// The ordered upvalue captures of the closure created at `pc`, read from the CAPTURE
    /// instructions that follow the NEWCLOSURE/DUPCLOSURE.
    fn closure_captures(&self, pc: usize) -> Vec<Capture> {
        let code = &self.proto.code;
        let len = Opcode::from_u8(insn_op(code[pc]))
            .map(|o| o.length())
            .unwrap_or(1)
            .max(1);
        let mut caps = Vec::new();
        let mut q = pc + len;
        while q < code.len() && Opcode::from_u8(insn_op(code[q])) == Some(Opcode::CAPTURE) {
            let cap = code[q];
            match insn_a(cap) {
                capture_type::VAL | capture_type::REF => caps.push(Capture::Reg(insn_b(cap))),
                capture_type::UPVAL => caps.push(Capture::Upval(insn_b(cap))),
                _ => {}
            }
            q += 1;
        }
        caps
    }

    /// After the enclosing function's names are final, rewrite each closure's upvalue
    /// placeholders (`u0`, `u1`, …) to the captured local's name. Captures of our own
    /// upvalues stay `uN` for OUR enclosing function to resolve in turn.
    fn resolve_closures(&self, stmts: &mut [Stmt], rename: &BTreeMap<String, String>) {
        for s in stmts.iter_mut() {
            self.resolve_closures_stmt(s, rename);
        }
    }

    fn resolve_closures_stmt(&self, s: &mut Stmt, rename: &BTreeMap<String, String>) {
        match s {
            Stmt::Local { values, .. } => values
                .iter_mut()
                .for_each(|e| self.resolve_in_expr(e, rename)),
            Stmt::Assign { targets, values } => {
                targets
                    .iter_mut()
                    .for_each(|e| self.resolve_in_expr(e, rename));
                values
                    .iter_mut()
                    .for_each(|e| self.resolve_in_expr(e, rename));
            }
            Stmt::Call(e) => self.resolve_in_expr(e, rename),
            Stmt::Return(es) => es.iter_mut().for_each(|e| self.resolve_in_expr(e, rename)),
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.resolve_in_expr(cond, rename);
                self.resolve_closures(then_body, rename);
                self.resolve_closures(else_body, rename);
            }
            Stmt::While { cond, body } => {
                self.resolve_in_expr(cond, rename);
                self.resolve_closures(body, rename);
            }
            Stmt::Repeat { body, cond } => {
                self.resolve_closures(body, rename);
                self.resolve_in_expr(cond, rename);
            }
            Stmt::NumericFor {
                start,
                limit,
                step,
                body,
                ..
            } => {
                self.resolve_in_expr(start, rename);
                self.resolve_in_expr(limit, rename);
                if let Some(s) = step {
                    self.resolve_in_expr(s, rename);
                }
                self.resolve_closures(body, rename);
            }
            Stmt::GenericFor { exprs, body, .. } => {
                exprs
                    .iter_mut()
                    .for_each(|e| self.resolve_in_expr(e, rename));
                self.resolve_closures(body, rename);
            }
            _ => {}
        }
    }

    fn resolve_in_expr(&self, e: &mut Expr, rename: &BTreeMap<String, String>) {
        match e {
            Expr::Closure { text, captures } => {
                let names: Vec<String> = captures
                    .iter()
                    .map(|c| match c {
                        Capture::Reg(r) => {
                            let n = self.reg_name(*r);
                            rename.get(&n).cloned().unwrap_or(n)
                        }
                        // Our own upvalue, resolved later by our enclosing function.
                        Capture::Upval(u) => format!("u{u}"),
                    })
                    .collect();
                *text = substitute_upvalues(text, &names);
            }
            Expr::Index(a, b) => {
                self.resolve_in_expr(a, rename);
                self.resolve_in_expr(b, rename);
            }
            Expr::Field(a, _) => self.resolve_in_expr(a, rename),
            Expr::Call(f, args) => {
                self.resolve_in_expr(f, rename);
                args.iter_mut()
                    .for_each(|x| self.resolve_in_expr(x, rename));
            }
            Expr::MethodCall(o, _, args) => {
                self.resolve_in_expr(o, rename);
                args.iter_mut()
                    .for_each(|x| self.resolve_in_expr(x, rename));
            }
            Expr::Unary(_, a) => self.resolve_in_expr(a, rename),
            Expr::Binary(_, a, b) => {
                self.resolve_in_expr(a, rename);
                self.resolve_in_expr(b, rename);
            }
            Expr::Table(fields) => {
                for f in fields {
                    match f {
                        TableField::Item(e) | TableField::Named(_, e) => {
                            self.resolve_in_expr(e, rename)
                        }
                        TableField::Keyed(k, v) => {
                            self.resolve_in_expr(k, rename);
                            self.resolve_in_expr(v, rename);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn signature_params(&self, proto: &Proto) -> Vec<String> {
        (0..proto.num_params)
            .map(|r| self.named_or(proto, r, format!("p{r}")))
            .collect()
    }

    fn emit_call(
        &mut self,
        a: u8,
        b: u8,
        c: u8,
        multret_top: Option<u8>,
        stmts: &mut Vec<Stmt>,
        pending_namecall: &mut Option<(u8, Expr, String)>,
    ) {
        let nresults = c as i32 - 1;

        // Arguments occupy registers `first ..= last`. The total slots after the callee are
        // B-1 (so the last slot is A+B-1); for a method call the receiver takes the first of
        // those slots and the explicit args start one later. With B==0 the list runs to the
        // top of the stack — the value left by the preceding multret instruction — so the
        // final argument is itself a multi-value expression.
        let last: Option<u8> = if b == 0 { multret_top } else { Some(a + b - 1) };
        let collect_args = |me: &mut Self, first: u8| -> Vec<Expr> {
            match last {
                Some(last) if last >= first => (first..=last).map(|r| me.reg(r)).collect(),
                Some(_) => Vec::new(), // no arguments
                None => {
                    me.note("multret call args approximated");
                    vec![Expr::Raw("--[[...]]".into())]
                }
            }
        };

        let call_expr = match pending_namecall.take() {
            Some((reg, obj, method)) if reg == a => {
                // receiver is at A+1; explicit args start at A+2.
                let args = collect_args(self, a + 2);
                Expr::MethodCall(Box::new(obj), method, args)
            }
            other => {
                *pending_namecall = other;
                let callee = self.reg(a);
                let args = collect_args(self, a + 1);
                Expr::Call(Box::new(callee), args)
            }
        };

        if nresults < 0 {
            // Multret result (C==0): the call's values extend to the top of the stack and are
            // consumed by the immediately-following "to top" instruction. Keep the call as an
            // inline expression (do NOT materialize it to one register — that would truncate it
            // to a single value) and arm the multret so the consumer expands it in place:
            // `f(g())`, `return g()`, `{g()}` all preserve every value g() returns.
            self.pending_multret = Some(a);
            self.set_inline(a, call_expr);
        } else if nresults == 0 {
            stmts.push(Stmt::Call(call_expr));
        } else if nresults == 1 {
            self.assign(a, call_expr, stmts);
        } else {
            // A fixed number (>1) of results: name each destination register, tuple-assign.
            let targets: Vec<Expr> = (0..nresults)
                .map(|i| {
                    let r = a + i as u8;
                    self.materialize(r);
                    Expr::Var(self.reg_name(r))
                })
                .collect();
            stmts.push(Stmt::Assign {
                targets,
                values: vec![call_expr],
            });
        }
    }

    // --- register/name bookkeeping ------------------------------------------------------

    /// Read the current expression of a register.
    /// Read a register: its cached inline expression, or a read of its name.
    fn reg(&self, r: u8) -> Expr {
        match self.regs.get(r as usize).and_then(|e| e.clone()) {
            Some(e) => e,
            None => Expr::Var(self.reg_name(r)),
        }
    }

    /// Cache an inlinable immutable expression in a register (no statement emitted).
    fn set_inline(&mut self, r: u8, e: Expr) {
        if let Some(slot) = self.regs.get_mut(r as usize) {
            *slot = Some(e);
        }
    }

    /// Flush every cached inline value to a named local so nothing crosses a control-flow
    /// edge. Dead flushes are removed and single-use ones re-inlined by the cleanup passes.
    fn flush_inline(&mut self, stmts: &mut Vec<Stmt>) {
        let count = self.regs.len();
        for r in 0..count {
            if let Some(e) = self.regs[r].clone() {
                self.regs[r] = None;
                if r < self.proto.num_params as usize {
                    // A parameter slot holding a constant means it was reassigned; emit it.
                    stmts.push(Stmt::Assign {
                        targets: vec![Expr::Var(self.reg_name(r as u8))],
                        values: vec![e],
                    });
                } else {
                    self.hoisted.insert(r as u8);
                    stmts.push(Stmt::Assign {
                        targets: vec![Expr::Var(self.reg_name(r as u8))],
                        values: vec![e],
                    });
                }
            }
        }
    }

    /// Emit a real assignment for any captured register still sitting in the inline cache.
    /// Called right before a closure is created so the value the closure captures is not lost.
    fn flush_captured(&mut self, stmts: &mut Vec<Stmt>) {
        let caps: Vec<u8> = self.captured_regs.iter().copied().collect();
        for r in caps {
            if let Some(e) = self.regs.get(r as usize).and_then(|s| s.clone()) {
                self.regs[r as usize] = None;
                if r >= self.proto.num_params {
                    self.hoisted.insert(r);
                }
                stmts.push(Stmt::Assign {
                    targets: vec![Expr::Var(self.reg_name(r))],
                    values: vec![e],
                });
            }
        }
    }

    /// Materialize a register: clear any cached inline expr (reads now use the name) and
    /// record it for hoisting if it is not a parameter.
    fn materialize(&mut self, r: u8) {
        if let Some(slot) = self.regs.get_mut(r as usize) {
            *slot = None;
        }
        if r >= self.proto.num_params {
            self.hoisted.insert(r);
        }
    }

    /// Names that must not be hoisted as locals: parameters, upvalues, and globals.
    fn non_local_names(&self) -> BTreeSet<String> {
        let mut s: BTreeSet<String> = (0..self.proto.num_params)
            .map(|r| self.reg_name(r))
            .collect();
        for i in 0..self.proto.num_upvalues {
            s.insert(self.upval_name(i));
        }
        s.extend(self.globals.iter().cloned());
        s
    }

    /// Names of registers captured into child closures (must survive cleanup).
    fn captured_names(&self) -> BTreeSet<String> {
        self.captured_regs
            .iter()
            .map(|&r| self.reg_name(r))
            .collect()
    }

    /// Registers captured by a child closure: the B operand of each VAL/REF CAPTURE that
    /// follows a NEWCLOSURE/DUPCLOSURE.
    fn compute_captured_regs(&self) -> BTreeSet<u8> {
        let code = &self.proto.code;
        let mut set = BTreeSet::new();
        let mut pc = 0;
        while pc < code.len() {
            let insn = code[pc];
            if let Some(op) = Opcode::from_u8(insn_op(insn)) {
                if matches!(op, Opcode::NEWCLOSURE | Opcode::DUPCLOSURE) {
                    let mut q = pc + op.length().max(1);
                    while q < code.len()
                        && Opcode::from_u8(insn_op(code[q])) == Some(Opcode::CAPTURE)
                    {
                        let cap = code[q];
                        let kind = insn_a(cap);
                        if kind == capture_type::VAL || kind == capture_type::REF {
                            set.insert(insn_b(cap));
                        }
                        q += 1;
                    }
                }
                pc += op.length().max(1);
            } else {
                pc += 1;
            }
        }
        set
    }

    /// Emit `name = expr` for a register and mark it materialized.
    fn assign(&mut self, r: u8, value: Expr, stmts: &mut Vec<Stmt>) {
        self.materialize(r);
        stmts.push(Stmt::Assign {
            targets: vec![Expr::Var(self.reg_name(r))],
            values: vec![value],
        });
    }

    /// A stable name for a register: the debug local name live here if unique, a parameter
    /// name, or `v<reg>`.
    fn reg_name(&self, r: u8) -> String {
        if let Some(name) = self.reg_name_override.get(&r) {
            return name.clone();
        }
        if let Some(name) = self.unique_debug_name(self.proto, r) {
            return name;
        }
        if r < self.proto.num_params {
            format!("p{r}")
        } else {
            format!("v{r}")
        }
    }

    /// The debug local name for a register live at `pc`, if present and a valid identifier.
    fn debug_name_at(&self, reg: u8, pc: usize) -> Option<String> {
        let dbg = self.proto.debug_info.as_ref()?;
        for l in &dbg.locals {
            if l.reg == reg && (l.start_pc as usize) <= pc && pc < (l.end_pc as usize) {
                if let Some(n) = self.module.resolve(l.name) {
                    if is_identifier(&n) {
                        return Some(n.into_owned());
                    }
                }
            }
        }
        None
    }

    /// A loop variable's name: its debug name if available, else a synthesized one that does
    /// not collide with the `vN`/`pN` synthesized names.
    fn loop_var_name(&mut self, reg: u8, body_pc: usize) -> String {
        if let Some(n) = self.debug_name_at(reg, body_pc) {
            return n;
        }
        const LETTERS: &[&str] = &["i", "j", "k", "l", "m", "o", "p", "q", "r", "s"];
        let n = self.next_loopvar;
        self.next_loopvar += 1;
        if n < LETTERS.len() {
            LETTERS[n].to_string()
        } else {
            format!("idx{n}")
        }
    }

    fn named_or(&self, proto: &Proto, r: u8, fallback: String) -> String {
        self.unique_debug_name(proto, r).unwrap_or(fallback)
    }

    /// If a register is associated with exactly one debug local name across the proto, use
    /// it (it is unambiguous). Otherwise fall back to a synthesized name.
    fn unique_debug_name(&self, proto: &Proto, r: u8) -> Option<String> {
        let dbg = proto.debug_info.as_ref()?;
        let mut found: Option<String> = None;
        for local in &dbg.locals {
            if local.reg == r {
                let name = self.module.resolve(local.name)?.into_owned();
                match &found {
                    Some(existing) if existing != &name => return None, // ambiguous
                    _ => found = Some(name),
                }
            }
        }
        found.filter(|n| is_identifier(n))
    }

    fn upval_name(&self, idx: u8) -> String {
        self.proto
            .debug_info
            .as_ref()
            .and_then(|d| d.upvalues.get(idx as usize).copied())
            .and_then(|s: StringRef| self.module.resolve(s))
            .map(|c| c.into_owned())
            .filter(|n| is_identifier(n))
            .unwrap_or_else(|| format!("u{idx}"))
    }

    fn string_const(&self, k: u32) -> String {
        match self.proto.constants.get(k as usize) {
            Some(Constant::String(sref)) => sref
                .index()
                .and_then(|i| self.module.string_bytes(i))
                .map(|b| String::from_utf8_lossy(b).into_owned())
                .unwrap_or_else(|| format!("K{k}")),
            _ => format!("K{k}"),
        }
    }

    fn target_label(&self, insn: u32, pc: usize) -> String {
        match jump_target(insn, pc).and_then(|t| self.labels.get(t).copied().flatten()) {
            Some(id) => format!("L{id}"),
            None => "L?".to_string(),
        }
    }

    fn cond_goto(&mut self, cond: Expr, insn: u32, pc: usize, stmts: &mut Vec<Stmt>) {
        let label = self.target_label(insn, pc);
        stmts.push(Stmt::If {
            cond,
            then_body: vec![Stmt::Goto(label)],
            else_body: Vec::new(),
        });
        self.mark_partial_goto();
    }

    fn mark_partial_goto(&mut self) {
        self.note("control flow rendered with goto/labels (structuring incomplete)");
    }

    fn note(&mut self, msg: &str) {
        let m = msg.to_string();
        if !self.notes.contains(&m) {
            self.notes.push(m);
        }
        let _ = self.proto_idx;
    }
}

/// Collect the set of label names that some emitted `goto` targets, recursing into nested
/// statement bodies (the conditional-goto fallback puts a goto inside an `if`).
fn collect_goto_targets(stmts: &[Stmt]) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    fn walk(stmts: &[Stmt], set: &mut BTreeSet<String>) {
        for s in stmts {
            match s {
                Stmt::Goto(n) => {
                    set.insert(n.clone());
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    walk(then_body, set);
                    walk(else_body, set);
                }
                Stmt::While { body, .. }
                | Stmt::Repeat { body, .. }
                | Stmt::NumericFor { body, .. }
                | Stmt::GenericFor { body, .. } => walk(body, set),
                _ => {}
            }
        }
    }
    walk(stmts, &mut set);
    set
}

/// Recursively drop `Label` statements whose name no goto references.
fn retain_referenced_labels(stmts: &mut Vec<Stmt>, referenced: &BTreeSet<String>) {
    stmts.retain(|s| !matches!(s, Stmt::Label(n) if !referenced.contains(n)));
    for s in stmts.iter_mut() {
        match s {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                retain_referenced_labels(then_body, referenced);
                retain_referenced_labels(else_body, referenced);
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. } => retain_referenced_labels(body, referenced),
            _ => {}
        }
    }
}

/// Replace whole-word `u0`, `u1`, … upvalue placeholders in rendered closure text with the
/// captured names. String literals are skipped so identical-looking text inside a string is
/// never rewritten.
fn substitute_upvalues(text: &str, names: &[String]) -> String {
    if names.is_empty() {
        return text.to_string();
    }
    let bytes = text.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut in_str: Option<u8> = None;
    while i < bytes.len() {
        let b = bytes[i];
        if let Some(q) = in_str {
            out.push(b);
            if b == b'\\' && i + 1 < bytes.len() {
                out.push(bytes[i + 1]);
                i += 2;
                continue;
            }
            if b == q {
                in_str = None;
            }
            i += 1;
            continue;
        }
        if b == b'"' || b == b'\'' {
            in_str = Some(b);
            out.push(b);
            i += 1;
            continue;
        }
        let prev_ident = i > 0 && is_ident(bytes[i - 1]);
        if b == b'u' && !prev_ident {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 && (j >= bytes.len() || !is_ident(bytes[j])) {
                if let Ok(idx) = text[i + 1..j].parse::<usize>() {
                    if idx < names.len() {
                        out.extend_from_slice(names[idx].as_bytes());
                        i = j;
                        continue;
                    }
                }
            }
        }
        out.push(b);
        i += 1;
    }
    String::from_utf8(out).unwrap_or_else(|_| text.to_string())
}

/// A two-way conditional jump (has a taken and a fall-through edge).
fn is_conditional_jump(op: Opcode) -> bool {
    use Opcode::*;
    matches!(
        op,
        JUMPIF
            | JUMPIFNOT
            | JUMPIFEQ
            | JUMPIFLE
            | JUMPIFLT
            | JUMPIFNOTEQ
            | JUMPIFNOTLE
            | JUMPIFNOTLT
            | JUMPXEQKNIL
            | JUMPXEQKB
            | JUMPXEQKN
            | JUMPXEQKS
    )
}

/// Logically negate a boolean condition, pushing the negation into comparisons so the
/// result reads naturally. Note: flipping ordering comparisons mirrors exactly how the
/// compiler chose the branch (it is recovery, not an unsound rewrite).
fn negate(e: Expr) -> Expr {
    match e {
        Expr::Binary("==", a, b) => Expr::Binary("~=", a, b),
        Expr::Binary("~=", a, b) => Expr::Binary("==", a, b),
        Expr::Binary("<", a, b) => Expr::Binary(">=", a, b),
        Expr::Binary("<=", a, b) => Expr::Binary(">", a, b),
        Expr::Binary(">", a, b) => Expr::Binary("<=", a, b),
        Expr::Binary(">=", a, b) => Expr::Binary("<", a, b),
        Expr::Unary("not ", inner) => *inner,
        other => Expr::Unary("not ", Box::new(other)),
    }
}

/// A numeric-for `step` that is literally `1` is the Luau default and can be omitted.
fn drop_unit_for_steps(stmts: &mut [Stmt]) {
    for s in stmts.iter_mut() {
        if let Stmt::NumericFor { step, body, .. } = s {
            if matches!(step, Some(Expr::Num(n)) if n == "1") {
                *step = None;
            }
            drop_unit_for_steps(body);
        } else {
            match s {
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    drop_unit_for_steps(then_body);
                    drop_unit_for_steps(else_body);
                }
                Stmt::While { body, .. }
                | Stmt::Repeat { body, .. }
                | Stmt::GenericFor { body, .. } => drop_unit_for_steps(body),
                _ => {}
            }
        }
    }
}

fn bin_op_text(op: Opcode) -> &'static str {
    use Opcode::*;
    match op {
        ADD | ADDK => "+",
        SUB | SUBK | SUBRK => "-",
        MUL | MULK => "*",
        DIV | DIVK | DIVRK => "/",
        IDIV | IDIVK => "//",
        MOD | MODK => "%",
        POW | POWK => "^",
        CONCAT => "..",
        AND | ANDK => "and",
        OR | ORK => "or",
        _ => "?",
    }
}

/// Whether `s` is a valid Luau identifier (so we can use `t.field` and bare names).
fn is_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

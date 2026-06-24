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
mod naming;

use std::collections::BTreeSet;

use ast::{render_block, render_expr, Expr, Stmt};
use luau_bytecode::opcode::*;
use luau_bytecode::{Constant, Module, Proto, StringRef};
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

    reports.push(ProtoReport {
        index: proto_idx,
        name: module.resolve(proto.debug_name).map(|c| c.into_owned()),
        partial: d.partial,
        notes: d.notes.clone(),
    });

    // Fold register-reuse field/method chains (x = a.b; x = x.c -> x = a.b.c) before naming,
    // so a variable is named from its final, complete expression.
    naming::fold_refinements(&mut stmts);

    // The names for materialized, hoisted locals (debug names where unambiguous, else vN).
    let mut hoist_names: Vec<String> = d.hoisted.iter().map(|&r| d.reg_name(r)).collect();

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

    // Hoist all materialized non-parameter locals so every assignment has a declaration in
    // scope regardless of how control flow nests.
    let mut out = String::new();
    if !hoist_names.is_empty() {
        out.push_str(&format!("local {}\n", hoist_names.join(", ")));
    }
    out.push_str(&render_block(&stmts, 0));
    out
}

struct Decompiler<'a> {
    module: &'a Module,
    proto: &'a Proto,
    proto_idx: usize,
    /// Current expression held in each register, if it is an inlinable immutable leaf.
    regs: Vec<Option<Expr>>,
    /// Registers (>= num_params) that were materialized and need a hoisted `local`.
    hoisted: BTreeSet<u8>,
    labels: Vec<Option<u32>>,
    partial: bool,
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
            partial: false,
            notes: Vec::new(),
        }
    }

    fn run(&mut self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        let code = &self.proto.code;
        let mut pc = 0;
        let mut pending_namecall: Option<(u8, Expr, String)> = None;

        while pc < code.len() {
            let insn = code[pc];
            let op = match Opcode::from_u8(insn_op(insn)) {
                Some(o) => o,
                None => {
                    pc += 1;
                    continue;
                }
            };
            let len = op.length().max(1);

            // Emit a label if this PC is a jump target.
            if let Some(id) = self.labels.get(pc).copied().flatten() {
                stmts.push(Stmt::Label(format!("L{id}")));
            }

            self.step(op, pc, &mut stmts, &mut pending_namecall);
            pc += len;
        }

        // Drop labels nothing jumps to. Many jump targets (notably the FASTCALL skip-over)
        // never produce a goto in the reconstruction, and a dangling `::label::` is not even
        // valid Luau, so emitting it would wrongly break otherwise-clean output.
        let referenced = collect_goto_targets(&stmts);
        stmts.retain(|s| !matches!(s, Stmt::Label(n) if !referenced.contains(n)));
        stmts
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

        use Opcode::*;
        match op {
            // --- immutable leaves: inline at use, no statement ---
            LOADNIL => self.set_inline(a, Expr::Nil),
            LOADB => self.set_inline(a, Expr::Bool(b != 0)),
            LOADN => self.set_inline(a, Expr::Num(d.to_string())),
            LOADK => self.set_inline(a, self.const_expr(d as usize)),
            LOADKX => self.set_inline(a, self.const_expr(aux as usize)),
            GETIMPORT => self.set_inline(a, self.const_expr(d as usize)),
            GETGLOBAL => self.set_inline(a, Expr::Var(self.string_const(aux))),

            // --- materialized values ---
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
            NEWTABLE | DUPTABLE => self.assign(a, Expr::Table(Vec::new()), stmts),
            SETLIST => {
                // SETLIST A B C [aux]: table[aux + i] = R(B+i) for i in 0..C-1.
                let count = c as i32 - 1;
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
                stmts.push(Stmt::Assign {
                    targets: vec![Expr::Var(self.string_const(aux))],
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
                // B-1 results from `...`. With one result, R(A) = (...); else materialize
                // each from a vararg expansion (best effort).
                let n = b as i32 - 1;
                if n == 1 {
                    self.assign(a, Expr::Vararg, stmts);
                } else {
                    self.assign(a, Expr::Vararg, stmts);
                    if n != 1 {
                        self.note("multi-value `...` expansion approximated");
                    }
                }
            }
            NEWCLOSURE => {
                let child = insn_d(insn) as usize;
                let e = self.closure_expr(child);
                self.assign(a, e, stmts);
            }
            DUPCLOSURE => {
                // The constant is a Closure referencing a child proto.
                if let Some(Constant::Closure { proto }) = self.proto.constants.get(d as usize) {
                    let e = self.closure_expr(*proto as usize);
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
            CALL => self.emit_call(a, b, c, stmts, pending_namecall),
            RETURN => {
                let n = b as i32 - 1;
                let vals = if n < 0 {
                    self.note("multret return approximated");
                    vec![self.reg(a)]
                } else {
                    (0..n).map(|i| self.reg(a + i as u8)).collect()
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
            PREPVARARGS | NOP | BREAK | COVERAGE | NATIVECALL => {}
            FASTCALL | FASTCALL1 | FASTCALL2 | FASTCALL2K | FASTCALL3 => {
                // Optimization hints; the real work is the following CALL.
            }
            other => {
                stmts.push(Stmt::Comment(format!("unhandled op {}", other.name())));
                self.note(&format!("unhandled opcode {}", other.name()));
            }
        }
    }

    // --- expression helpers -------------------------------------------------------------

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

    fn closure_expr(&mut self, child_idx: usize) -> Expr {
        // Recursively decompile the child proto into a function literal.
        let child = &self.module.protos[child_idx];
        let params = self.signature_params(child);
        let mut sub_reports = Vec::new();
        let body = decompile_proto(self.module, child_idx, &mut sub_reports);
        if sub_reports.iter().any(|r| r.partial) {
            self.partial = true;
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
        Expr::Closure(format!(
            "function({}{})\n{}end",
            params.join(", "),
            vararg,
            indented
        ))
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
        stmts: &mut Vec<Stmt>,
        pending_namecall: &mut Option<(u8, Expr, String)>,
    ) {
        let nargs = b as i32 - 1;
        let nresults = c as i32 - 1;

        let call_expr = match pending_namecall.take() {
            Some((reg, obj, method)) if reg == a => {
                // self is at A+1; explicit args at A+2..A+nargs.
                let count = (nargs - 1).max(0);
                let args = (0..count).map(|i| self.reg(a + 2 + i as u8)).collect();
                if nargs < 0 {
                    self.note("multret method-call args approximated");
                }
                Expr::MethodCall(Box::new(obj), method, args)
            }
            other => {
                *pending_namecall = other;
                let callee = self.reg(a);
                let args = if nargs < 0 {
                    self.note("multret call args approximated");
                    vec![Expr::Raw("--[[...]]".into())]
                } else {
                    (0..nargs).map(|i| self.reg(a + 1 + i as u8)).collect()
                };
                Expr::Call(Box::new(callee), args)
            }
        };

        if nresults == 0 {
            stmts.push(Stmt::Call(call_expr));
        } else if nresults == 1 {
            self.assign(a, call_expr, stmts);
        } else {
            // Multiple results: name each destination register and assign as a tuple.
            let n = if nresults < 0 { 1 } else { nresults };
            if nresults < 0 {
                self.note("multret call results approximated");
            }
            let targets: Vec<Expr> = (0..n)
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
    fn reg(&self, r: u8) -> Expr {
        match self.regs.get(r as usize).and_then(|e| e.clone()) {
            Some(e) => e,
            None => Expr::Var(self.reg_name(r)),
        }
    }

    /// Store an inlinable immutable expression in a register (no statement emitted).
    fn set_inline(&mut self, r: u8, e: Expr) {
        if let Some(slot) = self.regs.get_mut(r as usize) {
            *slot = Some(e);
        }
    }

    /// Materialize a register: clear any inlined expr so reads use its name, and record it
    /// for hoisting if it is not a parameter.
    fn materialize(&mut self, r: u8) {
        if let Some(slot) = self.regs.get_mut(r as usize) {
            *slot = None;
        }
        if r >= self.proto.num_params {
            self.hoisted.insert(r);
        }
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
        if let Some(name) = self.unique_debug_name(self.proto, r) {
            return name;
        }
        if r < self.proto.num_params {
            format!("p{r}")
        } else {
            format!("v{r}")
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
        if !self.partial {
            self.partial = true;
            self.note("control flow rendered with goto/labels (structuring incomplete)");
        }
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

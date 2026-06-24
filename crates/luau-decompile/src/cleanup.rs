//! AST cleanup passes that restore readability after the always-materialize emission.
//!
//! Two passes, both designed to be *sound* — they never change observable behavior:
//!  * `single_use_inline`: a local assigned once and read once, whose value is pure and
//!    whose inputs are not disturbed between definition and use, is inlined into that use.
//!  * `dead_store_elim`: a local that is never read is dropped (or, if its value is a call,
//!    reduced to a bare call so the side effect is preserved).
//!
//! Both consult global use/def counts and only act on the conservative cases. The pitfalls
//! the synthesized catalog warned about (reordering effects, moving a read past a write to
//! its inputs, touching captured/escaping registers) are all excluded here.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::ast::{Expr, Stmt, TableField};
use crate::naming::is_pure;

/// Names that are assigned (as a sole bare-Var target) somewhere in the tree, in first-
/// appearance order, excluding `exclude` (parameters). Used to build the hoisted `local`
/// declaration after cleanups have removed some assignments.
pub fn assigned_locals(root: &[Stmt], exclude: &BTreeSet<String>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    fn walk(
        stmts: &[Stmt],
        exclude: &BTreeSet<String>,
        seen: &mut BTreeSet<String>,
        order: &mut Vec<String>,
    ) {
        for s in stmts {
            // Every bare-Var assignment target needs a declaration, including the multiple
            // targets of a tuple assignment (`a, b = pcall(f)`) — otherwise they leak as
            // globals.
            if let Stmt::Assign { targets, .. } = s {
                for t in targets {
                    if let Expr::Var(name) = t {
                        if !exclude.contains(name) && seen.insert(name.clone()) {
                            order.push(name.clone());
                        }
                    }
                }
            }
            for_each_block(s, |b| walk(b, exclude, seen, order));
        }
    }
    walk(root, exclude, &mut seen, &mut order);
    order
}

/// Inline single-use pure temporaries to fixpoint. `protected` names are never inlined
/// (e.g. registers captured by closures).
pub fn single_use_inline(root: &mut Vec<Stmt>, protected: &BTreeSet<String>) {
    loop {
        let uses = count_uses(root);
        let defs = count_defs(root);
        if !inline_in_block(root, &uses, &defs, protected) {
            break;
        }
    }
}

/// Remove dead pure stores; reduce dead call-stores to bare calls. `protected` names are
/// never removed.
pub fn dead_store_elim(root: &mut Vec<Stmt>, protected: &BTreeSet<String>) {
    loop {
        let uses = count_uses(root);
        if !dead_in_block(root, &uses, protected) {
            break;
        }
    }
}

/// Drop statements after a `return`/`break` in each block. A flush of the inline cache can
/// append assignments after a terminator; that code is both unreachable and (for `return`)
/// not even valid Luau, so it must go.
pub fn drop_unreachable(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, drop_unreachable);
    }
    if let Some(idx) = root
        .iter()
        .position(|s| matches!(s, Stmt::Return(_) | Stmt::Break))
    {
        root.truncate(idx + 1);
    }
}

/// Recover the `z = COND and X or Y` short-circuit ternary from the diamond the compiler
/// emits (a conditional write to one register on both paths, rejoining at a label):
///
/// ```text
/// if COND then z = X; if z then goto L end end
/// z = Y
/// ::L::
/// ```
///
/// becomes `z = COND and X or Y`. This is purely structural recovery of the and/or idiom.
pub fn recover_and_or(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_and_or);
    }
    let mut i = 0;
    while i + 2 < root.len() {
        if let Some(rewritten) = match_and_or(&root[i], &root[i + 1], &root[i + 2]) {
            root[i] = rewritten;
            root.remove(i + 2);
            root.remove(i + 1);
            // Re-check at i so `a and b and c or d` style chains collapse.
            continue;
        }
        i += 1;
    }
}

fn match_and_or(s0: &Stmt, s1: &Stmt, s2: &Stmt) -> Option<Stmt> {
    // s0: if COND then z = X; if z then goto L end end   (no else)
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = s0
    else {
        return None;
    };
    if !else_body.is_empty() || then_body.len() != 2 {
        return None;
    }
    let (z, x) = match &then_body[0] {
        Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            match &targets[0] {
                Expr::Var(z) => (z.clone(), values[0].clone()),
                _ => return None,
            }
        }
        _ => return None,
    };
    let label = match &then_body[1] {
        Stmt::If {
            cond: Expr::Var(zc),
            then_body: gt,
            else_body: ge,
        } if *zc == z && ge.is_empty() && gt.len() == 1 => match &gt[0] {
            Stmt::Goto(l) => l.clone(),
            _ => return None,
        },
        _ => return None,
    };
    // s1: z = Y
    let y = match s1 {
        Stmt::Assign { targets, values }
            if targets.len() == 1
                && values.len() == 1
                && matches!(&targets[0], Expr::Var(z2) if *z2 == z) =>
        {
            values[0].clone()
        }
        _ => return None,
    };
    // s2: ::L::
    match s2 {
        Stmt::Label(l) if *l == label => {}
        _ => return None,
    }

    let expr = Expr::Binary(
        "or",
        Box::new(Expr::Binary("and", Box::new(cond.clone()), Box::new(x))),
        Box::new(y),
    );
    Some(Stmt::Assign {
        targets: vec![Expr::Var(z)],
        values: vec![expr],
    })
}

// --- inlining --------------------------------------------------------------------------

fn inline_in_block(
    block: &mut Vec<Stmt>,
    uses: &BTreeMap<String, usize>,
    defs: &BTreeMap<String, usize>,
    protected: &BTreeSet<String>,
) -> bool {
    // Recurse into nested blocks first.
    for s in block.iter_mut() {
        let mut changed = false;
        for_each_block_mut(s, |b| {
            if !changed {
                changed = inline_in_block(b, uses, defs, protected);
            }
        });
        if changed {
            return true;
        }
    }

    for i in 0..block.len() {
        let Some((name, val)) = sole_var_assign(&block[i]) else {
            continue;
        };
        if protected.contains(&name) {
            continue;
        }
        if uses.get(&name).copied().unwrap_or(0) != 1 || defs.get(&name).copied().unwrap_or(0) != 1
        {
            continue;
        }
        if !is_pure(&val) {
            continue; // only pure values may move
        }
        let inputs = reads_of_expr(&val);
        let has_table_read = reads_table(&val);

        // Find the unique use in this same block, after i.
        let Some(j) = (i + 1..block.len()).find(|&k| stmt_reads_var(&block[k], &name)) else {
            continue;
        };

        // Interference check on the statements strictly between def and use.
        let mut safe = true;
        for stmt in &block[i + 1..j] {
            if matches!(stmt, Stmt::Label(_) | Stmt::Goto(_)) {
                safe = false;
                break;
            }
            if !writes_of_stmt(stmt).is_disjoint(&inputs) {
                safe = false;
                break;
            }
            if has_table_read && stmt_effectful(stmt) {
                safe = false;
                break;
            }
        }
        if !safe {
            continue;
        }

        // Inline: replace the single occurrence in block[j], drop the def.
        let mut v = Some(val);
        replace_first_var(&mut block[j], &name, &mut v);
        block.remove(i);
        return true;
    }
    false
}

// --- dead store elimination ------------------------------------------------------------

fn dead_in_block(
    block: &mut Vec<Stmt>,
    uses: &BTreeMap<String, usize>,
    protected: &BTreeSet<String>,
) -> bool {
    for s in block.iter_mut() {
        let mut changed = false;
        for_each_block_mut(s, |b| {
            if !changed {
                changed = dead_in_block(b, uses, protected);
            }
        });
        if changed {
            return true;
        }
    }

    for i in 0..block.len() {
        let Some((name, val)) = sole_var_assign(&block[i]) else {
            continue;
        };
        if protected.contains(&name) {
            continue;
        }
        // The local is never read anywhere: its stores are dead regardless of how many there
        // are. (A register reused for several short-lived unread values produces several.)
        if uses.get(&name).copied().unwrap_or(0) != 0 {
            continue;
        }
        if is_pure(&val) {
            block.remove(i); // pure & unused -> gone
        } else {
            block[i] = Stmt::Call(val); // keep the side effect, drop the binding
        }
        return true;
    }
    false
}

// --- counting --------------------------------------------------------------------------

fn count_uses(root: &[Stmt]) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for s in root {
        count_uses_stmt(s, &mut counts);
    }
    counts
}

fn count_uses_stmt(s: &Stmt, counts: &mut BTreeMap<String, usize>) {
    match s {
        Stmt::Local { values, .. } => values.iter().for_each(|e| add_reads(e, counts)),
        Stmt::Assign { targets, values } => {
            for t in targets {
                match t {
                    // A sole Var target is a write, not a read.
                    Expr::Var(_) => {}
                    // `t.x = v` / `t[k] = v` read the base (and key).
                    other => add_reads(other, counts),
                }
            }
            values.iter().for_each(|e| add_reads(e, counts));
        }
        Stmt::Call(e) => add_reads(e, counts),
        Stmt::Return(es) => es.iter().for_each(|e| add_reads(e, counts)),
        Stmt::If { cond, .. } => add_reads(cond, counts),
        Stmt::While { cond, .. } => add_reads(cond, counts),
        Stmt::Repeat { cond, .. } => add_reads(cond, counts),
        Stmt::NumericFor {
            start, limit, step, ..
        } => {
            add_reads(start, counts);
            add_reads(limit, counts);
            if let Some(s) = step {
                add_reads(s, counts);
            }
        }
        Stmt::GenericFor { exprs, .. } => exprs.iter().for_each(|e| add_reads(e, counts)),
        Stmt::Break | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => {}
    }
    for_each_block(s, |b| {
        for st in b {
            count_uses_stmt(st, counts);
        }
    });
}

fn count_defs(root: &[Stmt]) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    fn walk(stmts: &[Stmt], counts: &mut BTreeMap<String, usize>) {
        for s in stmts {
            if let Some((name, _)) = sole_var_assign(s) {
                *counts.entry(name).or_insert(0) += 1;
            }
            for_each_block(s, |b| walk(b, counts));
        }
    }
    walk(root, &mut counts);
    counts
}

fn add_reads(e: &Expr, counts: &mut BTreeMap<String, usize>) {
    count_occurrences(e, counts);
}

/// Count each Var occurrence (multiplicity matters for "used once").
fn count_occurrences(e: &Expr, counts: &mut BTreeMap<String, usize>) {
    match e {
        Expr::Var(name) if !name.contains('.') => {
            *counts.entry(name.clone()).or_insert(0) += 1;
        }
        Expr::Var(_) => {}
        Expr::Index(t, k) => {
            count_occurrences(t, counts);
            count_occurrences(k, counts);
        }
        Expr::Field(t, _) => count_occurrences(t, counts),
        Expr::Call(f, args) => {
            count_occurrences(f, counts);
            args.iter().for_each(|a| count_occurrences(a, counts));
        }
        Expr::MethodCall(o, _, args) => {
            count_occurrences(o, counts);
            args.iter().for_each(|a| count_occurrences(a, counts));
        }
        Expr::Unary(_, a) => count_occurrences(a, counts),
        Expr::Binary(_, a, b) => {
            count_occurrences(a, counts);
            count_occurrences(b, counts);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => count_occurrences(e, counts),
                    TableField::Keyed(k, v) => {
                        count_occurrences(k, counts);
                        count_occurrences(v, counts);
                    }
                }
            }
        }
        _ => {}
    }
}

fn reads_of_expr(e: &Expr) -> BTreeSet<String> {
    let mut m = BTreeMap::new();
    count_occurrences(e, &mut m);
    m.into_keys().collect()
}

// --- predicates & helpers --------------------------------------------------------------

/// If `s` is `name = value` with a single bare-Var target, return `(name, value)`.
fn sole_var_assign(s: &Stmt) -> Option<(String, Expr)> {
    if let Stmt::Assign { targets, values } = s {
        if targets.len() == 1 && values.len() == 1 {
            if let Expr::Var(name) = &targets[0] {
                return Some((name.clone(), values[0].clone()));
            }
        }
    }
    None
}

fn stmt_reads_var(s: &Stmt, name: &str) -> bool {
    let mut counts = BTreeMap::new();
    count_uses_stmt(s, &mut counts);
    counts.get(name).copied().unwrap_or(0) > 0
}

/// All bare-Var names assigned by a statement, including inside nested blocks.
fn writes_of_stmt(s: &Stmt) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    fn walk(s: &Stmt, out: &mut BTreeSet<String>) {
        match s {
            Stmt::Assign { targets, .. } => {
                for t in targets {
                    if let Expr::Var(n) = t {
                        out.insert(n.clone());
                    }
                }
            }
            Stmt::Local { names, .. } => out.extend(names.iter().cloned()),
            Stmt::NumericFor { var, .. } => {
                out.insert(var.clone());
            }
            Stmt::GenericFor { vars, .. } => out.extend(vars.iter().cloned()),
            _ => {}
        }
        for_each_block(s, |b| {
            for st in b {
                walk(st, out);
            }
        });
    }
    walk(s, &mut out);
    out
}

/// Whether a statement performs an observable side effect (a call, or a write through a
/// table — `t.x = v` / `t[k] = v`).
fn stmt_effectful(s: &Stmt) -> bool {
    match s {
        Stmt::Call(_) => true,
        Stmt::Assign { targets, values } => {
            targets
                .iter()
                .any(|t| !matches!(t, Expr::Var(_)) || expr_effectful(t))
                || values.iter().any(expr_effectful)
        }
        Stmt::Return(es) => es.iter().any(expr_effectful),
        // A nested control-flow block may do anything; treat it as effectful.
        Stmt::If { .. }
        | Stmt::While { .. }
        | Stmt::Repeat { .. }
        | Stmt::NumericFor { .. }
        | Stmt::GenericFor { .. } => true,
        _ => false,
    }
}

fn expr_effectful(e: &Expr) -> bool {
    !is_pure(e)
}

fn reads_table(e: &Expr) -> bool {
    match e {
        Expr::Field(..) | Expr::Index(..) => true,
        Expr::Unary(_, a) => reads_table(a),
        Expr::Binary(_, a, b) => reads_table(a) || reads_table(b),
        _ => false,
    }
}

/// Replace the first `Var(name)` read inside a statement with `repl` (taken once).
fn replace_first_var(s: &mut Stmt, name: &str, repl: &mut Option<Expr>) {
    match s {
        Stmt::Local { values, .. } => values
            .iter_mut()
            .for_each(|e| replace_in_expr(e, name, repl)),
        Stmt::Assign { targets, values } => {
            for t in targets.iter_mut() {
                if !matches!(t, Expr::Var(_)) {
                    replace_in_expr(t, name, repl);
                }
            }
            values
                .iter_mut()
                .for_each(|e| replace_in_expr(e, name, repl));
        }
        Stmt::Call(e) => replace_in_expr(e, name, repl),
        Stmt::Return(es) => es.iter_mut().for_each(|e| replace_in_expr(e, name, repl)),
        Stmt::If { cond, .. } => replace_in_expr(cond, name, repl),
        Stmt::While { cond, .. } => replace_in_expr(cond, name, repl),
        Stmt::Repeat { cond, .. } => replace_in_expr(cond, name, repl),
        Stmt::NumericFor {
            start, limit, step, ..
        } => {
            replace_in_expr(start, name, repl);
            replace_in_expr(limit, name, repl);
            if let Some(s) = step {
                replace_in_expr(s, name, repl);
            }
        }
        Stmt::GenericFor { exprs, .. } => exprs
            .iter_mut()
            .for_each(|e| replace_in_expr(e, name, repl)),
        _ => {}
    }
}

fn replace_in_expr(e: &mut Expr, name: &str, repl: &mut Option<Expr>) {
    if repl.is_none() {
        return;
    }
    match e {
        Expr::Var(n) if n == name => {
            if let Some(v) = repl.take() {
                *e = v;
            }
        }
        Expr::Index(t, k) => {
            replace_in_expr(t, name, repl);
            replace_in_expr(k, name, repl);
        }
        Expr::Field(t, _) => replace_in_expr(t, name, repl),
        Expr::Call(f, args) => {
            replace_in_expr(f, name, repl);
            args.iter_mut().for_each(|a| replace_in_expr(a, name, repl));
        }
        Expr::MethodCall(o, _, args) => {
            replace_in_expr(o, name, repl);
            args.iter_mut().for_each(|a| replace_in_expr(a, name, repl));
        }
        Expr::Unary(_, a) => replace_in_expr(a, name, repl),
        Expr::Binary(_, a, b) => {
            replace_in_expr(a, name, repl);
            replace_in_expr(b, name, repl);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => replace_in_expr(e, name, repl),
                    TableField::Keyed(k, v) => {
                        replace_in_expr(k, name, repl);
                        replace_in_expr(v, name, repl);
                    }
                }
            }
        }
        _ => {}
    }
}

// --- block traversal -------------------------------------------------------------------

fn for_each_block(s: &Stmt, mut f: impl FnMut(&[Stmt])) {
    match s {
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            f(then_body);
            f(else_body);
        }
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => f(body),
        _ => {}
    }
}

fn for_each_block_mut(s: &mut Stmt, mut f: impl FnMut(&mut Vec<Stmt>)) {
    match s {
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            f(then_body);
            f(else_body);
        }
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => f(body),
        _ => {}
    }
}

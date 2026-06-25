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
    let mut declared = exclude.clone();
    for stmt in root {
        if let Stmt::Local { names, .. } = stmt {
            declared.extend(names.iter().cloned());
        }
    }

    fn walk(
        stmts: &[Stmt],
        declared: &BTreeSet<String>,
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
                        if !declared.contains(name) && seen.insert(name.clone()) {
                            order.push(name.clone());
                        }
                    }
                }
            }
            for_each_block(s, |b| walk(b, declared, seen, order));
        }
    }
    walk(root, &declared, &mut seen, &mut order);
    order
}

/// Promote first top-level assignments into local initializers when the variable is assigned
/// exactly once in the function. This removes synthetic "local x; x = ..." boilerplate
/// without changing scope across branches/loops.
pub fn promote_top_level_initializers(root: &mut [Stmt], exclude: &BTreeSet<String>) {
    let mut prior_reads = BTreeSet::new();
    let mut prior_writes = BTreeSet::new();

    for stmt in root.iter_mut() {
        let replacement = match stmt {
            Stmt::Assign { targets, values } if !targets.is_empty() => {
                let mut names = Vec::new();
                for target in targets.iter() {
                    let Expr::Var(name) = target else {
                        names.clear();
                        break;
                    };
                    if exclude.contains(name)
                        || prior_reads.contains(name)
                        || prior_writes.contains(name)
                    {
                        names.clear();
                        break;
                    }
                    names.push(name.clone());
                }

                let value_reads = values.iter().fold(BTreeSet::new(), |mut acc, value| {
                    acc.extend(reads_of_expr(value));
                    acc
                });
                if names.is_empty() || names.iter().any(|name| value_reads.contains(name)) {
                    None
                } else {
                    Some(Stmt::Local {
                        names,
                        values: values.clone(),
                    })
                }
            }
            _ => None,
        };

        if let Some(local) = replacement {
            *stmt = local;
        }

        let mut reads = BTreeMap::new();
        count_uses_stmt(stmt, &mut reads);
        prior_reads.extend(reads.into_keys());
        prior_writes.extend(writes_of_stmt(stmt));
    }
}

/// Inline single-use pure temporaries to fixpoint. `protected` names are never inlined
/// (e.g. registers captured by closures or globals).
pub fn single_use_inline(root: &mut Vec<Stmt>, protected: &BTreeSet<String>) {
    while inline_in_block(root, protected) {}
}

/// Remove dead pure stores; reduce dead call-stores to bare calls. `protected` names are
/// never removed.
pub fn dead_store_elim(root: &mut Vec<Stmt>, protected: &BTreeSet<String>) {
    loop {
        let uses = count_uses(root);
        if !dead_in_block(root, &uses, protected) && !dead_overwritten_in_block(root, protected) {
            break;
        }
    }
}

/// Total statement count across the whole tree (used to detect cleanup fixpoint).
pub fn count_stmts(root: &[Stmt]) -> usize {
    let mut n = 0;
    for s in root {
        n += 1;
        for_each_block(s, |b| n += count_stmts(b));
    }
    n
}

/// Fold `t = {}; t[1]=a; t[2]=b; t.k=v` (a NEWTABLE/DUPTABLE followed by its consecutive
/// SETLIST/SETTABLEKS fills) into a table literal `t = {a, b, k = v}`. Only consecutive fills
/// of `t` whose key/value don't reference `t` are absorbed, so evaluation order and any later
/// mutation of `t` are preserved. Combined with single-use inlining, nested tables collapse
/// into nested literals.
pub fn fold_table_literals(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, fold_table_literals);
    }
    let mut i = 0;
    while i < root.len() {
        let Some((t, mut fields)) = table_init(&root[i]) else {
            i += 1;
            continue;
        };
        let mut array_next = 1 + fields
            .iter()
            .filter(|f| matches!(f, TableField::Item(_)))
            .count();
        let mut j = i + 1;
        while j < root.len() {
            match table_fill_field(&root[j], &t, &mut array_next) {
                Some(field) => {
                    fields.push(field);
                    j += 1;
                }
                None => break,
            }
        }
        if j > i + 1 {
            replace_table_init(&mut root[i], fields);
            root.drain(i + 1..j);
        }
        i += 1;
    }
}

fn table_init(s: &Stmt) -> Option<(String, Vec<TableField>)> {
    match s {
        Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            match (&targets[0], &values[0]) {
                (Expr::Var(t), Expr::Table(base)) => Some((t.clone(), base.clone())),
                _ => None,
            }
        }
        Stmt::Local { names, values } if names.len() == 1 && values.len() == 1 => {
            match &values[0] {
                Expr::Table(base) => Some((names[0].clone(), base.clone())),
                _ => None,
            }
        }
        _ => None,
    }
}

fn replace_table_init(s: &mut Stmt, fields: Vec<TableField>) {
    match s {
        Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            values[0] = Expr::Table(fields);
        }
        Stmt::Local { names, values } if names.len() == 1 && values.len() == 1 => {
            values[0] = Expr::Table(fields);
        }
        _ => {}
    }
}

/// If `s` is a fill of table `t` (`t[k] = v` or `t.k = v`) safe to absorb into a literal,
/// return the corresponding field. `array_next` tracks the next positional array index.
fn table_fill_field(s: &Stmt, t: &str, array_next: &mut usize) -> Option<TableField> {
    let Stmt::Assign { targets, values } = s else {
        return None;
    };
    if targets.len() != 1 || values.len() != 1 {
        return None;
    }
    let value = &values[0];
    if reads_of_expr(value).contains(t) {
        return None; // value reads t — the literal can't capture it
    }
    let is_t = |e: &Expr| matches!(e, Expr::Var(n) if n == t);
    match &targets[0] {
        Expr::Field(base, name) if is_t(base) => {
            Some(TableField::Named(name.clone(), value.clone()))
        }
        Expr::Index(base, key) if is_t(base) => {
            if reads_of_expr(key).contains(t) {
                return None;
            }
            if let Expr::Num(n) = key.as_ref() {
                if *n == array_next.to_string() {
                    *array_next += 1;
                    return Some(TableField::Item(value.clone()));
                }
            }
            Some(TableField::Keyed((**key).clone(), value.clone()))
        }
        _ => None,
    }
}

/// Drop statements after a `return`/`break`/`continue`/`goto` in each block. A flush of the inline
/// cache can append assignments after a terminator; that code is both unreachable and (for
/// `return`) not even valid Luau, so it must go. Statements at or after a `::label::` are kept,
/// however — they may be reached by a `goto` that jumps over the terminator (a guard like
/// `if not (a and b) then return end <body>` puts <body> behind a label after the return), and
/// dropping them would silently delete reachable code.
pub fn drop_unreachable(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, drop_unreachable);
    }
    let mut i = 0;
    while i < root.len() {
        if matches!(
            root[i],
            Stmt::Return(_) | Stmt::Break | Stmt::Continue | Stmt::Goto(_)
        ) {
            let mut j = i + 1;
            while j < root.len() && !matches!(root[j], Stmt::Label(_)) {
                j += 1;
            }
            root.drain(i + 1..j);
        }
        i += 1;
    }
}

/// A final bare `return` at the end of a function is equivalent to falling off the end of
/// the function. Drop only the current function body's trailing empty return; do not recurse
/// into nested control-flow blocks, where a branch-local `return` may guard outer code.
pub fn drop_trailing_empty_return(root: &mut Vec<Stmt>) {
    if matches!(root.last(), Some(Stmt::Return(values)) if values.is_empty()) {
        root.pop();
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

/// Recover simple forward gotos used only to skip a block:
///
/// ```text
/// if COND then goto L end
/// <body>
/// ::L::
/// ```
///
/// becomes `if not COND then <body> end`. Nested guard chains are folded into a combined
/// condition when the target label has no other incoming gotos.
pub fn recover_if_skip_gotos(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_if_skip_gotos);
    }
    while recover_if_skip_once(root) {}
}

fn recover_if_skip_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let Some((cond, label)) = conditional_goto_expr(&root[i], None) else {
            continue;
        };
        if count_gotos_named(root, &label) != 1 {
            continue;
        }
        let Some(label_idx) = root[i + 1..]
            .iter()
            .position(|s| matches!(s, Stmt::Label(name) if name == &label))
            .map(|offset| i + 1 + offset)
        else {
            continue;
        };
        if contains_label_or_goto(&root[i + 1..label_idx]) {
            continue;
        }
        if !direct_local_scope_safe(&root[i + 1..label_idx], &root[label_idx + 1..]) {
            continue;
        }

        if label_idx == i + 1 {
            root.drain(i..=label_idx);
            return true;
        }

        let skipped_body = root[i + 1..label_idx].to_vec();
        root[i] = Stmt::If {
            cond: negate_condition(cond),
            then_body: skipped_body,
            else_body: Vec::new(),
        };
        root.drain(i + 1..=label_idx);
        return true;
    }
    false
}

/// Recover loop-body guard diamonds where one path jumps to a trailing error/fallback block:
///
/// ```text
/// if INVALID then goto L end
/// <accepted body>
/// continue
/// ::L::
/// <fallback body>
/// ```
///
/// becomes `if not INVALID then <accepted body> else <fallback body> end`. The rewrite only
/// fires when the accepted path terminates with `continue`, so all remaining statements in
/// the current loop block are known to belong to the fallback path.
pub fn recover_guard_else_gotos(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_guard_else_gotos);
    }
    while recover_guard_else_once(root) {}
}

fn recover_guard_else_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let labels = goto_names_in_stmt(&root[i]);
        for label in labels {
            let guard_gotos = count_gotos_named_stmt(&root[i], &label);
            if guard_gotos == 0 || count_gotos_named(root, &label) != guard_gotos {
                continue;
            }
            let Some((invalid_cond, _)) = conditional_goto_expr(&root[i], Some(&label)) else {
                continue;
            };
            let Some(label_idx) = root[i + 1..]
                .iter()
                .position(|s| matches!(s, Stmt::Label(name) if name == &label))
                .map(|offset| i + 1 + offset)
            else {
                continue;
            };
            if label_idx <= i + 1 || !matches!(root[label_idx - 1], Stmt::Continue) {
                continue;
            }
            if contains_label_or_goto(&root[i + 1..label_idx - 1]) {
                continue;
            }
            if !direct_local_scope_safe(&root[i + 1..label_idx - 1], &root[label_idx + 1..]) {
                continue;
            }

            let then_body = root[i + 1..label_idx - 1].to_vec();
            let else_body = root[label_idx + 1..].to_vec();
            root[i] = Stmt::If {
                cond: negate_condition(invalid_cond),
                then_body,
                else_body,
            };
            root.truncate(i + 1);
            return true;
        }
    }
    false
}

/// Recover a validation branch that jumps into a labeled `if` body:
///
/// ```text
/// if ACCEPT_A then goto L end
/// if ACCEPT_B then
///     ::L::
///     <accepted body>
/// end
/// ```
///
/// becomes `if ACCEPT_A or ACCEPT_B then <accepted body> end`. This is common after the
/// reducing passes inline temporaries like `v = typeof(x)` back into the guard tests.
pub fn recover_goto_into_if_gates(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_goto_into_if_gates);
    }
    while recover_goto_into_if_gate_once(root) {}
}

fn recover_goto_into_if_gate_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        let Some((goto_cond, label)) = conditional_goto_expr(&root[i], None) else {
            i += 1;
            continue;
        };
        let guard_gotos = count_gotos_named_stmt(&root[i], &label);
        if guard_gotos == 0 || count_gotos_named(root, &label) != guard_gotos {
            i += 1;
            continue;
        }

        let Stmt::If {
            cond: target_cond,
            then_body,
            else_body,
        } = &root[i + 1]
        else {
            i += 1;
            continue;
        };
        if !else_body.is_empty()
            || !matches!(then_body.first(), Some(Stmt::Label(name)) if name == &label)
            || contains_label_or_goto(&then_body[1..])
        {
            i += 1;
            continue;
        }

        let accepted_body = then_body[1..].to_vec();
        root[i + 1] = Stmt::If {
            cond: Expr::Binary("or", Box::new(goto_cond), Box::new(target_cond.clone())),
            then_body: accepted_body,
            else_body: Vec::new(),
        };
        root.remove(i);
        return true;
    }
    false
}

fn conditional_goto_expr(stmt: &Stmt, required_label: Option<&str>) -> Option<(Expr, String)> {
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = stmt
    else {
        return None;
    };
    if !else_body.is_empty() {
        return None;
    }
    let (body_cond, label) = guard_body_goto_expr(then_body, required_label)?;
    let cond = if matches!(body_cond, Expr::Bool(true)) {
        cond.clone()
    } else {
        Expr::Binary("and", Box::new(cond.clone()), Box::new(body_cond))
    };
    Some((cond, label))
}

fn guard_body_goto_expr(stmts: &[Stmt], required_label: Option<&str>) -> Option<(Expr, String)> {
    let mut conds = Vec::new();
    let mut target = required_label.map(str::to_string);
    for stmt in stmts {
        let (cond, label) = match stmt {
            Stmt::Goto(label) => (Expr::Bool(true), label.clone()),
            _ => conditional_goto_expr(stmt, required_label)?,
        };
        if let Some(required) = required_label {
            if label != required {
                return None;
            }
        }
        match &target {
            Some(existing) if existing != &label => return None,
            None => target = Some(label.clone()),
            _ => {}
        }
        conds.push(cond);
    }
    let label = target?;
    Some((or_all(conds)?, label))
}

fn or_all(mut conds: Vec<Expr>) -> Option<Expr> {
    let first = conds.pop()?;
    Some(conds.into_iter().rev().fold(first, |acc, cond| {
        Expr::Binary("or", Box::new(cond), Box::new(acc))
    }))
}

fn negate_condition(e: Expr) -> Expr {
    match e {
        Expr::Binary("==", a, b) => Expr::Binary("~=", a, b),
        Expr::Binary("~=", a, b) => Expr::Binary("==", a, b),
        Expr::Binary("<", a, b) => Expr::Binary(">=", a, b),
        Expr::Binary("<=", a, b) => Expr::Binary(">", a, b),
        Expr::Binary(">", a, b) => Expr::Binary("<=", a, b),
        Expr::Binary(">=", a, b) => Expr::Binary("<", a, b),
        Expr::Binary("and", a, b) => Expr::Binary(
            "or",
            Box::new(negate_condition(*a)),
            Box::new(negate_condition(*b)),
        ),
        Expr::Binary("or", a, b) => Expr::Binary(
            "and",
            Box::new(negate_condition(*a)),
            Box::new(negate_condition(*b)),
        ),
        Expr::Unary("not ", inner) => *inner,
        other => Expr::Unary("not ", Box::new(other)),
    }
}

fn contains_label_or_goto(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Label(_) | Stmt::Goto(_) => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => contains_label_or_goto(then_body) || contains_label_or_goto(else_body),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => contains_label_or_goto(body),
        _ => false,
    })
}

fn direct_local_scope_safe(moved: &[Stmt], following: &[Stmt]) -> bool {
    let locals: BTreeSet<String> = moved
        .iter()
        .filter_map(|stmt| match stmt {
            Stmt::Local { names, .. } => Some(names.iter().cloned()),
            _ => None,
        })
        .flatten()
        .collect();
    locals.is_empty()
        || !following
            .iter()
            .any(|stmt| locals.iter().any(|name| stmt_reads_var(stmt, name)))
}

fn count_gotos_named(stmts: &[Stmt], label: &str) -> usize {
    stmts
        .iter()
        .map(|stmt| count_gotos_named_stmt(stmt, label))
        .sum()
}

fn count_gotos_named_stmt(stmt: &Stmt, label: &str) -> usize {
    match stmt {
        Stmt::Goto(name) if name == label => 1,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => count_gotos_named(then_body, label) + count_gotos_named(else_body, label),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => count_gotos_named(body, label),
        _ => 0,
    }
}

fn goto_names_in_stmt(stmt: &Stmt) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_goto_names(stmt, &mut names);
    names
}

fn collect_goto_names(stmt: &Stmt, names: &mut BTreeSet<String>) {
    match stmt {
        Stmt::Goto(name) => {
            names.insert(name.clone());
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            for stmt in then_body.iter().chain(else_body.iter()) {
                collect_goto_names(stmt, names);
            }
        }
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => {
            for stmt in body {
                collect_goto_names(stmt, names);
            }
        }
        _ => {}
    }
}

// --- inlining --------------------------------------------------------------------------

fn inline_in_block(block: &mut Vec<Stmt>, protected: &BTreeSet<String>) -> bool {
    // Recurse into nested blocks first.
    for s in block.iter_mut() {
        let mut changed = false;
        for_each_block_mut(s, |b| {
            if !changed {
                changed = inline_in_block(b, protected);
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
        if reads_of_expr(&val).contains(&name) {
            continue; // self-referential definition (a refinement); leave it
        }
        // Pure values can move anywhere (interference-checked). An impure value (a call) may
        // only be inlined when the use evaluates it first (the temp is the head/receiver) and
        // nothing effectful sits between — then no side effect is reordered.
        let impure = !is_pure(&val);

        // The definition's value is live until `name` is next written. Work only within a
        // straight-line window up to that point so we can see every use of THIS value.
        let next_def = ((i + 1)..block.len())
            .find(|&k| writes_of_stmt(&block[k]).contains(&name))
            .unwrap_or(block.len());
        let reads: Vec<(usize, usize)> = ((i + 1)..next_def)
            .filter_map(|k| {
                let count = stmt_read_count(&block[k], &name);
                (count > 0).then_some((k, count))
            })
            .collect();
        if reads.is_empty() {
            continue;
        }
        let total_reads: usize = reads.iter().map(|(_, count)| *count).sum();
        let (j, reads_in_stmt) = reads[0];
        let replaceable_reads = stmt_replaceable_read_count(&block[j], &name);
        if replaceable_reads == 0 {
            continue;
        }
        if block[i + 1..j].iter().any(is_control_flow) {
            continue; // a branch/loop before the use may hide path-specific behavior
        }

        // Interference check on the statements strictly between def and use.
        let inputs = reads_of_expr(&val);
        let needs_no_effects = reads_table(&val) || impure;
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
            if needs_no_effects && stmt_effectful(stmt) {
                safe = false;
                break;
            }
        }
        // An impure value may only be inlined where it is evaluated first (head/receiver).
        if impure && stmt_head(&block[j]) != Some(name.as_str()) {
            safe = false;
        }
        if !safe {
            continue;
        }

        // If this logical value has exactly one read and the next definition doesn't also
        // read it (`x = x.foo`), the materializing assignment can disappear entirely.
        let can_remove_def = total_reads == 1
            && !(next_def < block.len() && stmt_reads_var(&block[next_def], &name));
        if stmt_reads_var_in_assignment_target(&block[j], &name) {
            continue;
        }
        if !can_remove_def && !is_duplicable_leaf(&val) {
            continue;
        }
        if !can_remove_def && (reads_in_stmt != 1 || replaceable_reads != 1) {
            continue; // don't partially inline `x` inside `x and x.y`
        }

        let mut v = Some(val);
        replace_first_var(&mut block[j], &name, &mut v);
        if can_remove_def {
            block.remove(i);
        }
        return true;
    }
    false
}

/// The variable read first when evaluating an expression (its receiver/leftmost operand),
/// if evaluation begins by reading a variable.
fn expr_head(e: &Expr) -> Option<&str> {
    match e {
        Expr::Var(n) => Some(n),
        Expr::Field(b, _) | Expr::Index(b, _) => expr_head(b),
        Expr::MethodCall(o, _, _) => expr_head(o),
        Expr::Call(c, _) => expr_head(c),
        Expr::Binary(_, a, _) => expr_head(a),
        Expr::Unary(_, a) => expr_head(a),
        _ => None,
    }
}

/// The variable a statement evaluates first, when that is a plain leading read (so an impure
/// value inlined there isn't reordered relative to the statement's other side effects).
fn stmt_head(s: &Stmt) -> Option<&str> {
    match s {
        Stmt::Call(e) => expr_head(e),
        Stmt::Return(vals) => vals.first().and_then(expr_head),
        Stmt::Local { values, .. } => values.first().and_then(expr_head),
        Stmt::Assign { targets, values } if matches!(targets.as_slice(), [Expr::Var(_)]) => {
            values.first().and_then(expr_head)
        }
        Stmt::If { cond, .. } => expr_head(cond),
        _ => None,
    }
}

fn is_control_flow(s: &Stmt) -> bool {
    matches!(
        s,
        Stmt::If { .. }
            | Stmt::While { .. }
            | Stmt::Repeat { .. }
            | Stmt::NumericFor { .. }
            | Stmt::GenericFor { .. }
            | Stmt::Label(_)
            | Stmt::Goto(_)
            | Stmt::Break
            | Stmt::Continue
    )
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

fn dead_overwritten_in_block(block: &mut Vec<Stmt>, protected: &BTreeSet<String>) -> bool {
    for s in block.iter_mut() {
        let mut changed = false;
        for_each_block_mut(s, |b| {
            if !changed {
                changed = dead_overwritten_in_block(b, protected);
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
        if protected.contains(&name) || !is_pure(&val) {
            continue;
        }
        let Some(next_def) =
            ((i + 1)..block.len()).find(|&k| directly_writes_var(&block[k], &name))
        else {
            continue;
        };
        if block[i + 1..next_def].iter().any(is_control_flow) {
            continue;
        }
        if block[i + 1..next_def]
            .iter()
            .any(|stmt| stmt_reads_var(stmt, &name))
        {
            continue;
        }
        if stmt_reads_var(&block[next_def], &name) {
            continue;
        }
        block.remove(i);
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
        Stmt::Break | Stmt::Continue | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => {}
    }
    for_each_block(s, |b| {
        for st in b {
            count_uses_stmt(st, counts);
        }
    });
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

/// If `s` is `name = value` or `local name = value` with a single bare name, return
/// `(name, value)`.
fn sole_var_assign(s: &Stmt) -> Option<(String, Expr)> {
    match s {
        Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            if let Expr::Var(name) = &targets[0] {
                Some((name.clone(), values[0].clone()))
            } else {
                None
            }
        }
        Stmt::Local { names, values } if names.len() == 1 && values.len() == 1 => {
            Some((names[0].clone(), values[0].clone()))
        }
        _ => None,
    }
}

fn stmt_reads_var(s: &Stmt, name: &str) -> bool {
    stmt_read_count(s, name) > 0
}

fn directly_writes_var(s: &Stmt, name: &str) -> bool {
    match s {
        Stmt::Assign { targets, .. } => targets
            .iter()
            .any(|target| matches!(target, Expr::Var(target_name) if target_name == name)),
        Stmt::Local { names, .. } => names.iter().any(|target_name| target_name == name),
        _ => false,
    }
}

fn stmt_reads_var_in_assignment_target(s: &Stmt, name: &str) -> bool {
    match s {
        Stmt::Assign { targets, .. } => targets.iter().any(|t| match t {
            Expr::Var(_) => false,
            other => reads_of_expr(other).contains(name),
        }),
        _ => false,
    }
}

fn stmt_read_count(s: &Stmt, name: &str) -> usize {
    let mut counts = BTreeMap::new();
    count_uses_stmt(s, &mut counts);
    counts.get(name).copied().unwrap_or(0)
}

fn stmt_replaceable_read_count(s: &Stmt, name: &str) -> usize {
    let mut counts = BTreeMap::new();
    match s {
        Stmt::Local { values, .. } => values.iter().for_each(|e| add_reads(e, &mut counts)),
        Stmt::Assign { targets, values } => {
            for t in targets {
                if !matches!(t, Expr::Var(_)) {
                    add_reads(t, &mut counts);
                }
            }
            values.iter().for_each(|e| add_reads(e, &mut counts));
        }
        Stmt::Call(e) => add_reads(e, &mut counts),
        Stmt::Return(es) => es.iter().for_each(|e| add_reads(e, &mut counts)),
        Stmt::If { cond, .. } => add_reads(cond, &mut counts),
        Stmt::NumericFor {
            start, limit, step, ..
        } => {
            add_reads(start, &mut counts);
            add_reads(limit, &mut counts);
            if let Some(step) = step {
                add_reads(step, &mut counts);
            }
        }
        Stmt::GenericFor { exprs, .. } => exprs.iter().for_each(|e| add_reads(e, &mut counts)),
        Stmt::While { .. }
        | Stmt::Repeat { .. }
        | Stmt::Break
        | Stmt::Continue
        | Stmt::Label(_)
        | Stmt::Goto(_)
        | Stmt::Comment(_) => {}
    }
    counts.get(name).copied().unwrap_or(0)
}

fn is_duplicable_leaf(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Nil
            | Expr::Bool(_)
            | Expr::Num(_)
            | Expr::Str(_)
            | Expr::Vector(_)
            | Expr::Var(_)
            | Expr::Vararg
    )
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::render_block;

    #[test]
    fn folds_fields_into_local_table_literals() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["object".into()],
                values: vec![Expr::Table(vec![TableField::Named(
                    "Camera".into(),
                    Expr::Var("camera".into()),
                )])],
            },
            Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("object".into())),
                    "Looped".into(),
                )],
                values: vec![Expr::Binary(
                    "or",
                    Box::new(Expr::Var("looped".into())),
                    Box::new(Expr::Bool(false)),
                )],
            },
            Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("object".into())),
                    "Speed".into(),
                )],
                values: vec![Expr::Binary(
                    "or",
                    Box::new(Expr::Var("speed".into())),
                    Box::new(Expr::Num("1".into())),
                )],
            },
            Stmt::Return(vec![Expr::Var("object".into())]),
        ];

        fold_table_literals(&mut stmts);

        assert_eq!(stmts.len(), 2);
        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("Camera = camera"), "{rendered}");
        assert!(rendered.contains("Looped = looped or false"), "{rendered}");
        assert!(rendered.contains("Speed = speed or 1"), "{rendered}");
        assert!(!rendered.contains("object.Looped"), "{rendered}");
        assert!(!rendered.contains("object.Speed"), "{rendered}");
    }

    #[test]
    fn keeps_copy_when_overwrite_reads_same_name() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["fn".into()],
                values: vec![Expr::Var("fn".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("fn".into()), Expr::Var("result".into())],
                values: vec![Expr::Call(
                    Box::new(Expr::Var("fn".into())),
                    vec![Expr::Num("1".into())],
                )],
            },
            Stmt::Return(vec![Expr::Var("fn".into()), Expr::Var("result".into())]),
        ];

        dead_store_elim(&mut stmts, &BTreeSet::new());

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("local fn = fn"), "{rendered}");
        assert!(rendered.contains("fn, result = fn(1)"), "{rendered}");
    }

    #[test]
    fn drops_unreachable_after_goto_until_next_label() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("cond".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("value".into())],
                        values: vec![Expr::Num("1".into())],
                    },
                    Stmt::Goto("done".into()),
                    Stmt::Assign {
                        targets: vec![Expr::Var("value".into())],
                        values: vec![Expr::Num("2".into())],
                    },
                ],
                else_body: Vec::new(),
            },
            Stmt::Label("done".into()),
            Stmt::Return(vec![Expr::Var("value".into())]),
        ];

        drop_unreachable(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("goto done"), "{rendered}");
        assert!(rendered.contains("::done::"), "{rendered}");
        assert!(rendered.contains("value = 1"), "{rendered}");
        assert!(!rendered.contains("value = 2"), "{rendered}");
    }

    #[test]
    fn drops_only_function_body_trailing_empty_return() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("ok".into()),
                then_body: vec![Stmt::Return(Vec::new())],
                else_body: Vec::new(),
            },
            Stmt::Return(Vec::new()),
        ];

        drop_trailing_empty_return(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("return"), "{rendered}");
        assert!(rendered.trim_end().ends_with("end"), "{rendered}");
    }

    #[test]
    fn recovers_nested_if_skip_goto() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Binary(
                    "==",
                    Box::new(Expr::Var("kind".into())),
                    Box::new(Expr::Str("\"Vector3\"".into())),
                ),
                then_body: vec![Stmt::If {
                    cond: Expr::Var("point".into()),
                    then_body: vec![Stmt::Goto("done".into())],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("value".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("point".into())),
                    "Position".into(),
                )],
            },
            Stmt::Label("done".into()),
            Stmt::Return(vec![Expr::Var("value".into())]),
        ];

        recover_if_skip_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if kind ~= \"Vector3\" or not point then"),
            "{rendered}"
        );
        assert!(rendered.contains("value = point.Position"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::done::"), "{rendered}");
    }

    #[test]
    fn recovers_loop_guard_else_goto() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Binary(
                    "~=",
                    Box::new(Expr::Var("kind".into())),
                    Box::new(Expr::Str("\"Vector3\"".into())),
                ),
                then_body: vec![
                    Stmt::If {
                        cond: Expr::Binary(
                            "~=",
                            Box::new(Expr::Var("kind".into())),
                            Box::new(Expr::Str("\"Instance\"".into())),
                        ),
                        then_body: vec![Stmt::Goto("bad".into())],
                        else_body: Vec::new(),
                    },
                    Stmt::If {
                        cond: Expr::Unary("not ", Box::new(Expr::Var("isBasePart".into()))),
                        then_body: vec![Stmt::Goto("bad".into())],
                        else_body: Vec::new(),
                    },
                ],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("bezier".into())),
                "AddBezierPoint".into(),
                vec![Expr::Var("point".into())],
            )),
            Stmt::Continue,
            Stmt::Label("bad".into()),
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("error".into())),
                vec![Expr::Str("\"bad point\"".into())],
            )),
        ];

        recover_guard_else_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered
                .contains("if kind == \"Vector3\" or (kind == \"Instance\" and isBasePart) then"),
            "{rendered}"
        );
        assert!(
            rendered.contains("bezier:AddBezierPoint(point)"),
            "{rendered}"
        );
        assert!(
            rendered.contains("else\n\terror(\"bad point\")"),
            "{rendered}"
        );
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::bad::"), "{rendered}");
        assert!(!rendered.contains("continue"), "{rendered}");
    }

    #[test]
    fn recovers_goto_into_labeled_if_gate() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("isInstance".into()),
                then_body: vec![Stmt::If {
                    cond: Expr::Var("isBasePart".into()),
                    then_body: vec![Stmt::Goto("accept".into())],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("isVector".into()),
                then_body: vec![
                    Stmt::Label("accept".into()),
                    Stmt::Call(Expr::MethodCall(
                        Box::new(Expr::Var("bezier".into())),
                        "AddBezierPoint".into(),
                        vec![Expr::Var("point".into())],
                    )),
                ],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("error".into())),
                vec![Expr::Str("\"bad point\"".into())],
            )),
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if (isInstance and isBasePart) or isVector then"),
            "{rendered}"
        );
        assert!(
            rendered.contains("bezier:AddBezierPoint(point)"),
            "{rendered}"
        );
        assert!(rendered.contains("error(\"bad point\")"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::accept::"), "{rendered}");
    }
}

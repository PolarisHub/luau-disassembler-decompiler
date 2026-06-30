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
    // Inlining is strictly block-local: a definition and the use it folds into are always in the
    // same block (the def->use window is verified to contain no control flow), so a rewrite in one
    // block never enables a rewrite in another. Reduce each nested block to its own fixpoint FIRST,
    // then reduce this block — visiting every block once instead of restarting the whole-tree scan
    // from the root after each rewrite. The per-block result and the restart-from-0 order *within*
    // a block are unchanged (the same nested-then-flat order the old `while inline_in_block` ran);
    // only the wasteful cross-block re-traversal is removed.
    for s in root.iter_mut() {
        match s {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                single_use_inline(then_body, protected);
                single_use_inline(else_body, protected);
            }
            Stmt::While { cond, body } | Stmt::Repeat { body, cond } => {
                let mut loop_protected = protected.clone();
                loop_protected.extend(reads_of_expr(cond));
                single_use_inline(body, &loop_protected);
            }
            Stmt::NumericFor { body, .. } | Stmt::GenericFor { body, .. } => {
                single_use_inline(body, protected);
            }
            _ => {}
        }
    }
    while flat_inline_once(root, protected) {}
}

/// Remove dead pure stores; reduce dead call-stores to bare calls. `protected` names are
/// never removed.
pub fn dead_store_elim(root: &mut Vec<Stmt>, protected: &BTreeSet<String>) {
    // Each pass removes every store the current use-counts prove dead — both the never-read
    // ones and the overwritten-before-read ones — in a single traversal, then recomputes once
    // to expose cascades. The removals are monotone (deleting a store only lowers other
    // variables' read counts, never raises them), so batching reaches the same fixpoint as
    // removing one-at-a-time would, at a fraction of the `count_uses` recomputes that dominated
    // large protos (the loop used to recompute the whole-tree count after every single removal).
    loop {
        let uses = count_uses(root);
        let removed_unread = dead_in_block_all(root, &uses, protected);
        let removed_overwritten = dead_overwritten_all(root, protected);
        if !removed_unread && !removed_overwritten {
            break;
        }
    }
}

/// Remove a pure assignment after the variable's final read in the current block. This catches
/// register-reuse leftovers like `key = 60` where the name was legitimately read earlier, so a
/// whole-function use count cannot prove the final store dead.
pub fn remove_dead_pure_stores_after_last_read(root: &mut Vec<Stmt>, protected: &BTreeSet<String>) {
    while dead_after_last_read_in_block(root, protected) {}
}

/// Remove duplicated pure condition checks introduced by conservative goto recovery.
///
/// The common shape is:
///
/// ```lua
/// if not x then
///     if not x then
///         return
///     end
/// end
/// ```
///
/// Once the outer branch is entered, the inner condition is known. Re-evaluating it is only
/// removable when the expression is pure and syntactically identical. The same pass also folds
/// pure `a and a` / `a or a` expression noise.
pub fn simplify_redundant_conditions(root: &mut [Stmt]) {
    for stmt in root.iter_mut() {
        simplify_redundant_condition_exprs(stmt);
        for_each_block_mut(stmt, |block| simplify_redundant_conditions(block));
    }

    while simplify_redundant_nested_if_once(root) {}
}

fn simplify_redundant_nested_if_once(root: &mut [Stmt]) -> bool {
    for stmt in root {
        let Stmt::If {
            cond,
            then_body,
            else_body,
        } = stmt
        else {
            continue;
        };
        if !else_body.is_empty() || then_body.len() != 1 || !is_pure(cond) {
            continue;
        }
        let Stmt::If {
            cond: inner_cond,
            then_body: inner_then,
            else_body: inner_else,
        } = &then_body[0]
        else {
            continue;
        };
        if !inner_else.is_empty() || inner_cond != cond {
            continue;
        }
        *then_body = inner_then.clone();
        return true;
    }
    false
}

fn simplify_redundant_condition_exprs(stmt: &mut Stmt) {
    match stmt {
        Stmt::If { cond, .. } | Stmt::While { cond, .. } | Stmt::Repeat { cond, .. } => {
            simplify_expr(cond);
        }
        Stmt::Local { values, .. } | Stmt::Assign { values, .. } | Stmt::Return(values) => {
            for value in values {
                simplify_expr(value);
            }
        }
        Stmt::Call(expr) => {
            simplify_expr(expr);
        }
        Stmt::NumericFor {
            start, limit, step, ..
        } => {
            simplify_expr(start);
            simplify_expr(limit);
            if let Some(step) = step {
                simplify_expr(step);
            }
        }
        Stmt::GenericFor { exprs, .. } => {
            for expr in exprs {
                simplify_expr(expr);
            }
        }
        Stmt::Break | Stmt::Continue | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => {}
    }
}

fn simplify_expr(expr: &mut Expr) -> bool {
    let mut changed = match expr {
        Expr::Index(base, key) => simplify_expr(base) | simplify_expr(key),
        Expr::Field(base, _) => simplify_expr(base),
        Expr::Call(callee, args) => {
            let mut changed = simplify_expr(callee);
            for arg in args {
                changed |= simplify_expr(arg);
            }
            changed
        }
        Expr::MethodCall(receiver, _, args) => {
            let mut changed = simplify_expr(receiver);
            for arg in args {
                changed |= simplify_expr(arg);
            }
            changed
        }
        Expr::Unary("not ", inner) => {
            let mut changed = simplify_expr(inner);
            if let Some(simplified) = simplify_not_operand(inner) {
                **inner = simplified;
                changed = true;
            }
            changed
        }
        Expr::Unary(_, inner) => simplify_expr(inner),
        Expr::Binary(_, left, right) => simplify_expr(left) | simplify_expr(right),
        Expr::Table(fields) => {
            let mut changed = false;
            for field in fields {
                match field {
                    TableField::Item(value) | TableField::Named(_, value) => {
                        changed |= simplify_expr(value);
                    }
                    TableField::Keyed(key, value) => {
                        changed |= simplify_expr(key);
                        changed |= simplify_expr(value);
                    }
                }
            }
            changed
        }
        Expr::Nil
        | Expr::Bool(_)
        | Expr::Num(_)
        | Expr::Str(_)
        | Expr::Vector(_)
        | Expr::Var(_)
        | Expr::Vararg
        | Expr::Closure { .. }
        | Expr::Raw(_) => false,
    };

    if let Expr::Binary(op @ ("and" | "or"), _, _) = expr {
        let op = *op;
        let mut operands = Vec::new();
        collect_same_binary_operands(expr, op, &mut operands);

        let mut unique = Vec::with_capacity(operands.len());
        for operand in operands {
            if is_pure(&operand) && unique.iter().any(|existing| existing == &operand) {
                changed = true;
            } else {
                unique.push(operand);
            }
        }

        if changed {
            *expr = rebuild_binary_chain(op, unique);
        }
    }
    changed
}

fn simplify_not_operand(expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::Binary("or", left, right) if matches!(right.as_ref(), Expr::Nil) && is_pure(left) => {
            Some(*left.clone())
        }
        Expr::Binary("or", left, right) if matches!(left.as_ref(), Expr::Nil) && is_pure(right) => {
            Some(*right.clone())
        }
        _ => None,
    }
}

fn collect_same_binary_operands(expr: &Expr, op: &'static str, out: &mut Vec<Expr>) {
    match expr {
        Expr::Binary(inner_op, left, right) if *inner_op == op => {
            collect_same_binary_operands(left, op, out);
            collect_same_binary_operands(right, op, out);
        }
        other => out.push(other.clone()),
    }
}

fn rebuild_binary_chain(op: &'static str, mut operands: Vec<Expr>) -> Expr {
    if operands.is_empty() {
        return Expr::Bool(true);
    }
    let mut expr = operands.remove(0);
    for operand in operands {
        expr = Expr::Binary(op, Box::new(expr), Box::new(operand));
    }
    expr
}

fn dead_after_last_read_in_block(block: &mut Vec<Stmt>, protected: &BTreeSet<String>) -> bool {
    for i in 0..block.len() {
        let Some((name, val)) = sole_var_assign(&block[i]) else {
            continue;
        };
        if protected.contains(&name) || !is_pure(&val) {
            continue;
        }
        if block[i + 1..]
            .iter()
            .any(|stmt| stmt_reads_var_recursive(stmt, &name))
        {
            continue;
        }
        if block[i + 1..].iter().any(stmt_contains_nonlocal_flow) {
            continue;
        }
        block.remove(i);
        return true;
    }
    false
}

/// A label as the final statement of a proto is just the function's natural return point.
/// Gotos to it from nested branches are early exits from the function, so rewrite them to
/// `return` and remove the label.
pub fn replace_terminal_label_gotos_with_return(root: &mut Vec<Stmt>) {
    let Some((label_idx, label)) = terminal_label(root) else {
        return;
    };
    if count_gotos_named(root, &label) == 0 {
        return;
    }
    replace_gotos_with_return(root, &label);
    root.remove(label_idx);
}

/// Recover a terminal shared tail:
///
/// ```lua
/// if a then
///     setup()
///     goto done
/// end
/// fallback()
/// ::done::
/// finish()
/// ```
///
/// When the label is at function end and the tail is tiny, jumps to it can be represented as
/// `finish(); return` inside the jumping branch while the natural fallthrough keeps the single
/// terminal tail. This avoids keeping a label solely for a small common epilogue.
pub fn replace_terminal_label_tail_gotos(root: &mut Vec<Stmt>) {
    let Some((mut label_idx, label, _tail)) = terminal_label_tail(root) else {
        return;
    };
    if label_idx > 0 && matches!(&root[label_idx - 1], Stmt::Goto(target) if target == &label) {
        root.remove(label_idx - 1);
        label_idx -= 1;
    }
    let tail = root[label_idx + 1..].to_vec();
    if count_gotos_named(&root[..label_idx], &label) == 0 {
        root.remove(label_idx);
        return;
    }
    if has_goto_in_nested_loop(&root[..label_idx], &label, false) {
        return;
    }
    let Some(first_goto_idx) = root[..label_idx]
        .iter()
        .position(|stmt| count_gotos_named_stmt(stmt, &label) > 0)
    else {
        return;
    };
    if tail_reads_late_local(root, first_goto_idx, label_idx, &tail) {
        return;
    }
    if replace_gotos_with_tail_return_before(root, &mut label_idx, &label, &tail)
        && count_gotos_named(&root[..label_idx], &label) == 0
    {
        root.remove(label_idx);
    }
}

/// Like `replace_terminal_label_tail_gotos`, but also handles gotos nested inside loops when
/// the shared tail itself terminates the function. A `goto done` from inside a loop to:
///
/// ```lua
/// ::done::
/// cleanup()
/// return value
/// ```
///
/// is equivalent to `cleanup(); return value` at the jump site. This is intentionally narrower
/// than the normal terminal-tail pass: non-terminating tails still need structured loop exits.
pub fn replace_loop_gotos_to_terminal_label_tail(root: &mut Vec<Stmt>) {
    let Some((mut label_idx, label, tail)) = terminal_label_tail(root) else {
        return;
    };
    if !block_ends_terminated(&tail) || count_gotos_named(&root[..label_idx], &label) == 0 {
        return;
    }
    let Some(first_goto_idx) = root[..label_idx]
        .iter()
        .position(|stmt| count_gotos_named_stmt(stmt, &label) > 0)
    else {
        return;
    };
    if tail_reads_late_local(root, first_goto_idx, label_idx, &tail) {
        return;
    }
    if replace_gotos_with_terminal_tail_before(root, &mut label_idx, &label, &tail)
        && count_gotos_named(&root[..label_idx], &label) == 0
    {
        root.remove(label_idx);
    }
}

/// If previous structuring removed a terminal label but left a final jump to it, the jump is
/// just the function's natural exit.
pub fn replace_orphan_terminal_goto_with_return(root: &mut [Stmt]) {
    let labels = label_names(root);
    let Some(idx) = orphan_terminal_goto_idx(root) else {
        return;
    };
    let Stmt::Goto(label) = &root[idx] else {
        return;
    };
    if !labels.contains(label) {
        root[idx] = Stmt::Return(Vec::new());
    }
}

/// Labels that immediately return are just shared early-return targets. Replacing gotos to
/// them with the same return removes noisy labels without moving any non-returning work.
pub fn replace_return_label_gotos(root: &mut Vec<Stmt>) {
    let return_labels = return_only_labels(root);
    if return_labels.is_empty() {
        return;
    }
    replace_gotos_to_return_labels(root, &return_labels);
    remove_return_only_labels(root, &return_labels);
}

/// Recover missing-label joins whose continuation is terminal and can be safely duplicated at
/// each jump. This handles value-selection code like:
///
/// ```lua
/// if candidate:IsA("Sound") then
///     sound = candidate
///     goto done
/// end
/// sound = candidate:FindFirstChildWhichIsA("Sound")
/// if not sound then return nil end
/// return use(sound)
/// ```
///
/// after earlier passes removed `::done::`. The rewrite copies the terminal suffix beginning at
/// `if not sound ...` into each jump site, preserving the natural fallback path and avoiding a
/// raw orphan goto. It is intentionally limited to one join variable and terminal suffixes.
pub fn replace_orphan_gotos_with_terminal_continuation(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, replace_orphan_gotos_with_terminal_continuation);
    }
    while replace_orphan_gotos_with_terminal_continuation_once(root) {}
}

/// Recover missing-label joins whose purpose was to skip a bounded fallback block before the
/// next read of the selected value:
///
/// ```lua
/// if fast then
///     value = cached
///     goto done
/// end
/// value = compute()
/// if value then
///     use(value)
/// end
/// ```
///
/// becomes:
///
/// ```lua
/// if fast then
///     value = cached
/// else
///     value = compute()
/// end
/// if value then
///     use(value)
/// end
/// ```
///
/// The pass is deliberately conservative: it only handles one synthesized join variable, only
/// moves a small label-free/goto-free fallback region, and widens locals that are still needed
/// after the join.
pub fn recover_orphan_if_fallback_gotos(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_orphan_if_fallback_gotos);
    }
    while recover_orphan_if_fallback_once(root) {}
}

/// Recover missing-label skips where the target was a short fallthrough point after a bounded
/// calculation block:
///
/// ```lua
/// if skip_a then goto done end
/// if skip_b then goto done end
/// update()
/// local next = ...
/// ```
///
/// becomes:
///
/// ```lua
/// if not (skip_a or skip_b) then
///     update()
/// end
/// local next = ...
/// ```
///
/// This only runs when every jump to the missing label is in one consecutive guard run, so it
/// never guesses across unrelated branches.
pub fn recover_orphan_skip_blocks(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_orphan_skip_blocks);
    }
    while recover_orphan_skip_block_once(root) {}
}

pub fn recover_nested_orphan_skip_gotos(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_nested_orphan_skip_gotos);
    }
    while recover_nested_orphan_skip_once(root) || recover_orphan_multistmt_skip_once(root) {}
}

pub fn retarget_missing_gotos_to_next_label(root: &mut [Stmt]) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, |block| retarget_missing_gotos_to_next_label(block));
    }
    while retarget_missing_goto_to_next_label_once(root) {}
}

pub fn recover_loop_bool_selector_gotos(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_loop_bool_selector_gotos);
    }
    while recover_loop_bool_selector_once(root)
        || recover_loop_bool_assignment_break_once(root)
        || recover_loop_bool_guard_break_once(root)
        || remove_trailing_missing_loop_goto_once(root)
    {}
}

pub fn recover_loop_find_breaks(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_loop_find_breaks);
    }
    while recover_loop_find_break_once(root) || recover_loop_find_fallback_block_once(root) {}
}

pub fn recover_forward_label_skip_gotos(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_forward_label_skip_gotos);
    }
    while recover_forward_label_skip_once(root) {}
}

pub fn recover_missing_label_skip_to_block_end_gotos(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_missing_label_skip_to_block_end_gotos);
    }
    while recover_missing_label_skip_to_block_end_once(root) {}
}

pub fn recover_missing_guard_skip_to_block_end_gotos(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_missing_guard_skip_to_block_end_gotos);
    }
    while recover_missing_guard_skip_to_block_end_once(root) {}
}

pub fn recover_duplicate_labeled_terminal_bodies(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_duplicate_labeled_terminal_bodies);
    }
    while recover_duplicate_labeled_terminal_body_once(root) {}
}

pub fn recover_duplicate_labeled_bodies(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_duplicate_labeled_bodies);
    }
    while recover_duplicate_labeled_body_once(root) {}
}

fn recover_loop_find_break_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        if !is_loop_stmt(&root[i]) {
            i += 1;
            continue;
        }
        let Some((result_var, default_value)) = sole_var_assign(&root[i + 1]) else {
            i += 1;
            continue;
        };
        let default_is_nil = matches!(default_value, Expr::Nil);
        let labels = label_names(root);
        let goto_labels = goto_names_in_stmt(&root[i]);
        for label in goto_labels {
            let label_after_default =
                matches!(root.get(i + 2), Some(Stmt::Label(name)) if name == &label);
            if !default_is_nil && !label_after_default {
                continue;
            }
            let loop_gotos = count_gotos_named_stmt(&root[i], &label);
            if labels.contains(&label)
                && (!label_after_default || count_gotos_named(root, &label) != loop_gotos)
            {
                continue;
            }
            let Some(body) = loop_body_mut(&mut root[i]) else {
                continue;
            };
            if has_goto_in_nested_loop(body, &label, false)
                || !all_gotos_preceded_by_assign_to(body, &label, &result_var)
            {
                continue;
            }
            replace_gotos_with_break(body, &label);
            let default = root.remove(i + 1);
            root.insert(i, default);
            if label_after_default
                && matches!(root.get(i + 2), Some(Stmt::Label(name)) if name == &label)
            {
                root.remove(i + 2);
            }
            return true;
        }
        i += 1;
    }
    false
}

fn recover_loop_find_fallback_block_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 2 < root.len() {
        if !is_loop_stmt(&root[i]) {
            i += 1;
            continue;
        }
        let labels = goto_names_in_stmt(&root[i]);
        for label in labels {
            let Some(label_idx) = root[i + 2..]
                .iter()
                .position(|stmt| matches!(stmt, Stmt::Label(name) if name == &label))
                .map(|offset| i + 2 + offset)
            else {
                continue;
            };
            let fallback = &root[i + 1..label_idx];
            let Some((result_var, _)) = fallback.last().and_then(sole_var_assign) else {
                continue;
            };
            let loop_gotos = count_gotos_named_stmt(&root[i], &label);
            if fallback.len() > 6
                || loop_gotos == 0
                || count_gotos_named(root, &label) != loop_gotos
                || contains_label_or_goto(fallback)
                || !fallback.iter().all(is_pure_assignment_stmt)
            {
                continue;
            }

            let Some(body) = loop_body_mut(&mut root[i]) else {
                continue;
            };
            if has_goto_in_nested_loop(body, &label, false)
                || !all_gotos_preceded_by_assign_to(body, &label, &result_var)
            {
                continue;
            }

            replace_gotos_with_break(body, &label);
            let fallback = root[i + 1..label_idx].to_vec();
            root.drain(i + 1..=label_idx);
            for (offset, stmt) in fallback.into_iter().enumerate() {
                root.insert(i + offset, stmt);
            }
            return true;
        }
        i += 1;
    }
    false
}

fn is_pure_assignment_stmt(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Assign { targets, values } => {
            targets.iter().all(|target| matches!(target, Expr::Var(_)))
                && values.iter().all(is_pure)
        }
        Stmt::Local { values, .. } => values.iter().all(is_pure),
        _ => false,
    }
}

fn recover_forward_label_skip_once(root: &mut Vec<Stmt>) -> bool {
    for label_idx in 2..root.len() {
        let Stmt::Label(label) = &root[label_idx] else {
            continue;
        };
        let label = label.clone();
        let Some(first_goto_idx) = root[..label_idx]
            .iter()
            .position(|stmt| count_gotos_named_stmt(stmt, &label) > 0)
        else {
            continue;
        };
        let region_gotos = count_gotos_named(&root[first_goto_idx..label_idx], &label);
        if region_gotos == 0
            || count_gotos_named(root, &label) != region_gotos
            || label_idx - first_goto_idx > 32
            || contains_label_or_goto_except_gotos(&root[first_goto_idx..label_idx], &label)
            || contains_break_continue(&root[first_goto_idx..label_idx])
            || has_goto_in_nested_loop(&root[first_goto_idx..label_idx], &label, false)
        {
            continue;
        }

        let mut wrapped = root[first_goto_idx..label_idx].to_vec();
        replace_gotos_with_break(&mut wrapped, &label);
        root.splice(
            first_goto_idx..=label_idx,
            [Stmt::Repeat {
                body: wrapped,
                cond: Expr::Bool(true),
            }],
        );
        return true;
    }
    false
}

fn recover_missing_label_skip_to_block_end_once(root: &mut Vec<Stmt>) -> bool {
    let labels = label_names(root);
    let missing = missing_goto_labels(root, &labels);
    for label in missing {
        let Some(first_goto_idx) = root
            .iter()
            .position(|stmt| count_gotos_named_stmt(stmt, &label) > 0)
        else {
            continue;
        };
        let region = &root[first_goto_idx..];
        let region_gotos = count_gotos_named(region, &label);
        if region_gotos == 0
            || count_gotos_named(root, &label) != region_gotos
            || region.len() > 32
            || contains_label_or_goto_except_gotos(region, &label)
            || contains_direct_break_continue(region)
            || has_goto_in_nested_loop(region, &label, false)
        {
            continue;
        }

        let mut wrapped = root.split_off(first_goto_idx);
        replace_gotos_with_break(&mut wrapped, &label);
        root.push(Stmt::Repeat {
            body: wrapped,
            cond: Expr::Bool(true),
        });
        return true;
    }
    false
}

fn recover_missing_guard_skip_to_block_end_once(root: &mut Vec<Stmt>) -> bool {
    let labels = label_names(root);
    let mut i = 0;
    while i + 1 < root.len() {
        let Some((cond, label)) = conditional_goto_expr(&root[i], None) else {
            i += 1;
            continue;
        };
        let goto_count = count_gotos_named_stmt(&root[i], &label);
        let tail = &root[i + 1..];
        if labels.contains(&label)
            || goto_count == 0
            || count_gotos_named(root, &label) != goto_count
            || tail.is_empty()
            || tail.len() > 32
            || contains_label_or_goto(tail)
        {
            i += 1;
            continue;
        }

        let then_body = tail.to_vec();
        root.truncate(i);
        root.push(Stmt::If {
            cond: negate_condition(cond),
            then_body,
            else_body: Vec::new(),
        });
        return true;
    }
    false
}

fn recover_duplicate_labeled_terminal_body_once(root: &mut Vec<Stmt>) -> bool {
    let mut candidates: BTreeMap<String, Vec<Vec<Stmt>>> = BTreeMap::new();
    for stmt in root.iter() {
        collect_immediate_labeled_terminal_bodies(stmt, &mut candidates);
    }

    for (label, bodies) in candidates {
        let Some(first) = bodies.first() else {
            continue;
        };
        if first.is_empty()
            || contains_label_or_goto(first)
            || !block_ends_terminated(first)
            || !bodies.iter().all(|body| body == first)
            || count_gotos_named(root, &label) == 0
            || has_goto_in_nested_loop(root, &label, false)
        {
            continue;
        }

        replace_gotos_with_body(root, &label, first);
        strip_leading_labels_named(root, &label);
        return true;
    }
    false
}

fn recover_duplicate_labeled_body_once(root: &mut Vec<Stmt>) -> bool {
    let mut candidates: BTreeMap<String, Vec<Vec<Stmt>>> = BTreeMap::new();
    for stmt in root.iter() {
        collect_immediate_labeled_bodies(stmt, &mut candidates);
    }

    for (label, bodies) in candidates {
        let Some(first) = bodies.first() else {
            continue;
        };
        if first.is_empty()
            || contains_label_or_goto(first)
            || contains_direct_break_continue(first)
            || !bodies.iter().all(|body| body == first)
            || count_labels_named(root, &label) != bodies.len()
            || count_gotos_named(root, &label) == 0
            || has_goto_in_nested_loop(root, &label, false)
        {
            continue;
        }

        replace_gotos_with_body(root, &label, first);
        strip_leading_labels_named(root, &label);
        return true;
    }
    false
}

fn collect_immediate_labeled_terminal_bodies(
    stmt: &Stmt,
    candidates: &mut BTreeMap<String, Vec<Vec<Stmt>>>,
) {
    let Stmt::If {
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return;
    };

    for body in [then_body, else_body] {
        let Some(Stmt::Label(label)) = body.first() else {
            continue;
        };
        let tail = body[1..].to_vec();
        if block_ends_terminated(&tail) {
            candidates.entry(label.clone()).or_default().push(tail);
        }
    }
}

fn collect_immediate_labeled_bodies(
    stmt: &Stmt,
    candidates: &mut BTreeMap<String, Vec<Vec<Stmt>>>,
) {
    let Stmt::If {
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return;
    };

    for body in [then_body, else_body] {
        let Some(Stmt::Label(label)) = body.first() else {
            continue;
        };
        candidates
            .entry(label.clone())
            .or_default()
            .push(body[1..].to_vec());
    }
}

fn replace_gotos_with_body(stmts: &mut Vec<Stmt>, label: &str, body: &[Stmt]) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < stmts.len() {
        match &mut stmts[i] {
            Stmt::Goto(target) if target == label => {
                stmts.splice(i..=i, body.to_vec());
                i += body.len();
                changed = true;
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                changed |= replace_gotos_with_body(then_body, label, body);
                changed |= replace_gotos_with_body(else_body, label, body);
                i += 1;
            }
            Stmt::While {
                body: loop_body, ..
            }
            | Stmt::Repeat {
                body: loop_body, ..
            }
            | Stmt::NumericFor {
                body: loop_body, ..
            }
            | Stmt::GenericFor {
                body: loop_body, ..
            } => {
                changed |= replace_gotos_with_body(loop_body, label, body);
                i += 1;
            }
            _ => i += 1,
        }
    }
    changed
}

fn strip_leading_labels_named(stmts: &mut Vec<Stmt>, label: &str) {
    for stmt in stmts {
        match stmt {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                if matches!(then_body.first(), Some(Stmt::Label(name)) if name == label) {
                    then_body.remove(0);
                }
                if matches!(else_body.first(), Some(Stmt::Label(name)) if name == label) {
                    else_body.remove(0);
                }
                strip_leading_labels_named(then_body, label);
                strip_leading_labels_named(else_body, label);
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. } => strip_leading_labels_named(body, label),
            _ => {}
        }
    }
}

fn all_gotos_preceded_by_assign_to(stmts: &[Stmt], label: &str, var: &str) -> bool {
    let mut found = false;
    all_gotos_preceded_by_assign_to_inner(stmts, label, var, &mut found) && found
}

fn all_gotos_preceded_by_assign_to_inner(
    stmts: &[Stmt],
    label: &str,
    var: &str,
    found: &mut bool,
) -> bool {
    for (idx, stmt) in stmts.iter().enumerate() {
        match stmt {
            Stmt::Goto(target) if target == label => {
                *found = true;
                let Some(prev) = idx.checked_sub(1).and_then(|prev| stmts.get(prev)) else {
                    return false;
                };
                if !matches!(sole_var_assign(prev), Some((name, _)) if name == var) {
                    return false;
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } if !all_gotos_preceded_by_assign_to_inner(then_body, label, var, found)
                || !all_gotos_preceded_by_assign_to_inner(else_body, label, var, found) =>
            {
                return false;
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. }
                if !all_gotos_preceded_by_assign_to_inner(body, label, var, found) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn retarget_missing_goto_to_next_label_once(root: &mut [Stmt]) -> bool {
    let labels = label_names(root);
    for i in 0..root.len() {
        let missing: Vec<String> = goto_names_in_stmt(&root[i])
            .into_iter()
            .filter(|label| !labels.contains(label))
            .collect();
        if missing.is_empty() {
            continue;
        }
        let Some(next_label) = root[i + 1..].iter().find_map(|stmt| match stmt {
            Stmt::Label(label) => Some(label.clone()),
            _ => None,
        }) else {
            continue;
        };

        for label in missing {
            if has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false) {
                continue;
            }
            if retarget_gotos_in_stmt(&mut root[i], &label, &next_label) {
                return true;
            }
        }
    }
    false
}

fn retarget_gotos_in_stmt(stmt: &mut Stmt, from: &str, to: &str) -> bool {
    match stmt {
        Stmt::Goto(label) if label == from => {
            *label = to.to_string();
            true
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            retarget_gotos_in_block(then_body, from, to)
                | retarget_gotos_in_block(else_body, from, to)
        }
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => retarget_gotos_in_block(body, from, to),
        _ => false,
    }
}

fn retarget_gotos_in_block(stmts: &mut [Stmt], from: &str, to: &str) -> bool {
    let mut changed = false;
    for stmt in stmts {
        changed |= retarget_gotos_in_stmt(stmt, from, to);
    }
    changed
}

fn recover_loop_bool_selector_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 2 < root.len() {
        if !is_loop_stmt(&root[i]) {
            i += 1;
            continue;
        }
        let Some((selector, Expr::Bool(true))) = sole_var_assign(&root[i + 1]) else {
            i += 1;
            continue;
        };
        if !if_is_negated_selector(&root[i + 2], &selector) {
            i += 1;
            continue;
        }

        let labels = goto_names_in_stmt(&root[i]);
        for label in labels {
            let Some(body) = loop_body_mut(&mut root[i]) else {
                continue;
            };
            if !all_gotos_preceded_by_bool_assign(body, &label, &selector, false) {
                continue;
            }
            replace_gotos_with_break(body, &label);
            if let Stmt::If { cond, .. } = &mut root[i + 2] {
                *cond = Expr::Unary("not ", Box::new(Expr::Var(selector.clone())));
            }
            let init = root.remove(i + 1);
            root.insert(i, init);
            return true;
        }

        i += 1;
    }
    false
}

fn recover_loop_bool_assignment_break_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        if !is_loop_stmt(&root[i]) {
            i += 1;
            continue;
        }
        let Some((selector, Expr::Bool(default_value))) = sole_var_assign(&root[i + 1]) else {
            i += 1;
            continue;
        };

        let labels = label_names(root);
        let goto_labels = goto_names_in_stmt(&root[i]);
        for label in goto_labels {
            if labels.contains(&label) {
                continue;
            }
            let Some(body) = loop_body_mut(&mut root[i]) else {
                continue;
            };
            if has_goto_in_nested_loop(body, &label, false)
                || !all_gotos_preceded_by_bool_assign(body, &label, &selector, !default_value)
            {
                continue;
            }

            replace_gotos_with_break(body, &label);
            if let Some(next) = root.get_mut(i + 2) {
                rewrite_const_bool_if_guard(next, &selector, default_value);
            }
            let init = root.remove(i + 1);
            root.insert(i, init);
            return true;
        }

        i += 1;
    }
    false
}

fn recover_loop_bool_guard_break_once(root: &mut [Stmt]) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        if !is_loop_stmt(&root[i]) {
            i += 1;
            continue;
        }
        let Some(selector) = if_negated_var(&root[i + 1]) else {
            i += 1;
            continue;
        };

        let labels = label_names(root);
        let goto_labels = goto_names_in_stmt(&root[i]);
        for label in goto_labels {
            if labels.contains(&label) {
                continue;
            }
            let Some(body) = loop_body_mut(&mut root[i]) else {
                continue;
            };
            if has_goto_in_nested_loop(body, &label, false)
                || !all_gotos_preceded_by_bool_assign(body, &label, &selector, true)
            {
                continue;
            }

            replace_gotos_with_break(body, &label);
            return true;
        }

        i += 1;
    }
    false
}

fn remove_trailing_missing_loop_goto_once(root: &mut [Stmt]) -> bool {
    let labels = label_names(root);
    for stmt in root {
        let Some(body) = loop_body_mut(stmt) else {
            continue;
        };
        if remove_tail_missing_goto(body, &labels) {
            return true;
        }
    }
    false
}

fn remove_tail_missing_goto(stmts: &mut Vec<Stmt>, labels: &BTreeSet<String>) -> bool {
    let Some(last) = stmts.last_mut() else {
        return false;
    };
    match last {
        Stmt::Goto(label) if !labels.contains(label) => {
            stmts.pop();
            true
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            remove_tail_missing_goto(then_body, labels)
                | remove_tail_missing_goto(else_body, labels)
        }
        _ => false,
    }
}

fn is_loop_stmt(stmt: &Stmt) -> bool {
    matches!(
        stmt,
        Stmt::While { .. }
            | Stmt::Repeat { .. }
            | Stmt::NumericFor { .. }
            | Stmt::GenericFor { .. }
    )
}

fn loop_body_mut(stmt: &mut Stmt) -> Option<&mut Vec<Stmt>> {
    match stmt {
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => Some(body),
        _ => None,
    }
}

fn if_is_negated_selector(stmt: &Stmt, selector: &str) -> bool {
    let Stmt::If { cond, .. } = stmt else {
        return false;
    };
    matches!(cond, Expr::Unary("not ", inner) if matches!(inner.as_ref(), Expr::Var(name) if name == selector) || matches!(inner.as_ref(), Expr::Bool(true)))
}

fn if_negated_var(stmt: &Stmt) -> Option<String> {
    let Stmt::If { cond, .. } = stmt else {
        return None;
    };
    match cond {
        Expr::Unary("not ", inner) => match inner.as_ref() {
            Expr::Var(name) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn rewrite_const_bool_if_guard(stmt: &mut Stmt, selector: &str, value: bool) {
    let Stmt::If { cond, .. } = stmt else {
        return;
    };
    match cond {
        Expr::Bool(current) if *current == value => {
            *cond = Expr::Var(selector.to_string());
        }
        Expr::Unary("not ", inner) if matches!(inner.as_ref(), Expr::Bool(current) if *current == value) =>
        {
            *cond = Expr::Unary("not ", Box::new(Expr::Var(selector.to_string())));
        }
        _ => {}
    }
}

fn all_gotos_preceded_by_bool_assign(
    stmts: &[Stmt],
    label: &str,
    selector: &str,
    value: bool,
) -> bool {
    let mut found = false;
    all_gotos_preceded_by_bool_assign_inner(stmts, label, selector, value, &mut found) && found
}

fn all_gotos_preceded_by_bool_assign_inner(
    stmts: &[Stmt],
    label: &str,
    selector: &str,
    value: bool,
    found: &mut bool,
) -> bool {
    for (idx, stmt) in stmts.iter().enumerate() {
        match stmt {
            Stmt::Goto(target) if target == label => {
                *found = true;
                let Some(prev) = idx.checked_sub(1).and_then(|prev| stmts.get(prev)) else {
                    return false;
                };
                if !matches!(
                    sole_var_assign(prev),
                    Some((name, Expr::Bool(v))) if name == selector && v == value
                ) {
                    return false;
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } if !all_gotos_preceded_by_bool_assign_inner(
                then_body, label, selector, value, found,
            ) || !all_gotos_preceded_by_bool_assign_inner(
                else_body, label, selector, value, found,
            ) =>
            {
                return false;
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. }
                if !all_gotos_preceded_by_bool_assign_inner(
                    body, label, selector, value, found,
                ) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn return_only_labels(root: &[Stmt]) -> BTreeMap<String, Vec<Expr>> {
    let mut candidates = BTreeMap::new();
    let mut rejected = BTreeSet::new();
    collect_return_only_labels(root, &mut candidates, &mut rejected);
    for label in rejected {
        candidates.remove(&label);
    }
    candidates
}

fn collect_return_only_labels(
    stmts: &[Stmt],
    candidates: &mut BTreeMap<String, Vec<Expr>>,
    rejected: &mut BTreeSet<String>,
) {
    for (idx, stmt) in stmts.iter().enumerate() {
        match stmt {
            Stmt::Label(label) => {
                let Some(Stmt::Return(values)) = stmts.get(idx + 1) else {
                    rejected.insert(label.clone());
                    continue;
                };
                match candidates.get(label) {
                    Some(existing) if existing != values => {
                        rejected.insert(label.clone());
                    }
                    Some(_) => {}
                    None => {
                        candidates.insert(label.clone(), values.clone());
                    }
                }
            }
            _ => for_each_block(stmt, |body| {
                collect_return_only_labels(body, candidates, rejected)
            }),
        }
    }
}

fn replace_gotos_to_return_labels(stmts: &mut [Stmt], labels: &BTreeMap<String, Vec<Expr>>) {
    for stmt in stmts {
        match stmt {
            Stmt::Goto(label) => {
                if let Some(values) = labels.get(label) {
                    *stmt = Stmt::Return(values.clone());
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                replace_gotos_to_return_labels(then_body, labels);
                replace_gotos_to_return_labels(else_body, labels);
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. } => replace_gotos_to_return_labels(body, labels),
            _ => {}
        }
    }
}

fn remove_return_only_labels(stmts: &mut Vec<Stmt>, labels: &BTreeMap<String, Vec<Expr>>) {
    let mut idx = 0;
    while idx < stmts.len() {
        match &mut stmts[idx] {
            Stmt::Label(label) if labels.contains_key(label) => {
                stmts.remove(idx);
            }
            stmt => {
                for_each_block_mut(stmt, |body| remove_return_only_labels(body, labels));
                idx += 1;
            }
        }
    }
}

fn orphan_terminal_goto_idx(root: &[Stmt]) -> Option<usize> {
    match root {
        [.., Stmt::Goto(_)] => Some(root.len() - 1),
        [.., Stmt::Goto(_), Stmt::Return(values)] if values.is_empty() => Some(root.len() - 2),
        _ => None,
    }
}

fn replace_orphan_gotos_with_terminal_continuation_once(root: &mut Vec<Stmt>) -> bool {
    let labels = label_names(root);
    let missing_labels = missing_goto_labels(root, &labels);
    for label in missing_labels {
        if has_goto_in_nested_loop(root, &label, false) {
            continue;
        }
        let Some(join_var) = orphan_join_assignment_var(root, &label) else {
            continue;
        };
        let Some(first_goto_idx) = root
            .iter()
            .position(|stmt| count_gotos_named_stmt(stmt, &label) > 0)
        else {
            continue;
        };

        for tail_start in first_goto_idx + 1..root.len() {
            let tail = root[tail_start..].to_vec();
            if tail.len() > 48
                || contains_label_or_goto(&tail)
                || !block_ends_terminated(&tail)
                || tail_reads_late_local(root, first_goto_idx, tail_start, &tail)
                || !stmt_reads_var_before_write(&root[tail_start], &join_var)
            {
                continue;
            }

            let mut boundary = tail_start;
            if replace_gotos_with_tail_return_before(root, &mut boundary, &label, &tail)
                && count_gotos_named(&root[..boundary], &label) == 0
            {
                return true;
            }
        }
    }
    false
}

fn recover_orphan_if_fallback_once(root: &mut Vec<Stmt>) -> bool {
    let labels = label_names(root);
    for i in (0..root.len()).rev() {
        let goto_labels = goto_names_in_stmt(&root[i]);
        if goto_labels.len() != 1 {
            continue;
        }
        let label = goto_labels.into_iter().next().unwrap();
        if labels.contains(&label)
            || has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false)
        {
            continue;
        }

        let mut vars = BTreeSet::new();
        if !collect_pre_goto_assignment_vars(std::slice::from_ref(&root[i]), &label, &mut vars)
            || vars.len() != 1
        {
            continue;
        }
        let join_var = vars.into_iter().next().unwrap();

        let Some(tail_start) =
            (i + 1..root.len()).find(|&idx| stmt_reads_var_before_write(&root[idx], &join_var))
        else {
            continue;
        };
        let mut fallback = root[i + 1..tail_start].to_vec();
        if fallback.is_empty()
            || fallback.len() > 64
            || contains_label_or_goto(&fallback)
            || block_ends_terminated(&fallback)
        {
            continue;
        }
        widen_locals_read_after_join(&mut fallback, &root[tail_start..]);
        if !direct_local_scope_safe(&fallback, &root[tail_start..]) {
            continue;
        }

        let Some(transformed) = absorb_join_in_stmt(root[i].clone(), &label, fallback) else {
            continue;
        };
        if contains_label_or_goto(std::slice::from_ref(&transformed)) {
            continue;
        }
        root[i] = transformed;
        root.drain(i + 1..tail_start);
        return true;
    }
    false
}

fn recover_orphan_skip_block_once(root: &mut Vec<Stmt>) -> bool {
    let labels = label_names(root);
    for i in 0..root.len() {
        let Some((first_cond, label)) = conditional_goto_expr(&root[i], None) else {
            continue;
        };
        if labels.contains(&label)
            || has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false)
        {
            continue;
        }

        let mut conds = vec![first_cond];
        let mut guard_end = i + 1;
        while guard_end < root.len() {
            let Some((cond, _)) = conditional_goto_expr(&root[guard_end], Some(&label)) else {
                break;
            };
            if has_goto_in_nested_loop(std::slice::from_ref(&root[guard_end]), &label, false) {
                break;
            }
            conds.push(cond);
            guard_end += 1;
        }

        let guard_gotos: usize = root[i..guard_end]
            .iter()
            .map(|stmt| count_gotos_named_stmt(stmt, &label))
            .sum();
        if guard_gotos == 0 || count_gotos_named(root, &label) != guard_gotos {
            continue;
        }

        let Some(boundary) = orphan_skip_boundary(root, guard_end) else {
            continue;
        };
        let mut skipped = root[guard_end..boundary].to_vec();
        widen_locals_read_after_join(&mut skipped, &root[boundary..]);
        if !direct_local_scope_safe(&skipped, &root[boundary..]) {
            continue;
        }

        let Some(skip_cond) = or_all(conds) else {
            continue;
        };
        root.splice(
            i..boundary,
            [Stmt::If {
                cond: negate_condition(skip_cond),
                then_body: skipped,
                else_body: Vec::new(),
            }],
        );
        return true;
    }
    false
}

fn recover_nested_orphan_skip_once(root: &mut Vec<Stmt>) -> bool {
    let labels = label_names(root);
    for i in 0..root.len() {
        let goto_labels = goto_names_in_stmt(&root[i]);
        for label in goto_labels {
            let goto_count = count_gotos_named_stmt(&root[i], &label);
            if goto_count == 0
                || labels.contains(&label)
                || count_gotos_named(root, &label) != goto_count
                || has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false)
            {
                continue;
            }

            let Some(boundary) = orphan_skip_boundary(root, i + 1) else {
                continue;
            };
            let mut normal_continuation = root[i + 1..boundary].to_vec();
            widen_locals_read_after_join(&mut normal_continuation, &root[boundary..]);
            if !direct_local_scope_safe(&normal_continuation, &root[boundary..]) {
                continue;
            }

            let Some(transformed) = route_gotos_to_target_body(
                vec![root[i].clone()],
                &label,
                Vec::new(),
                normal_continuation,
            ) else {
                continue;
            };
            if contains_label_or_goto(&transformed) {
                continue;
            }

            root.splice(i..boundary, transformed);
            return true;
        }
    }
    false
}

fn recover_orphan_multistmt_skip_once(root: &mut Vec<Stmt>) -> bool {
    let labels = label_names(root);
    let missing_labels = missing_goto_labels(root, &labels);
    for label in missing_labels {
        if has_goto_in_nested_loop(root, &label, false) {
            continue;
        }
        let indices: Vec<usize> = root
            .iter()
            .enumerate()
            .filter_map(|(idx, stmt)| (count_gotos_named_stmt(stmt, &label) > 0).then_some(idx))
            .collect();
        let (Some(first), Some(last)) = (indices.first().copied(), indices.last().copied()) else {
            continue;
        };
        if first == last
            || count_gotos_named(&root[first..=last], &label) != count_gotos_named(root, &label)
        {
            continue;
        }
        if contains_label_or_goto_except_gotos(&root[first..=last], &label) {
            continue;
        }

        let mut end = last + 1;
        if end < root.len() {
            let region_writes = direct_writes_in_block(&root[first..=last]);
            if is_pure_assignment_to_any(&root[end], &region_writes) {
                end += 1;
            }
        }

        let region = root[first..end].to_vec();
        let Some(transformed) =
            route_gotos_to_target_body_deep(region, &label, Vec::new(), Vec::new())
        else {
            continue;
        };
        if transformed.is_empty() || contains_label_or_goto(&transformed) {
            continue;
        }

        root.splice(first..end, transformed);
        return true;
    }
    false
}

fn is_pure_assignment_to_any(stmt: &Stmt, names: &BTreeSet<String>) -> bool {
    if names.is_empty() {
        return false;
    }
    match stmt {
        Stmt::Assign { targets, values } => {
            !values.is_empty()
                && values.iter().all(is_pure)
                && targets.iter().any(|target| match target {
                    Expr::Var(name) => names.contains(name),
                    _ => false,
                })
        }
        Stmt::Local {
            names: local_names,
            values,
        } => {
            !values.is_empty()
                && values.iter().all(is_pure)
                && local_names.iter().any(|name| names.contains(name))
        }
        _ => false,
    }
}

fn orphan_skip_boundary(root: &[Stmt], start: usize) -> Option<usize> {
    let max_end = root.len().min(start + 64);
    for boundary in start + 1..=max_end {
        let skipped = &root[start..boundary];
        if contains_label_or_goto(skipped) || block_ends_terminated(skipped) {
            return None;
        }
        if boundary == root.len() {
            return Some(boundary);
        }

        let writes = direct_writes_in_block(skipped);
        if !writes.is_empty()
            && stmt_reads_any_var_before_write(&root[boundary], &writes)
            && !stmt_definitely_writes_any_var(&root[boundary], &writes)
        {
            return Some(boundary);
        }

        if matches!(root[boundary], Stmt::Local { .. })
            && (skipped.len() >= 4 || skipped.last().is_some_and(is_nonlocal_effect_stmt))
        {
            return Some(boundary);
        }
    }
    None
}

fn direct_writes_in_block(stmts: &[Stmt]) -> BTreeSet<String> {
    let mut writes = BTreeSet::new();
    for stmt in stmts {
        writes.extend(writes_of_stmt(stmt));
    }
    writes
}

fn stmt_reads_any_var_before_write(stmt: &Stmt, names: &BTreeSet<String>) -> bool {
    names
        .iter()
        .any(|name| stmt_reads_var_before_write(stmt, name))
}

fn stmt_definitely_writes_any_var(stmt: &Stmt, names: &BTreeSet<String>) -> bool {
    names
        .iter()
        .any(|name| stmt_definitely_writes_var(stmt, name))
}

fn is_nonlocal_effect_stmt(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Call(_) => true,
        Stmt::Assign { targets, .. } => {
            targets.iter().any(|target| !matches!(target, Expr::Var(_)))
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => then_body
            .iter()
            .chain(else_body)
            .any(is_nonlocal_effect_stmt),
        _ => false,
    }
}

fn missing_goto_labels(root: &[Stmt], labels: &BTreeSet<String>) -> Vec<String> {
    let mut gotos = BTreeSet::new();
    for stmt in root {
        collect_goto_names(stmt, &mut gotos);
    }
    gotos
        .into_iter()
        .filter(|label| !labels.contains(label))
        .collect()
}

fn orphan_join_assignment_var(root: &[Stmt], label: &str) -> Option<String> {
    let mut vars = BTreeSet::new();
    if !collect_pre_goto_assignment_vars(root, label, &mut vars) || vars.len() != 1 {
        return None;
    }
    vars.into_iter().next()
}

fn collect_pre_goto_assignment_vars(
    stmts: &[Stmt],
    label: &str,
    vars: &mut BTreeSet<String>,
) -> bool {
    for (idx, stmt) in stmts.iter().enumerate() {
        match stmt {
            Stmt::Goto(target) if target == label => {
                let Some(prev) = idx.checked_sub(1).and_then(|prev| stmts.get(prev)) else {
                    return false;
                };
                let Some(name) = single_var_assignment_target(prev) else {
                    return false;
                };
                vars.insert(name);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } if !collect_pre_goto_assignment_vars(then_body, label, vars)
                || !collect_pre_goto_assignment_vars(else_body, label, vars) =>
            {
                return false;
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. }
                if count_gotos_named(body, label) > 0 =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn single_var_assignment_target(stmt: &Stmt) -> Option<String> {
    let Stmt::Assign { targets, values } = stmt else {
        return None;
    };
    if values.len() != 1 {
        return None;
    }
    match targets.as_slice() {
        [Expr::Var(name)] => Some(name.clone()),
        _ => None,
    }
}

fn stmt_reads_var_before_write(stmt: &Stmt, name: &str) -> bool {
    match stmt {
        Stmt::Local { names, values } => {
            values.iter().any(|value| expr_reads_var(value, name))
                || (!names.iter().any(|local| local == name)
                    && stmt_reads_var_recursive(stmt, name))
        }
        Stmt::Assign { targets, values } => {
            values.iter().any(|value| expr_reads_var(value, name))
                || (!targets.iter().any(|target| expr_writes_var(target, name))
                    && targets.iter().any(|target| expr_reads_var(target, name)))
        }
        Stmt::Call(expr) => expr_reads_var(expr, name),
        Stmt::Return(values) => values.iter().any(|value| expr_reads_var(value, name)),
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            expr_reads_var(cond, name)
                || block_reads_var_before_write(then_body, name)
                || block_reads_var_before_write(else_body, name)
        }
        Stmt::While { cond, body } => {
            expr_reads_var(cond, name) || block_reads_var_before_write(body, name)
        }
        Stmt::Repeat { cond, body } => {
            body.iter()
                .any(|stmt| stmt_reads_var_before_write(stmt, name))
                || expr_reads_var(cond, name)
        }
        Stmt::NumericFor {
            start, limit, step, ..
        } => {
            expr_reads_var(start, name)
                || expr_reads_var(limit, name)
                || step.as_ref().is_some_and(|step| expr_reads_var(step, name))
        }
        Stmt::GenericFor { vars, exprs, .. } => {
            !vars.iter().any(|var| var == name)
                && exprs.iter().any(|expr| expr_reads_var(expr, name))
        }
        Stmt::Break | Stmt::Continue | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => false,
    }
}

fn block_reads_var_before_write(stmts: &[Stmt], name: &str) -> bool {
    for stmt in stmts {
        if stmt_reads_var_before_write(stmt, name) {
            return true;
        }
        if stmt_definitely_writes_var(stmt, name) {
            return false;
        }
    }
    false
}

fn stmt_definitely_writes_var(stmt: &Stmt, name: &str) -> bool {
    match stmt {
        Stmt::Local { names, .. } => names.iter().any(|local| local == name),
        Stmt::Assign { targets, .. } => targets.iter().any(|target| expr_writes_var(target, name)),
        Stmt::If {
            then_body,
            else_body,
            ..
        } if !else_body.is_empty() => {
            block_definitely_writes_var(then_body, name)
                && block_definitely_writes_var(else_body, name)
        }
        _ => false,
    }
}

fn block_definitely_writes_var(stmts: &[Stmt], name: &str) -> bool {
    stmts
        .iter()
        .any(|stmt| stmt_definitely_writes_var(stmt, name))
}

fn expr_writes_var(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Var(var) if var == name)
}

fn terminal_label_tail(root: &[Stmt]) -> Option<(usize, String, Vec<Stmt>)> {
    for (idx, stmt) in root.iter().enumerate() {
        let Stmt::Label(label) = stmt else {
            continue;
        };
        let tail = &root[idx + 1..];
        if tail.is_empty()
            || tail.len() > 8
            || contains_label_or_goto(tail)
            || !tail.iter().all(is_simple_terminal_tail_stmt)
            || count_gotos_named(&root[..idx], label) == 0
        {
            continue;
        }
        return Some((idx, label.clone(), tail.to_vec()));
    }
    None
}

fn is_simple_terminal_tail_stmt(stmt: &Stmt) -> bool {
    matches!(stmt, Stmt::Assign { .. } | Stmt::Call(_) | Stmt::Return(_))
}

fn tail_reads_late_local(
    root: &[Stmt],
    first_goto_idx: usize,
    label_idx: usize,
    tail: &[Stmt],
) -> bool {
    let mut late_locals = BTreeSet::new();
    for stmt in &root[first_goto_idx + 1..label_idx] {
        if let Stmt::Local { names, .. } = stmt {
            late_locals.extend(names.iter().cloned());
        }
    }
    !late_locals.is_empty()
        && tail.iter().any(|stmt| {
            late_locals
                .iter()
                .any(|name| stmt_reads_var_recursive(stmt, name))
        })
}

/// Replace the `Goto` at `stmts[i]` with `tail` (when `pad_return`, append a bare `return`
/// unless the tail already ends terminated). Returns how many statements `i` now spans, so
/// callers can advance past the splice and adjust any tracked label index.
fn splice_tail_at(stmts: &mut Vec<Stmt>, i: usize, tail: &[Stmt], pad_return: bool) -> usize {
    let mut replacement = tail.to_vec();
    if pad_return && !block_ends_terminated(&replacement) {
        replacement.push(Stmt::Return(Vec::new()));
    }
    let replacement_len = replacement.len();
    stmts.splice(i..=i, replacement);
    replacement_len
}

fn replace_gotos_with_tail_return_before(
    root: &mut Vec<Stmt>,
    label_idx: &mut usize,
    label: &str,
    tail: &[Stmt],
) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < *label_idx {
        match &mut root[i] {
            Stmt::Goto(target) if target == label => {
                let replacement_len = splice_tail_at(root, i, tail, true);
                *label_idx += replacement_len - 1;
                i += replacement_len;
                changed = true;
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                changed |= replace_gotos_with_tail_return_in_block(then_body, label, tail);
                changed |= replace_gotos_with_tail_return_in_block(else_body, label, tail);
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }
    changed
}

fn replace_gotos_with_tail_return_in_block(
    stmts: &mut Vec<Stmt>,
    label: &str,
    tail: &[Stmt],
) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < stmts.len() {
        match &mut stmts[i] {
            Stmt::Goto(target) if target == label => {
                let replacement_len = splice_tail_at(stmts, i, tail, true);
                i += replacement_len;
                changed = true;
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                changed |= replace_gotos_with_tail_return_in_block(then_body, label, tail);
                changed |= replace_gotos_with_tail_return_in_block(else_body, label, tail);
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }
    changed
}

fn replace_gotos_with_terminal_tail_before(
    root: &mut Vec<Stmt>,
    label_idx: &mut usize,
    label: &str,
    tail: &[Stmt],
) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < *label_idx {
        match &mut root[i] {
            Stmt::Goto(target) if target == label => {
                let replacement_len = splice_tail_at(root, i, tail, false);
                *label_idx += replacement_len - 1;
                i += replacement_len;
                changed = true;
            }
            stmt => {
                changed |= replace_gotos_with_terminal_tail_in_stmt(stmt, label, tail);
                i += 1;
            }
        }
    }
    changed
}

fn replace_gotos_with_terminal_tail_in_stmt(stmt: &mut Stmt, label: &str, tail: &[Stmt]) -> bool {
    let mut changed = false;
    for_each_block_mut(stmt, |body| {
        changed |= replace_gotos_with_terminal_tail_in_block(body, label, tail);
    });
    changed
}

fn replace_gotos_with_terminal_tail_in_block(
    stmts: &mut Vec<Stmt>,
    label: &str,
    tail: &[Stmt],
) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < stmts.len() {
        match &mut stmts[i] {
            Stmt::Goto(target) if target == label => {
                let replacement_len = splice_tail_at(stmts, i, tail, false);
                i += replacement_len;
                changed = true;
            }
            stmt => {
                changed |= replace_gotos_with_terminal_tail_in_stmt(stmt, label, tail);
                i += 1;
            }
        }
    }
    changed
}

fn terminal_label(root: &[Stmt]) -> Option<(usize, String)> {
    match root {
        [.., Stmt::Label(label)] => Some((root.len() - 1, label.clone())),
        [.., Stmt::Label(label), Stmt::Return(values)] if values.is_empty() => {
            Some((root.len() - 2, label.clone()))
        }
        _ => None,
    }
}

fn replace_gotos_with_return(stmts: &mut [Stmt], target_label: &str) {
    for stmt in stmts {
        match stmt {
            Stmt::Goto(label) if label == target_label => {
                *stmt = Stmt::Return(Vec::new());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                replace_gotos_with_return(then_body, target_label);
                replace_gotos_with_return(else_body, target_label);
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. } => {
                replace_gotos_with_return(body, target_label);
            }
            _ => {}
        }
    }
}

/// Recover loop-carried callback transforms that compile as:
///
/// ```lua
/// current = callback(current)
/// if current ~= nil then continue end
/// return nil
/// ```
///
/// after temporary inlining has reduced the condition to `if callback(current) ~= nil`.
pub fn recover_loop_carried_call_updates(root: &mut [Stmt]) {
    for s in root.iter_mut() {
        for_each_block_mut(s, |b| recover_loop_carried_call_updates(b));
    }

    let mut i = 0;
    while i + 1 < root.len() {
        let Some((target, call)) = loop_carried_call_continue(&root[i]) else {
            i += 1;
            continue;
        };
        if !matches!(&root[i + 1], Stmt::Return(values) if values.len() == 1 && matches!(values[0], Expr::Nil))
        {
            i += 1;
            continue;
        }

        root[i] = Stmt::Assign {
            targets: vec![Expr::Var(target.clone())],
            values: vec![call],
        };
        root[i + 1] = Stmt::If {
            cond: Expr::Binary("==", Box::new(Expr::Var(target)), Box::new(Expr::Nil)),
            then_body: vec![Stmt::Return(vec![Expr::Nil])],
            else_body: Vec::new(),
        };
        i += 2;
    }
}

fn loop_carried_call_continue(stmt: &Stmt) -> Option<(String, Expr)> {
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = stmt
    else {
        return None;
    };
    if !else_body.is_empty() || !matches!(then_body.as_slice(), [Stmt::Continue]) {
        return None;
    }
    let Expr::Binary("~=", lhs, rhs) = cond else {
        return None;
    };
    if !matches!(rhs.as_ref(), Expr::Nil) {
        return None;
    }
    let (Expr::Call(_, args) | Expr::MethodCall(_, _, args)) = lhs.as_ref() else {
        return None;
    };
    let Some(Expr::Var(target)) = args.first() else {
        return None;
    };
    Some((target.clone(), *lhs.clone()))
}

/// Collapse repeat loops that were first recovered from `if cond then return ... end`
/// guards, so the condition moves back into `until` and temporary comparison registers can
/// be eliminated by the normal dead-store pass.
pub fn simplify_repeat_return_guards(root: &mut [Stmt]) {
    for s in root.iter_mut() {
        for_each_block_mut(s, |b| simplify_repeat_return_guards(b));
    }

    let mut i = 0;
    while i + 1 < root.len() {
        let return_values = match &root[i + 1] {
            Stmt::Return(values) => values.clone(),
            _ => {
                i += 1;
                continue;
            }
        };
        let Stmt::Repeat { body, cond } = &mut root[i] else {
            i += 1;
            continue;
        };

        let Some(cond_from_temp) = take_trailing_temp_repeat_condition(body, cond) else {
            i += 1;
            continue;
        };
        let guard_cond = take_trailing_return_guard(body, &return_values);
        *cond = match guard_cond {
            Some(guard) => Expr::Binary("or", Box::new(guard), Box::new(cond_from_temp)),
            None => cond_from_temp,
        };
        i += 1;
    }
}

fn take_trailing_temp_repeat_condition(body: &mut Vec<Stmt>, cond: &Expr) -> Option<Expr> {
    let (temp, normalized) = repeat_temp_condition(cond)?;
    let (assigned, value) = sole_var_assign(body.last()?)?;
    if assigned != temp {
        return None;
    }
    body.pop();
    Some(substitute_repeat_temp_condition(normalized, value))
}

enum RepeatTempCondition {
    TempLeOther(Expr),
    OtherLeTemp(Expr),
}

fn repeat_temp_condition(cond: &Expr) -> Option<(String, RepeatTempCondition)> {
    match cond {
        Expr::Binary("<=", lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (Expr::Var(temp), other) => Some((
                temp.clone(),
                RepeatTempCondition::TempLeOther(other.clone()),
            )),
            (other, Expr::Var(temp)) => Some((
                temp.clone(),
                RepeatTempCondition::OtherLeTemp(other.clone()),
            )),
            _ => None,
        },
        Expr::Binary(">=", lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (Expr::Var(temp), other) => Some((
                temp.clone(),
                RepeatTempCondition::OtherLeTemp(other.clone()),
            )),
            (other, Expr::Var(temp)) => Some((
                temp.clone(),
                RepeatTempCondition::TempLeOther(other.clone()),
            )),
            _ => None,
        },
        _ => None,
    }
}

fn substitute_repeat_temp_condition(kind: RepeatTempCondition, value: Expr) -> Expr {
    match kind {
        RepeatTempCondition::TempLeOther(other) => {
            Expr::Binary(">=", Box::new(other), Box::new(value))
        }
        RepeatTempCondition::OtherLeTemp(other) => {
            Expr::Binary("<=", Box::new(other), Box::new(value))
        }
    }
}

fn take_trailing_return_guard(body: &mut Vec<Stmt>, return_values: &[Expr]) -> Option<Expr> {
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = body.last()?
    else {
        return None;
    };
    if !else_body.is_empty() {
        return None;
    }
    if !matches!(then_body.as_slice(), [Stmt::Return(values)] if values == return_values) {
        return None;
    }
    let cond = cond.clone();
    body.pop();
    Some(cond)
}

/// Remove compiler/debug marker string assignments (`x = "BasePart"`) when the variable is
/// definitely overwritten or control leaves the block before any read.
pub fn remove_dead_literal_markers(root: &mut Vec<Stmt>) {
    remove_dead_literal_markers_with_continuation(root, &[]);
}

/// The statements that execute after the current block, as a chain of borrowed slices (innermost
/// first). This is what a literal marker must survive un-overwritten-and-unread to be dead. It is
/// only ever read, so it is passed by reference — never the per-statement deep clone it used to be.
fn remove_dead_literal_markers_with_continuation(root: &mut Vec<Stmt>, continuation: &[&[Stmt]]) {
    for i in 0..root.len() {
        // Only an `If` propagates this block's tail as its branches' continuation; loops use an
        // empty continuation and plain statements never recurse. `split_at_mut` lets us mutate the
        // `If` at index `i` while borrowing the tail `root[i+1..]` as the child continuation —
        // exactly the two borrows the old per-statement `.to_vec()` deep clone worked around.
        if matches!(root[i], Stmt::If { .. }) {
            let (head, tail) = root.split_at_mut(i + 1);
            let tail: &[Stmt] = tail;
            let mut child: Vec<&[Stmt]> = Vec::with_capacity(continuation.len() + 1);
            child.push(tail);
            child.extend_from_slice(continuation);
            if let Stmt::If {
                then_body,
                else_body,
                ..
            } = &mut head[i]
            {
                remove_dead_literal_markers_with_continuation(then_body, &child);
                remove_dead_literal_markers_with_continuation(else_body, &child);
            }
        } else if let Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } = &mut root[i]
        {
            remove_dead_literal_markers_with_continuation(body, &[]);
        }
    }

    let mut i = 0;
    while i < root.len() {
        let Some((name, Expr::Str(_))) = sole_var_assign(&root[i]) else {
            i += 1;
            continue;
        };
        if literal_marker_dead_before_read(&root[i + 1..], continuation, &name) {
            root.remove(i);
        } else {
            i += 1;
        }
    }
}

fn literal_marker_dead_before_read(stmts: &[Stmt], continuation: &[&[Stmt]], name: &str) -> bool {
    let cont = continuation.iter().flat_map(|s| s.iter());
    match marker_sequence_flow(stmts.iter().chain(cont), name) {
        MarkerFlow::Read | MarkerFlow::Open => false,
        MarkerFlow::Killed => true,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MarkerFlow {
    Read,
    Killed,
    Open,
}

fn marker_sequence_flow<'a>(stmts: impl Iterator<Item = &'a Stmt>, name: &str) -> MarkerFlow {
    for stmt in stmts {
        match marker_stmt_flow(stmt, name) {
            MarkerFlow::Open => {}
            other => return other,
        }
    }
    MarkerFlow::Open
}

fn marker_block_flow(stmts: &[Stmt], name: &str) -> MarkerFlow {
    marker_sequence_flow(stmts.iter(), name)
}

fn marker_stmt_flow(stmt: &Stmt, name: &str) -> MarkerFlow {
    if stmt_shallow_reads_var(stmt, name) {
        return MarkerFlow::Read;
    }
    if directly_writes_var(stmt, name)
        || matches!(
            stmt,
            Stmt::Return(_) | Stmt::Break | Stmt::Continue | Stmt::Goto(_)
        )
    {
        return MarkerFlow::Killed;
    }

    match stmt {
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            let then_flow = marker_block_flow(then_body, name);
            let else_flow = if else_body.is_empty() {
                MarkerFlow::Open
            } else {
                marker_block_flow(else_body, name)
            };
            if then_flow == MarkerFlow::Read || else_flow == MarkerFlow::Read {
                MarkerFlow::Read
            } else if then_flow == MarkerFlow::Killed && else_flow == MarkerFlow::Killed {
                MarkerFlow::Killed
            } else {
                MarkerFlow::Open
            }
        }
        Stmt::While { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => {
            if marker_block_flow(body, name) == MarkerFlow::Read {
                MarkerFlow::Read
            } else {
                MarkerFlow::Open
            }
        }
        Stmt::Repeat { body, .. } => marker_block_flow(body, name),
        _ => MarkerFlow::Open,
    }
}

fn stmt_shallow_reads_var(stmt: &Stmt, name: &str) -> bool {
    let mut counts = BTreeMap::new();
    match stmt {
        Stmt::Local { values, .. } => values.iter().for_each(|e| add_reads(e, &mut counts)),
        Stmt::Assign { targets, values } => {
            for target in targets {
                if !matches!(target, Expr::Var(_)) {
                    add_reads(target, &mut counts);
                }
            }
            values.iter().for_each(|e| add_reads(e, &mut counts));
        }
        Stmt::Call(e) => add_reads(e, &mut counts),
        Stmt::Return(values) => values.iter().for_each(|e| add_reads(e, &mut counts)),
        Stmt::If { cond, .. } | Stmt::While { cond, .. } | Stmt::Repeat { cond, .. } => {
            add_reads(cond, &mut counts);
        }
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
        Stmt::Break | Stmt::Continue | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => {}
    }
    counts.get(name).copied().unwrap_or(0) > 0
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

fn write_depends_on_between(
    root: &[Stmt],
    write_idx: usize,
    init_idx: usize,
    key: &Expr,
    val: &Expr,
) -> bool {
    let mut read_vars = reads_of_expr(key);
    read_vars.extend(reads_of_expr(val));

    for stmt in root.iter().take(write_idx).skip(init_idx + 1) {
        let written = writes_of_stmt(stmt);
        if !written.is_disjoint(&read_vars) {
            return true;
        }
    }
    false
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
        let Some((t, fields)) = table_init(&root[i]) else {
            i += 1;
            continue;
        };

        let mut writes = Vec::new();
        let mut stop_idx = root.len();

        for (k, stmt) in root.iter().enumerate().skip(i + 1) {
            let mut is_write = false;
            if let Stmt::Assign { targets, values } = stmt {
                if targets.len() == 1 && values.len() == 1 {
                    match &targets[0] {
                        Expr::Index(base, key) => {
                            if let Expr::Var(base_name) = base.as_ref() {
                                if base_name == &t
                                    && !expr_reads_var(key, &t)
                                    && !expr_reads_var(&values[0], &t)
                                {
                                    if write_depends_on_between(root, k, i, key, &values[0]) {
                                        stop_idx = k;
                                        break;
                                    }
                                    writes.push((
                                        k,
                                        TableField::Keyed(*key.clone(), values[0].clone()),
                                    ));
                                    is_write = true;
                                }
                            }
                        }
                        Expr::Field(base, field) => {
                            if let Expr::Var(base_name) = base.as_ref() {
                                if base_name == &t && !expr_reads_var(&values[0], &t) {
                                    if write_depends_on_between(root, k, i, &Expr::Nil, &values[0])
                                    {
                                        stop_idx = k;
                                        break;
                                    }
                                    writes.push((
                                        k,
                                        TableField::Named(field.clone(), values[0].clone()),
                                    ));
                                    is_write = true;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }

            if is_write {
                continue;
            }

            if is_escape_or_unsafe_read(stmt, &t) || is_control_flow(stmt) {
                stop_idx = k;
                break;
            }
        }

        writes.retain(|(idx, _)| *idx < stop_idx);

        if writes.is_empty() {
            i += 1;
            continue;
        }

        let mut uses = BTreeMap::new();
        for stmt in root.iter().skip(i + 1) {
            count_uses_stmt(stmt, &mut uses);
        }

        let mut inline_map = BTreeMap::new();
        let mut def_indices = BTreeSet::new();

        for (k, stmt) in root.iter().enumerate().take(stop_idx).skip(i + 1) {
            if let Some((var_name, def_val)) = sole_var_assign(stmt) {
                if uses.get(&var_name).copied().unwrap_or(0) == 1 && is_pure(&def_val) {
                    let read_in_writes = writes.iter().any(|(_, field)| match field {
                        TableField::Item(e) => expr_reads_var(e, &var_name),
                        TableField::Named(_, e) => expr_reads_var(e, &var_name),
                        TableField::Keyed(k, v) => {
                            expr_reads_var(k, &var_name) || expr_reads_var(v, &var_name)
                        }
                    });
                    if read_in_writes {
                        inline_map.insert(var_name, def_val);
                        def_indices.insert(k);
                    }
                }
            }
        }

        for (_, field) in writes.iter_mut() {
            match field {
                TableField::Item(e) => {
                    replace_inline_expr(e, &inline_map);
                }
                TableField::Named(_, e) => {
                    replace_inline_expr(e, &inline_map);
                }
                TableField::Keyed(k, v) => {
                    replace_inline_expr(k, &inline_map);
                    replace_inline_expr(v, &inline_map);
                }
            }
        }

        let mut final_fields = fields.clone();
        let mut array_next = 1 + fields
            .iter()
            .filter(|f| matches!(f, TableField::Item(_)))
            .count();

        for (_, field) in writes.iter() {
            let normalized_field = match field {
                TableField::Keyed(Expr::Num(n), val) if n == &array_next.to_string() => {
                    array_next += 1;
                    TableField::Item(val.clone())
                }
                other => other.clone(),
            };
            final_fields.push(normalized_field);
        }

        replace_table_init(&mut root[i], final_fields);

        let write_indices: BTreeSet<usize> = writes.iter().map(|(idx, _)| *idx).collect();
        let indices_to_remove: BTreeSet<usize> =
            write_indices.union(&def_indices).cloned().collect();

        for idx in indices_to_remove.into_iter().rev() {
            root.remove(idx);
        }

        i = 0;
    }
}

fn expr_reads_var(e: &Expr, var: &str) -> bool {
    reads_of_expr(e).contains(var)
}

fn stmt_reads_var_recursive(s: &Stmt, t: &str) -> bool {
    if stmt_reads_var(s, t) {
        return true;
    }
    let mut found = false;
    for_each_block(s, |b| {
        if !found {
            found = b.iter().any(|st| stmt_reads_var_recursive(st, t));
        }
    });
    found
}

fn is_escape_or_unsafe_read(stmt: &Stmt, t: &str) -> bool {
    if let Stmt::Assign { targets, values } = stmt {
        if targets.len() == 1 && values.len() == 1 {
            match &targets[0] {
                Expr::Index(base, key) => {
                    if let Expr::Var(base_name) = base.as_ref() {
                        if base_name == t {
                            return expr_reads_var(key, t) || expr_reads_var(&values[0], t);
                        }
                    }
                }
                Expr::Field(base, _) => {
                    if let Expr::Var(base_name) = base.as_ref() {
                        if base_name == t {
                            return expr_reads_var(&values[0], t);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    stmt_reads_var_recursive(stmt, t)
}

fn replace_inline_expr(e: &mut Expr, inline_map: &BTreeMap<String, Expr>) {
    match e {
        Expr::Var(n) => {
            if let Some(val) = inline_map.get(n) {
                *e = val.clone();
            }
        }
        Expr::Index(b, k) => {
            replace_inline_expr(b, inline_map);
            replace_inline_expr(k, inline_map);
        }
        Expr::Field(b, _) => {
            replace_inline_expr(b, inline_map);
        }
        Expr::Call(c, args) => {
            replace_inline_expr(c, inline_map);
            for arg in args {
                replace_inline_expr(arg, inline_map);
            }
        }
        Expr::MethodCall(o, _, args) => {
            replace_inline_expr(o, inline_map);
            for arg in args {
                replace_inline_expr(arg, inline_map);
            }
        }
        Expr::Unary(_, a) => {
            replace_inline_expr(a, inline_map);
        }
        Expr::Binary(_, a, b) => {
            replace_inline_expr(a, inline_map);
            replace_inline_expr(b, inline_map);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(v) => replace_inline_expr(v, inline_map),
                    TableField::Named(_, v) => replace_inline_expr(v, inline_map),
                    TableField::Keyed(k, v) => {
                        replace_inline_expr(k, inline_map);
                        replace_inline_expr(v, inline_map);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Inline temporary table literals that are immediately stored into another table:
///
/// ```lua
/// tmp = { ... }
/// parent[key] = tmp
/// ```
///
/// becomes `parent[key] = { ... }` when `tmp` is not read again before it is overwritten.
/// This removes compiler register temporaries from nested table construction without
/// changing shared-table behavior.
pub fn inline_table_literal_fill_temps(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, inline_table_literal_fill_temps);
    }

    let mut i = 0;
    while i + 1 < root.len() {
        let Some((name, fields)) = sole_table_literal_assign(&root[i]) else {
            i += 1;
            continue;
        };
        if !assigns_single_var_value(&root[i + 1], &name) {
            i += 1;
            continue;
        }
        if stmt_reads_var_in_assignment_target(&root[i + 1], &name) {
            i += 1;
            continue;
        }
        if read_before_next_write(&root[i + 2..], &name) {
            i += 1;
            continue;
        }

        if let Stmt::Assign { values, .. } = &mut root[i + 1] {
            values[0] = Expr::Table(fields);
        }
        root.remove(i);
    }
}

fn sole_table_literal_assign(stmt: &Stmt) -> Option<(String, Vec<TableField>)> {
    let (name, value) = sole_var_assign(stmt)?;
    match value {
        Expr::Table(fields) => Some((name, fields)),
        _ => None,
    }
}

fn assigns_single_var_value(stmt: &Stmt, name: &str) -> bool {
    matches!(
        stmt,
        Stmt::Assign { values, .. }
            if values.len() == 1 && matches!(&values[0], Expr::Var(value) if value == name)
    )
}

fn read_before_next_write(stmts: &[Stmt], name: &str) -> bool {
    for stmt in stmts {
        if directly_writes_var(stmt, name) {
            return false;
        }
        if stmt_reads_var(stmt, name) {
            return true;
        }
        if is_control_flow(stmt) {
            return true;
        }
    }
    false
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
    loop {
        let mut changed = false;
        let mut i = 0;
        while i < root.len() {
            if i + 2 < root.len() {
                if let Some(rewritten) = match_and_or(&root[i], &root[i + 1], &root[i + 2]) {
                    root[i] = rewritten;
                    root.remove(i + 2);
                    root.remove(i + 1);
                    changed = true;
                    continue;
                }
                if let Some(rewritten) =
                    match_guard_label_and_or(&root[i], &root[i + 1], &root[i + 2])
                {
                    root[i] = rewritten;
                    root.remove(i + 2);
                    root.remove(i + 1);
                    changed = true;
                    continue;
                }
            }
            if i + 1 < root.len() {
                if let Some(rewritten) = match_missing_label_and_or(root, i) {
                    root[i] = rewritten;
                    root.remove(i + 1);
                    changed = true;
                    continue;
                }
            }
            i += 1;
        }
        if !changed {
            break;
        }
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

fn match_missing_label_and_or(root: &[Stmt], i: usize) -> Option<Stmt> {
    // Reduced `(a and a.x) or fallback` shape after the join label has already been
    // removed. Keep this narrow: the inner condition must be a field matching the local
    // being initialized.
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = &root[i]
    else {
        return None;
    };
    if !else_body.is_empty() || then_body.len() != 1 {
        return None;
    }
    let Stmt::If {
        cond: inner_cond,
        then_body: inner_then,
        else_body: inner_else,
    } = &then_body[0]
    else {
        return None;
    };
    if !inner_else.is_empty() || inner_then.len() != 1 {
        return None;
    }
    let Stmt::Goto(label) = &inner_then[0] else {
        return None;
    };
    if label_exists(root, label) {
        return None;
    }

    let (target, fallback, is_local) = match &root[i + 1] {
        Stmt::Local { names, values } if names.len() == 1 && values.len() == 1 => {
            (names[0].clone(), values[0].clone(), true)
        }
        Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            let Expr::Var(name) = &targets[0] else {
                return None;
            };
            (name.clone(), values[0].clone(), false)
        }
        _ => return None,
    };
    if !expr_field_matches_name(inner_cond, &target) {
        return None;
    }

    let value = Expr::Binary(
        "or",
        Box::new(Expr::Binary(
            "and",
            Box::new(cond.clone()),
            Box::new(inner_cond.clone()),
        )),
        Box::new(fallback),
    );
    if is_local {
        Some(Stmt::Local {
            names: vec![target],
            values: vec![value],
        })
    } else {
        Some(Stmt::Assign {
            targets: vec![Expr::Var(target)],
            values: vec![value],
        })
    }
}

fn match_guard_label_and_or(s0: &Stmt, s1: &Stmt, s2: &Stmt) -> Option<Stmt> {
    let (label, target, is_local, value) = guard_and_or_parts(s0, s1)?;
    match s2 {
        Stmt::Label(name) if *name == label => {
            if is_local {
                Some(Stmt::Local {
                    names: vec![target],
                    values: vec![value],
                })
            } else {
                Some(Stmt::Assign {
                    targets: vec![Expr::Var(target)],
                    values: vec![value],
                })
            }
        }
        _ => None,
    }
}

fn guard_and_or_parts(s0: &Stmt, s1: &Stmt) -> Option<(String, String, bool, Expr)> {
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = s0
    else {
        return None;
    };
    if !else_body.is_empty() || then_body.len() != 1 {
        return None;
    }
    let Stmt::If {
        cond: inner_cond,
        then_body: inner_then,
        else_body: inner_else,
    } = &then_body[0]
    else {
        return None;
    };
    if !inner_else.is_empty() || inner_then.len() != 1 {
        return None;
    }
    let Stmt::Goto(label) = &inner_then[0] else {
        return None;
    };

    let (target, fallback, is_local) = match s1 {
        Stmt::Local { names, values } if names.len() == 1 && values.len() == 1 => {
            (names[0].clone(), values[0].clone(), true)
        }
        Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            let Expr::Var(name) = &targets[0] else {
                return None;
            };
            (name.clone(), values[0].clone(), false)
        }
        _ => return None,
    };
    if !expr_field_matches_name(inner_cond, &target) {
        return None;
    }

    let value = Expr::Binary(
        "or",
        Box::new(Expr::Binary(
            "and",
            Box::new(cond.clone()),
            Box::new(inner_cond.clone()),
        )),
        Box::new(fallback.clone()),
    );
    Some((label.clone(), target, is_local, value))
}

fn expr_field_matches_name(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Field(_, field) => field == name,
        Expr::Index(_, key) => matches!(key.as_ref(), Expr::Str(s) if s.trim_matches('"') == name),
        _ => false,
    }
}

fn label_exists(stmts: &[Stmt], label: &str) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Label(name) => name == label,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => label_exists(then_body, label) || label_exists(else_body, label),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => label_exists(body, label),
        _ => false,
    })
}

fn label_names(stmts: &[Stmt]) -> BTreeSet<String> {
    let mut labels = BTreeSet::new();
    fn collect(stmts: &[Stmt], labels: &mut BTreeSet<String>) {
        for stmt in stmts {
            match stmt {
                Stmt::Label(name) => {
                    labels.insert(name.clone());
                }
                _ => {
                    for_each_block(stmt, |body| collect(body, labels));
                }
            }
        }
    }
    collect(stmts, &mut labels);
    labels
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
    while recover_goto_into_if_gate_once(root)
        || recover_goto_into_later_if_chain_once(root)
        || recover_goto_into_later_if_gate_once(root)
        || recover_goto_into_if_chain_once(root)
        || recover_nested_goto_to_later_label_once(root)
    {}
}

/// Recover top-tested loops that survived the bytecode structurer as a label plus a nested
/// guard ending in a back-goto:
///
/// ```lua
/// ::L::
/// if a then
///     if b then
///         body()
///         goto L
///     end
/// end
/// ```
///
/// becomes `while a and b do body() end`. Every false guard path falls through to the same
/// loop exit, and the only goto to the label is the final back-edge, so this is a direct
/// structured form of the same control flow.
pub fn recover_top_test_while_gotos(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_top_test_while_gotos);
    }
    while recover_top_test_while_once(root) {}
}

/// General fallback loop recovery: turn any remaining backward-goto loop into
/// `while true do … end`. A label that is the target of a *backward* goto (one appearing
/// after the label, in the same block) is a loop header. The body spans from just after the
/// header to the last statement containing a back-edge; back-edges to the header become
/// `continue`, a bare unconditional trailing back-edge is dropped (it is the natural loop
/// edge), and the implicit fall-through past the body — which in goto form exits the loop —
/// becomes an explicit `break`. A single forward jump to a label after the loop becomes a
/// `break` too. The specialized passes recover prettier `while <cond>` / `repeat` forms
/// first; this catches whatever they leave behind (loops whose only exits are `return`s or
/// nested conditional back-edges) so no `goto`/label survives.
pub fn recover_natural_loops(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_natural_loops);
    }
    while recover_natural_loop_once(root) {}
}

fn recover_natural_loop_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let Stmt::Label(label) = &root[i] else {
            continue;
        };
        let label = label.clone();

        // There must be at least one back-edge (a `goto` after the header) and no forward
        // entry (a `goto` before it), so the region from the header onward is a clean loop.
        if count_gotos_named(&root[i + 1..], &label) == 0 {
            continue;
        }
        if count_gotos_named(&root[..i], &label) != 0 {
            continue;
        }

        // The loop body ends at the last top-level statement that still holds a back-edge.
        let Some(loop_end) = (i + 1..root.len())
            .rev()
            .find(|&j| count_gotos_named_stmt(&root[j], &label) > 0)
        else {
            continue;
        };

        let mut body: Vec<Stmt> = root[i + 1..=loop_end].to_vec();

        // A back-edge inside a *nested* loop would have to `continue` the outer loop, which a
        // single `continue` cannot express — leave it unstructured.
        if has_goto_in_nested_loop(&body, &label, false) {
            continue;
        }

        // Residual forward jumps (after the continue rewrite) must all target one label that
        // sits after the loop — a `break`. Anything else we cannot structure cleanly.
        let mut exits = BTreeSet::new();
        for s in &body {
            collect_goto_names(s, &mut exits);
        }
        exits.remove(&label);
        let exit_label = match exits.len() {
            0 => None,
            1 => {
                let exit = exits.into_iter().next().unwrap();
                let after = (loop_end + 1..root.len())
                    .any(|j| matches!(&root[j], Stmt::Label(l) if l == &exit));
                if !after || has_goto_in_nested_loop(&body, &exit, false) {
                    continue;
                }
                Some(exit)
            }
            _ => continue,
        };

        // Drop a bare unconditional trailing back-edge (the natural loop edge). Otherwise the
        // body can fall off the end, which in goto form exits — make that an explicit break.
        let trailing_backedge = matches!(body.last(), Some(Stmt::Goto(l)) if l == &label);
        if trailing_backedge {
            body.pop();
        }
        replace_gotos_with_continue(&mut body, &label);
        if let Some(exit) = &exit_label {
            replace_gotos_with_break(&mut body, exit);
        }
        // Represent the implicit fall-through exit as an explicit `break` — but only when the
        // body can actually fall off its end. If it already ends in a terminator (`return` /
        // `break` / `continue`), control never reaches past it, and appending `break` after a
        // `return` would not even be valid Luau (a `return` must end its block).
        let ends_terminated = matches!(
            body.last(),
            Some(Stmt::Return(_) | Stmt::Break | Stmt::Continue)
        );
        if !trailing_backedge && !ends_terminated {
            body.push(Stmt::Break);
        }

        if contains_label_or_goto(&body) {
            continue;
        }

        root[i] = Stmt::While {
            cond: Expr::Bool(true),
            body,
        };
        root.drain(i + 1..=loop_end);

        // Drop the exit label if the recovered breaks were its only references.
        if let Some(exit) = exit_label {
            if count_gotos_named(root, &exit) == 0 {
                if let Some(pos) = root
                    .iter()
                    .position(|s| matches!(s, Stmt::Label(l) if l == &exit))
                {
                    root.remove(pos);
                }
            }
        }
        return true;
    }
    false
}

/// Merge a leading `if <cond> then break end` guard into the enclosing while condition.
/// Luau often emits `while a do if not b then break end ... end` for `while a and b do`.
pub fn merge_leading_while_break_guards(root: &mut [Stmt]) {
    for s in root.iter_mut() {
        for_each_block_mut(s, |body| merge_leading_while_break_guards(body));
    }

    for stmt in root.iter_mut() {
        let Stmt::While { cond, body } = stmt else {
            continue;
        };
        while let Some(first) = body.first() {
            let Stmt::If {
                cond: break_cond,
                then_body,
                else_body,
            } = first
            else {
                break;
            };
            if !else_body.is_empty() || !matches!(then_body.as_slice(), [Stmt::Break]) {
                break;
            }
            *cond = Expr::Binary(
                "and",
                Box::new(cond.clone()),
                Box::new(negate_condition(break_cond.clone())),
            );
            body.remove(0);
        }
    }
}

fn recover_top_test_while_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        let Stmt::Label(label) = &root[i] else {
            i += 1;
            continue;
        };
        let label = label.clone();
        if count_gotos_named(root, &label) != 1 {
            i += 1;
            continue;
        }

        let Some((cond, mut body)) = top_test_while_body(&root[i + 1], &label) else {
            i += 1;
            continue;
        };

        // The body's only residual unstructured control flow may be forward `goto <exit>`
        // jumps that are really `break`s, where <exit> is the label immediately following
        // this loop. Convert those before deciding the loop is recoverable; anything else
        // (internal labels, jumps elsewhere) means we can't structure it cleanly.
        let mut exit_label = None;
        if contains_label_or_goto(&body) {
            let Some(exit) = sole_forward_exit_label(&body, root, i + 1) else {
                i += 1;
                continue;
            };
            // A `goto <exit>` buried inside a *nested* loop would have to break out of two
            // loops at once, which a single `break` cannot express — leave it unstructured.
            if has_goto_in_nested_loop(&body, &exit, false) {
                i += 1;
                continue;
            }
            replace_gotos_with_break(&mut body, &exit);
            if contains_label_or_goto(&body) {
                i += 1;
                continue;
            }
            exit_label = Some(exit);
        }

        root[i] = Stmt::While { cond, body };
        root.remove(i + 1);

        // Drop the exit label if the recovered `break`s were its only references.
        if let Some(exit) = exit_label {
            if count_gotos_named(root, &exit) == 0 {
                if let Some(pos) = root
                    .iter()
                    .position(|s| matches!(s, Stmt::Label(l) if l == &exit))
                {
                    root.remove(pos);
                }
            }
        }
        return true;
    }
    false
}

/// If every `goto` in `body` targets a single label, and that label is defined in `root` at
/// some index strictly after `loop_idx` (so it is a forward jump *out* of the loop), return
/// it. Returns `None` when `body` defines its own labels or jumps to more than one place —
/// cases a single `break` cannot capture.
fn sole_forward_exit_label(body: &[Stmt], root: &[Stmt], loop_idx: usize) -> Option<String> {
    let mut targets = BTreeSet::new();
    for stmt in body {
        collect_goto_names(stmt, &mut targets);
    }
    if targets.len() != 1 {
        return None;
    }
    let exit = targets.into_iter().next().unwrap();
    let defined_after = root
        .iter()
        .enumerate()
        .any(|(idx, s)| idx > loop_idx && matches!(s, Stmt::Label(l) if l == &exit));
    defined_after.then_some(exit)
}

fn top_test_while_body(stmt: &Stmt, label: &str) -> Option<(Expr, Vec<Stmt>)> {
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

    let (guard, body) = loop_back_body(then_body, label)?;
    Some(match guard {
        Some(extra) => (
            Expr::Binary("and", Box::new(cond.clone()), Box::new(extra)),
            body,
        ),
        None => (cond.clone(), body),
    })
}

fn loop_back_body(stmts: &[Stmt], label: &str) -> Option<(Option<Expr>, Vec<Stmt>)> {
    match stmts {
        [Stmt::If {
            cond,
            then_body,
            else_body,
        }] if else_body.is_empty() => {
            let (inner_cond, body) = loop_back_body(then_body, label)?;
            let cond = match inner_cond {
                Some(inner) => Expr::Binary("and", Box::new(cond.clone()), Box::new(inner)),
                None => cond.clone(),
            };
            Some((Some(cond), body))
        }
        _ => {
            let (last, prefix) = stmts.split_last()?;
            if !matches!(last, Stmt::Goto(target) if target == label) {
                return None;
            }
            Some((None, prefix.to_vec()))
        }
    }
}

fn recover_goto_into_if_gate_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        let Some((goto_cond, label)) = conditional_goto_expr(&root[i], None) else {
            i += 1;
            continue;
        };
        let guard_gotos = count_gotos_named_stmt(&root[i], &label);
        if guard_gotos == 0 {
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
            || !label_names(&then_body[1..]).is_empty()
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

fn recover_goto_into_if_chain_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        let Some((entry_cond, label)) = conditional_goto_expr(&root[i], None) else {
            i += 1;
            continue;
        };
        let guard_gotos = count_gotos_named_stmt(&root[i], &label);
        if guard_gotos == 0 {
            i += 1;
            continue;
        }
        if has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false) {
            i += 1;
            continue;
        }

        let Some(transformed) =
            force_entry_into_labeled_if(root[i + 1].clone(), &label, &entry_cond)
        else {
            i += 1;
            continue;
        };
        if contains_label_or_goto(std::slice::from_ref(&transformed)) {
            i += 1;
            continue;
        }

        root[i + 1] = transformed;
        root.remove(i);
        return true;
    }
    false
}

fn recover_goto_into_later_if_chain_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 2 < root.len() {
        let Some((entry_cond, label)) = conditional_goto_expr(&root[i], None) else {
            i += 1;
            continue;
        };
        let guard_gotos = count_gotos_named_stmt(&root[i], &label);
        if guard_gotos == 0 {
            i += 1;
            continue;
        }
        if has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false) {
            i += 1;
            continue;
        }
        if count_gotos_named(root, &label) != guard_gotos {
            i += 1;
            continue;
        }

        let search_end = root.len().min(i + 48);
        for target_idx in i + 2..search_end {
            if !block_contains_label(std::slice::from_ref(&root[target_idx]), &label) {
                continue;
            }
            let prefix = root[i + 1..target_idx].to_vec();
            if prefix.is_empty()
                || prefix.len() > 32
                || contains_label_or_goto(&prefix)
                || block_ends_terminated(&prefix)
            {
                continue;
            }
            if !direct_local_scope_safe(&prefix, &root[target_idx + 1..]) {
                continue;
            }

            let Some((target_body, target_without_labels)) =
                duplicate_labeled_if_chain_body_and_strip(root[target_idx].clone(), &label)
            else {
                continue;
            };
            if target_body.is_empty()
                || contains_label_or_goto(&target_body)
                || contains_label_or_goto(std::slice::from_ref(&target_without_labels))
            {
                continue;
            }

            let mut else_body = prefix;
            else_body.push(target_without_labels);
            root[target_idx] = Stmt::If {
                cond: entry_cond,
                then_body: target_body,
                else_body,
            };
            root.drain(i..target_idx);
            return true;
        }
        i += 1;
    }
    false
}

fn recover_goto_into_later_if_gate_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 2 < root.len() {
        let Some((entry_cond, label)) = conditional_goto_expr(&root[i], None) else {
            i += 1;
            continue;
        };
        let guard_gotos = count_gotos_named_stmt(&root[i], &label);
        if guard_gotos == 0 {
            i += 1;
            continue;
        }
        if has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false) {
            i += 1;
            continue;
        }

        let search_end = root.len().min(i + 48);
        for target_idx in i + 2..search_end {
            if !block_contains_label(std::slice::from_ref(&root[target_idx]), &label) {
                continue;
            }
            let prefix = root[i + 1..target_idx].to_vec();
            if prefix.is_empty()
                || prefix.len() > 32
                || contains_label_or_goto(&prefix)
                || block_ends_terminated(&prefix)
            {
                continue;
            }
            let region_gotos = count_gotos_named(&root[i..=target_idx], &label);
            if region_gotos != guard_gotos
                || (count_gotos_named(root, &label) != region_gotos
                    && count_labels_named_outside(root, &label, i, target_idx) == 0)
            {
                continue;
            }

            let Some((target_body, target_without_label)) =
                split_tail_label_continuation(root[target_idx].clone(), &label)
            else {
                continue;
            };
            if target_body.is_empty()
                || contains_label_or_goto(&target_body)
                || contains_label_or_goto(std::slice::from_ref(&target_without_label))
            {
                continue;
            }

            let mut else_body = prefix;
            else_body.push(target_without_label);
            root.splice(
                i..=target_idx,
                [Stmt::If {
                    cond: entry_cond,
                    then_body: target_body,
                    else_body,
                }],
            );
            return true;
        }

        i += 1;
    }
    false
}

fn recover_nested_goto_to_later_label_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let labels = goto_names_in_stmt(&root[i]);
        for label in labels {
            let goto_count = count_gotos_named_stmt(&root[i], &label);
            if goto_count == 0
                || has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false)
            {
                continue;
            }

            let search_end = root.len().min(i + 48);
            for target_idx in i + 1..search_end {
                if !block_contains_label(std::slice::from_ref(&root[target_idx]), &label) {
                    continue;
                }
                let mut normal_continuation = root[i + 1..target_idx].to_vec();
                let region_gotos = count_gotos_named(&root[i..=target_idx], &label);
                if normal_continuation.len() > 32
                    || count_gotos_named(&normal_continuation, &label) != 0
                    || block_contains_label(&normal_continuation, &label)
                    || block_ends_terminated(&normal_continuation)
                    || region_gotos != goto_count
                    || (count_gotos_named(root, &label) != region_gotos
                        && count_labels_named_outside(root, &label, i, target_idx) == 0)
                {
                    continue;
                }

                let Some((target_body, target_without_label)) =
                    split_later_label_target(root[target_idx].clone(), &label)
                else {
                    continue;
                };
                if count_gotos_named(&target_body, &label) != 0
                    || block_contains_label(&target_body, &label)
                    || target_without_label.as_ref().is_some_and(|stmt| {
                        count_gotos_named_stmt(stmt, &label) != 0
                            || block_contains_label(std::slice::from_ref(stmt), &label)
                    })
                {
                    continue;
                }
                if let Some(target_without_label) = target_without_label {
                    normal_continuation.push(target_without_label);
                }
                widen_locals_read_after_join(&mut normal_continuation, &root[target_idx + 1..]);
                if !direct_local_scope_safe(&normal_continuation, &root[target_idx + 1..]) {
                    continue;
                }

                let Some(transformed) = route_gotos_to_target_body(
                    vec![root[i].clone()],
                    &label,
                    target_body,
                    normal_continuation,
                ) else {
                    continue;
                };
                if count_gotos_named(&transformed, &label) != 0
                    || block_contains_label(&transformed, &label)
                {
                    continue;
                }

                root.splice(i..=target_idx, transformed);
                return true;
            }
        }
    }
    false
}

fn split_later_label_target(stmt: Stmt, label: &str) -> Option<(Vec<Stmt>, Option<Stmt>)> {
    match stmt {
        Stmt::Label(name) if name == label => Some((Vec::new(), None)),
        other => {
            let (target, without_label) = split_tail_label_continuation(other, label)?;
            Some((target, Some(without_label)))
        }
    }
}

fn split_tail_label_continuation(stmt: Stmt, label: &str) -> Option<(Vec<Stmt>, Stmt)> {
    match stmt {
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            if block_contains_label(&then_body, label) {
                if block_contains_label(&else_body, label) {
                    return None;
                }
                let (target, then_body) = split_tail_label_continuation_block(then_body, label)?;
                return Some((
                    target,
                    Stmt::If {
                        cond,
                        then_body,
                        else_body,
                    },
                ));
            }
            if block_contains_label(&else_body, label) {
                let (target, else_body) = split_tail_label_continuation_block(else_body, label)?;
                return Some((
                    target,
                    Stmt::If {
                        cond,
                        then_body,
                        else_body,
                    },
                ));
            }
            None
        }
        _ => None,
    }
}

fn split_tail_label_continuation_block(
    mut stmts: Vec<Stmt>,
    label: &str,
) -> Option<(Vec<Stmt>, Vec<Stmt>)> {
    for idx in 0..stmts.len() {
        match &stmts[idx] {
            Stmt::Label(name) if name == label => {
                let target = stmts[idx + 1..].to_vec();
                stmts.remove(idx);
                return Some((target, stmts));
            }
            stmt if block_contains_label(std::slice::from_ref(stmt), label) => {
                if idx + 1 != stmts.len() {
                    return None;
                }
                let (target, replacement) =
                    split_tail_label_continuation(stmts.remove(idx), label)?;
                stmts.push(replacement);
                return Some((target, stmts));
            }
            _ => {}
        }
    }
    None
}

fn force_entry_into_labeled_if(stmt: Stmt, label: &str, entry_cond: &Expr) -> Option<Stmt> {
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = stmt
    else {
        return None;
    };
    if !block_contains_label(&then_body, label) {
        return None;
    }

    Some(Stmt::If {
        cond: Expr::Binary("or", Box::new(entry_cond.clone()), Box::new(cond)),
        then_body: force_entry_into_labeled_block(then_body, label, entry_cond, true)?,
        else_body: force_entry_into_labeled_block(else_body, label, entry_cond, false)?,
    })
}

fn force_entry_into_labeled_block(
    stmts: Vec<Stmt>,
    label: &str,
    entry_cond: &Expr,
    route_entry: bool,
) -> Option<Vec<Stmt>> {
    let mut out = Vec::new();
    for stmt in stmts {
        match stmt {
            Stmt::Label(name) if name == label => {}
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                let then_has = block_contains_label(&then_body, label);
                let else_has = block_contains_label(&else_body, label);
                let cond = if route_entry && then_has {
                    Expr::Binary("or", Box::new(entry_cond.clone()), Box::new(cond))
                } else {
                    cond
                };
                if route_entry && else_has && !then_has {
                    return None;
                }
                out.push(Stmt::If {
                    cond,
                    then_body: force_entry_into_labeled_block(
                        then_body,
                        label,
                        entry_cond,
                        route_entry && then_has,
                    )?,
                    else_body: force_entry_into_labeled_block(else_body, label, entry_cond, false)?,
                });
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. }
                if block_contains_label(&body, label) =>
            {
                return None;
            }
            other => out.push(other),
        }
    }
    Some(out)
}

fn duplicate_labeled_if_chain_body_and_strip(stmt: Stmt, label: &str) -> Option<(Vec<Stmt>, Stmt)> {
    let mut bodies = Vec::new();
    collect_duplicate_labeled_if_chain_bodies(&stmt, label, &mut bodies)?;
    if bodies.len() < 2 {
        return None;
    }

    let first = bodies.first()?.clone();
    if first.is_empty()
        || contains_label_or_goto(&first)
        || !bodies.iter().all(|body| body == &first)
    {
        return None;
    }

    let stripped = strip_duplicate_labeled_if_chain_labels(stmt, label)?;
    Some((first, stripped))
}

fn collect_duplicate_labeled_if_chain_bodies(
    stmt: &Stmt,
    label: &str,
    bodies: &mut Vec<Vec<Stmt>>,
) -> Option<()> {
    let Stmt::If {
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return None;
    };

    if let Some(body) = leading_label_body(then_body, label) {
        bodies.push(body);
    } else if block_contains_label(then_body, label) {
        return None;
    }

    match else_body.as_slice() {
        [next @ Stmt::If { .. }] => {
            collect_duplicate_labeled_if_chain_bodies(next, label, bodies)?;
        }
        _ if block_contains_label(else_body, label) => return None,
        _ => {}
    }

    Some(())
}

fn strip_duplicate_labeled_if_chain_labels(stmt: Stmt, label: &str) -> Option<Stmt> {
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = stmt
    else {
        return None;
    };

    let then_body = strip_leading_label_from_chain_body(then_body, label)?;
    let else_body = match else_body.as_slice() {
        [Stmt::If { .. }] => vec![strip_duplicate_labeled_if_chain_labels(
            else_body.into_iter().next()?,
            label,
        )?],
        _ if block_contains_label(&else_body, label) => return None,
        _ => else_body,
    };

    Some(Stmt::If {
        cond,
        then_body,
        else_body,
    })
}

fn strip_leading_label_from_chain_body(mut body: Vec<Stmt>, label: &str) -> Option<Vec<Stmt>> {
    match body.first() {
        Some(Stmt::Label(name)) if name == label => {
            body.remove(0);
            Some(body)
        }
        _ if block_contains_label(&body, label) => None,
        _ => Some(body),
    }
}

fn leading_label_body(stmts: &[Stmt], label: &str) -> Option<Vec<Stmt>> {
    match stmts.first() {
        Some(Stmt::Label(name)) if name == label => Some(stmts[1..].to_vec()),
        _ => None,
    }
}

fn block_contains_label(stmts: &[Stmt], label: &str) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Label(name) => name == label,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => block_contains_label(then_body, label) || block_contains_label(else_body, label),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => block_contains_label(body, label),
        _ => false,
    })
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

fn contains_label_or_goto_except_gotos(stmts: &[Stmt], allowed_goto: &str) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Label(_) => true,
        Stmt::Goto(label) => label != allowed_goto,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            contains_label_or_goto_except_gotos(then_body, allowed_goto)
                || contains_label_or_goto_except_gotos(else_body, allowed_goto)
        }
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => contains_label_or_goto_except_gotos(body, allowed_goto),
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

fn count_labels_named_outside(stmts: &[Stmt], label: &str, start: usize, end: usize) -> usize {
    stmts
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx < start || *idx > end)
        .map(|(_, stmt)| count_labels_named_stmt(stmt, label))
        .sum()
}

fn count_labels_named_stmt(stmt: &Stmt, label: &str) -> usize {
    match stmt {
        Stmt::Label(name) if name == label => 1,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => count_labels_named(then_body, label) + count_labels_named(else_body, label),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => count_labels_named(body, label),
        _ => 0,
    }
}

fn count_labels_named(stmts: &[Stmt], label: &str) -> usize {
    stmts
        .iter()
        .map(|stmt| count_labels_named_stmt(stmt, label))
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

/// One flat (non-recursive) inline within `block`: find the first foldable single-use definition
/// and inline it, returning whether it did. The caller loops this to the block's fixpoint; nested
/// blocks are reduced separately by [`single_use_inline`].
fn flat_inline_once(block: &mut Vec<Stmt>, protected: &BTreeSet<String>) -> bool {
    // Only LARGE blocks suffer the within-block O(n^2) (`next_def` scanning to end-of-block and the
    // goto-prefix check, for each of n candidates). For them, precompute per-name read/write
    // positions and a goto prefix ONCE — built from the exact same helpers (`writes_of_stmt`,
    // `count_uses_stmt`, `stmt_contains_goto`) so the lookups are identical to the direct scans.
    // Small blocks keep the direct scans: there the index build would cost more than it saves.
    type InlineIndex = (
        Vec<bool>,
        BTreeMap<String, Vec<usize>>,
        BTreeMap<String, Vec<(usize, usize)>>,
    );
    let index: Option<InlineIndex> = (block.len() > 64).then(|| {
        let mut goto_before = Vec::with_capacity(block.len() + 1);
        goto_before.push(false);
        let mut writes_at: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut reads_at: BTreeMap<String, Vec<(usize, usize)>> = BTreeMap::new();
        for (k, s) in block.iter().enumerate() {
            goto_before.push(goto_before[k] || stmt_contains_goto(s));
            for w in writes_of_stmt(s) {
                writes_at.entry(w).or_default().push(k);
            }
            let mut rc = BTreeMap::new();
            count_uses_stmt(s, &mut rc);
            for (name, count) in rc {
                reads_at.entry(name).or_default().push((k, count));
            }
        }
        (goto_before, writes_at, reads_at)
    });

    for i in 0..block.len() {
        let Some((name, val)) = sole_var_assign_ref(&block[i]) else {
            continue;
        };
        if protected.contains(name) {
            continue;
        }
        if expr_count_var(val, name) > 0 {
            continue; // self-referential definition (a refinement); leave it
        }
        // Pure values can move anywhere (interference-checked). An impure value (a call) may
        // only be inlined when the use evaluates it first (the temp is the head/receiver) and
        // nothing effectful sits between — then no side effect is reordered.
        let impure = !is_pure(val);

        // The definition's value is live until `name` is next written. Work only within a
        // straight-line window up to that point so we can see every use of THIS value.
        let next_def = match &index {
            Some((_, writes_at, _)) => writes_at
                .get(name)
                .and_then(|ws| ws.iter().find(|&&k| k > i).copied())
                .unwrap_or(block.len()),
            None => ((i + 1)..block.len())
                .find(|&k| stmt_writes_var(&block[k], name))
                .unwrap_or(block.len()),
        };
        let reads: Vec<(usize, usize)> = match &index {
            Some((_, _, reads_at)) => reads_at
                .get(name)
                .map(|rs| {
                    rs.iter()
                        .filter(|&&(k, _)| k > i && k < next_def)
                        .copied()
                        .collect()
                })
                .unwrap_or_default(),
            None => ((i + 1)..next_def)
                .filter_map(|k| {
                    let count = stmt_read_count(&block[k], name);
                    (count > 0).then_some((k, count))
                })
                .collect(),
        };
        if reads.is_empty() {
            continue;
        }
        let total_reads: usize = reads.iter().map(|(_, count)| *count).sum();
        let (j, reads_in_stmt) = reads[0];
        let replaceable_reads = stmt_replaceable_read_count(&block[j], name);
        if replaceable_reads == 0 {
            continue;
        }
        let goto_before_i = match &index {
            Some((goto_before, _, _)) => goto_before[i],
            None => block[..i].iter().any(stmt_contains_goto),
        };
        if goto_before_i {
            continue; // an earlier goto may jump a label into this value's def->use window;
                      // break/continue only exit to loop boundaries, never into the window
        }
        if block[i + 1..j].iter().any(is_control_flow) {
            continue; // a branch/loop before the use may hide path-specific behavior
        }

        // Interference check on the statements strictly between def and use. The read-set is
        // built only here — candidates that bailed at the cheaper checks above never allocate it.
        let val_reads = reads_of_expr(val);
        let needs_no_effects = reads_table(val) || impure;
        let mut safe = true;
        for stmt in &block[i + 1..j] {
            if matches!(stmt, Stmt::Label(_) | Stmt::Goto(_)) {
                safe = false;
                break;
            }
            if stmt_writes_any_of(stmt, &val_reads) {
                safe = false;
                break;
            }
            if needs_no_effects && stmt_effectful(stmt) {
                safe = false;
                break;
            }
        }
        // An impure value may only be inlined where it is evaluated first (head/receiver).
        if impure && stmt_head(&block[j]) != Some(name) {
            safe = false;
        }
        if !safe {
            continue;
        }

        // If this logical value has exactly one read and the next definition doesn't also
        // read it (`x = x.foo`), the materializing assignment can disappear entirely.
        let can_remove_def = total_reads == 1
            && !(next_def < block.len() && stmt_reads_var(&block[next_def], name));
        if stmt_reads_var_in_assignment_target(&block[j], name) {
            continue;
        }
        if !can_remove_def && !is_duplicable_leaf(val) {
            continue;
        }
        if !can_remove_def && (reads_in_stmt != 1 || replaceable_reads != 1) {
            continue; // don't partially inline `x` inside `x and x.y`
        }

        // Commit: only now do we clone the name/value (every candidate above was inspected by
        // reference). The borrows of `block[i]` via `name`/`val` end here, before the mutation.
        let name = name.to_string();
        let mut v = Some(val.clone());
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

fn stmt_contains_nonlocal_flow(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Goto(_) | Stmt::Break | Stmt::Continue => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => then_body
            .iter()
            .chain(else_body)
            .any(stmt_contains_nonlocal_flow),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => body.iter().any(stmt_contains_nonlocal_flow),
        _ => false,
    }
}

/// Whether `stmt` contains a `goto` anywhere (including inside nested loops/ifs). Unlike
/// `break`/`continue`, a `goto` can target a label outside its enclosing loop, so only a `goto`
/// can land control *inside* a straight-line def->use window.
fn stmt_contains_goto(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Goto(_) => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => then_body.iter().chain(else_body).any(stmt_contains_goto),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => body.iter().any(stmt_contains_goto),
        _ => false,
    }
}

fn contains_break_continue(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Break | Stmt::Continue => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => contains_break_continue(then_body) || contains_break_continue(else_body),
        Stmt::While { body, .. }
        | Stmt::Repeat { body, .. }
        | Stmt::NumericFor { body, .. }
        | Stmt::GenericFor { body, .. } => contains_break_continue(body),
        _ => false,
    })
}

fn contains_direct_break_continue(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Break | Stmt::Continue => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => contains_direct_break_continue(then_body) || contains_direct_break_continue(else_body),
        Stmt::While { .. }
        | Stmt::Repeat { .. }
        | Stmt::NumericFor { .. }
        | Stmt::GenericFor { .. } => false,
        _ => false,
    })
}

// --- dead store elimination ------------------------------------------------------------

/// Remove (when pure) or strip to a bare call (when impure) every sole-`Var` assignment whose
/// variable is read nowhere, at every nesting level, in a single pass. Returns whether anything
/// changed. The per-statement decision is identical to removing one-at-a-time; only the
/// batching differs. `uses` may be stale within the pass — that only makes it skip a store that
/// just became dead (caught on the caller's next recompute), never wrongly remove a live one,
/// because removing stores can only lower a variable's read count.
fn dead_in_block_all(
    block: &mut Vec<Stmt>,
    uses: &BTreeMap<String, usize>,
    protected: &BTreeSet<String>,
) -> bool {
    let mut changed = false;
    for s in block.iter_mut() {
        for_each_block_mut(s, |b| {
            if dead_in_block_all(b, uses, protected) {
                changed = true;
            }
        });
    }

    let mut i = 0;
    while i < block.len() {
        let Some((name, val)) = sole_var_assign(&block[i]) else {
            i += 1;
            continue;
        };
        // The local is never read anywhere: its stores are dead regardless of how many there
        // are. (A register reused for several short-lived unread values produces several.)
        if protected.contains(&name) || uses.get(&name).copied().unwrap_or(0) != 0 {
            i += 1;
            continue;
        }
        changed = true;
        if is_pure(&val) {
            block.remove(i); // pure & unused -> gone; re-examine the shifted statement
        } else {
            block[i] = Stmt::Call(val); // keep the side effect, drop the binding
            i += 1;
        }
    }
    changed
}

fn dead_overwritten_all(block: &mut Vec<Stmt>, protected: &BTreeSet<String>) -> bool {
    let mut changed = false;
    for s in block.iter_mut() {
        if dead_overwritten_nested_block(s, protected) {
            changed = true;
        }
    }

    let mut i = 0;
    while i < block.len() {
        let Some((name, val)) = sole_var_assign(&block[i]) else {
            i += 1;
            continue;
        };
        if protected.contains(&name) || !is_pure(&val) {
            i += 1;
            continue;
        }
        let Some(next_def) = ((i + 1)..block.len()).find(|&k| directly_writes_var(&block[k], &name))
        else {
            i += 1;
            continue;
        };
        if block[i + 1..next_def].iter().any(is_control_flow)
            || block[i + 1..next_def]
                .iter()
                .any(|stmt| stmt_reads_var(stmt, &name))
            || stmt_reads_var(&block[next_def], &name)
        {
            i += 1;
            continue;
        }
        block.remove(i); // re-examine the shifted statement
        changed = true;
    }
    changed
}

fn dead_overwritten_nested_block(s: &mut Stmt, protected: &BTreeSet<String>) -> bool {
    match s {
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            let a = dead_overwritten_all(then_body, protected);
            let b = dead_overwritten_all(else_body, protected);
            a || b
        }
        Stmt::While { cond, body } | Stmt::Repeat { body, cond } => {
            let mut loop_protected = protected.clone();
            loop_protected.extend(reads_of_expr(cond));
            dead_overwritten_all(body, &loop_protected)
        }
        Stmt::NumericFor { body, .. } | Stmt::GenericFor { body, .. } => {
            dead_overwritten_all(body, protected)
        }
        _ => false,
    }
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
    sole_var_assign_ref(s).map(|(name, val)| (name.to_string(), val.clone()))
}

/// Borrowing form of [`sole_var_assign`] — `(name, value)` for a single-target `x = v` / `local
/// x = v`, without cloning. The hot `inline_in_block` scan uses this so it only clones the value
/// at the rare point where it actually commits an inline, not for every candidate it inspects.
fn sole_var_assign_ref(s: &Stmt) -> Option<(&str, &Expr)> {
    match s {
        Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            match &targets[0] {
                Expr::Var(name) => Some((name.as_str(), &values[0])),
                _ => None,
            }
        }
        Stmt::Local { names, values } if names.len() == 1 && values.len() == 1 => {
            Some((names[0].as_str(), &values[0]))
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

/// `count_occurrences(e, ..)[name]` without the BTreeMap — mirrors `count_occurrences`'s arms and
/// the `!name.contains('.')` guard exactly, so it returns the identical count.
fn expr_count_var(e: &Expr, name: &str) -> usize {
    match e {
        Expr::Var(n) if !n.contains('.') => usize::from(n == name),
        Expr::Var(_) => 0,
        Expr::Index(t, k) => expr_count_var(t, name) + expr_count_var(k, name),
        Expr::Field(t, _) => expr_count_var(t, name),
        Expr::Call(f, args) => {
            expr_count_var(f, name) + args.iter().map(|a| expr_count_var(a, name)).sum::<usize>()
        }
        Expr::MethodCall(o, _, args) => {
            expr_count_var(o, name) + args.iter().map(|a| expr_count_var(a, name)).sum::<usize>()
        }
        Expr::Unary(_, a) => expr_count_var(a, name),
        Expr::Binary(_, a, b) => expr_count_var(a, name) + expr_count_var(b, name),
        Expr::Table(fields) => fields
            .iter()
            .map(|f| match f {
                TableField::Item(e) | TableField::Named(_, e) => expr_count_var(e, name),
                TableField::Keyed(k, v) => expr_count_var(k, name) + expr_count_var(v, name),
            })
            .sum(),
        _ => 0,
    }
}

/// `count_uses_stmt(s, ..)[name]` without the BTreeMap — mirrors `count_uses_stmt`'s arms,
/// the sole-Var-target-is-a-write rule, and the nested-block recursion exactly.
fn stmt_count_var(s: &Stmt, name: &str) -> usize {
    let mut n = match s {
        Stmt::Local { values, .. } => values.iter().map(|e| expr_count_var(e, name)).sum(),
        Stmt::Assign { targets, values } => {
            targets
                .iter()
                .map(|t| match t {
                    Expr::Var(_) => 0,
                    other => expr_count_var(other, name),
                })
                .sum::<usize>()
                + values.iter().map(|e| expr_count_var(e, name)).sum::<usize>()
        }
        Stmt::Call(e) => expr_count_var(e, name),
        Stmt::Return(es) => es.iter().map(|e| expr_count_var(e, name)).sum(),
        Stmt::If { cond, .. } | Stmt::While { cond, .. } | Stmt::Repeat { cond, .. } => {
            expr_count_var(cond, name)
        }
        Stmt::NumericFor {
            start, limit, step, ..
        } => {
            expr_count_var(start, name)
                + expr_count_var(limit, name)
                + step.as_ref().map_or(0, |s| expr_count_var(s, name))
        }
        Stmt::GenericFor { exprs, .. } => exprs.iter().map(|e| expr_count_var(e, name)).sum(),
        Stmt::Break | Stmt::Continue | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => 0,
    };
    for_each_block(s, |b| {
        n += b.iter().map(|st| stmt_count_var(st, name)).sum::<usize>();
    });
    n
}

fn stmt_read_count(s: &Stmt, name: &str) -> usize {
    stmt_count_var(s, name)
}

/// Reads of `name` directly in `s`'s own expressions (NOT nested blocks) — the shallow,
/// allocation-free counterpart of the original; mirrors its arms exactly (note While/Repeat
/// conditions are excluded, matching the original).
fn stmt_replaceable_read_count(s: &Stmt, name: &str) -> usize {
    match s {
        Stmt::Local { values, .. } => values.iter().map(|e| expr_count_var(e, name)).sum(),
        Stmt::Assign { targets, values } => {
            targets
                .iter()
                .filter(|t| !matches!(t, Expr::Var(_)))
                .map(|t| expr_count_var(t, name))
                .sum::<usize>()
                + values.iter().map(|e| expr_count_var(e, name)).sum::<usize>()
        }
        Stmt::Call(e) => expr_count_var(e, name),
        Stmt::Return(es) => es.iter().map(|e| expr_count_var(e, name)).sum(),
        Stmt::If { cond, .. } => expr_count_var(cond, name),
        Stmt::NumericFor {
            start, limit, step, ..
        } => {
            expr_count_var(start, name)
                + expr_count_var(limit, name)
                + step.as_ref().map_or(0, |s| expr_count_var(s, name))
        }
        Stmt::GenericFor { exprs, .. } => exprs.iter().map(|e| expr_count_var(e, name)).sum(),
        Stmt::While { .. }
        | Stmt::Repeat { .. }
        | Stmt::Break
        | Stmt::Continue
        | Stmt::Label(_)
        | Stmt::Goto(_)
        | Stmt::Comment(_) => 0,
    }
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

/// Whether `s` writes `name` anywhere — `writes_of_stmt(s).contains(name)` without the BTreeSet
/// allocation. Mirrors `writes_of_stmt`'s arms and recursion (via `for_each_block`) exactly, so it
/// is membership-identical; used in the hot `single_use_inline` scan where it ran once per
/// (candidate, statement) pair.
fn stmt_writes_var(s: &Stmt, name: &str) -> bool {
    let direct = match s {
        Stmt::Assign { targets, .. } => targets
            .iter()
            .any(|t| matches!(t, Expr::Var(n) if n == name)),
        Stmt::Local { names, .. } => names.iter().any(|n| n == name),
        Stmt::NumericFor { var, .. } => var == name,
        Stmt::GenericFor { vars, .. } => vars.iter().any(|v| v == name),
        _ => false,
    };
    if direct {
        return true;
    }
    let mut found = false;
    for_each_block(s, |b| {
        found = found || b.iter().any(|st| stmt_writes_var(st, name));
    });
    found
}

/// Whether `s` writes any name in `set` — `!writes_of_stmt(s).is_disjoint(set)` without the
/// allocation. Mirrors `writes_of_stmt` exactly.
fn stmt_writes_any_of(s: &Stmt, set: &BTreeSet<String>) -> bool {
    let direct = match s {
        Stmt::Assign { targets, .. } => targets
            .iter()
            .any(|t| matches!(t, Expr::Var(n) if set.contains(n))),
        Stmt::Local { names, .. } => names.iter().any(|n| set.contains(n)),
        Stmt::NumericFor { var, .. } => set.contains(var),
        Stmt::GenericFor { vars, .. } => vars.iter().any(|v| set.contains(v)),
        _ => false,
    };
    if direct {
        return true;
    }
    let mut found = false;
    for_each_block(s, |b| {
        found = found || b.iter().any(|st| stmt_writes_any_of(st, set));
    });
    found
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
        Expr::Call(callee, args) => reads_table(callee) || args.iter().any(reads_table),
        Expr::MethodCall(recv, _, args) => reads_table(recv) || args.iter().any(reads_table),
        Expr::Table(fields) => fields.iter().any(|field| match field {
            TableField::Item(value) | TableField::Named(_, value) => reads_table(value),
            TableField::Keyed(key, value) => reads_table(key) || reads_table(value),
        }),
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

pub fn remove_redundant_gotos(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, remove_redundant_gotos);
    }
    let mut i = 0;
    while i < root.len() {
        if let Stmt::Goto(label) = &root[i] {
            let label = label.clone();
            let mut next_idx = i + 1;
            while next_idx < root.len() {
                match &root[next_idx] {
                    Stmt::Comment(_) => {
                        next_idx += 1;
                    }
                    Stmt::Label(target) if target == &label => {
                        root.remove(i);
                        break;
                    }
                    _ => {
                        break;
                    }
                }
            }
            if next_idx < root.len()
                && matches!(&root[next_idx], Stmt::Label(target) if target == &label)
            {
                continue;
            }
        }
        i += 1;
    }
}

pub fn remove_trailing_sibling_gotos(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, remove_trailing_sibling_gotos);
    }

    let mut i = 0;
    while i < root.len() {
        let mut next_label = None;
        let mut next_idx = i + 1;
        while next_idx < root.len() {
            match &root[next_idx] {
                Stmt::Comment(_) => {
                    next_idx += 1;
                }
                Stmt::Label(name) => {
                    next_label = Some(name.clone());
                    break;
                }
                _ => {
                    break;
                }
            }
        }

        if let Some(label_name) = next_label {
            if let Stmt::If {
                cond,
                then_body,
                else_body,
            } = &mut root[i]
            {
                if let Some(Stmt::Goto(name)) = then_body.last() {
                    if name == &label_name {
                        then_body.pop();
                    }
                }
                if let Some(Stmt::Goto(name)) = else_body.last() {
                    if name == &label_name {
                        else_body.pop();
                    }
                }

                if then_body.is_empty() && else_body.is_empty() {
                    if is_pure(cond) {
                        root.remove(i);
                        continue;
                    } else {
                        root[i] = Stmt::Call(cond.clone());
                    }
                }
            }
        }
        i += 1;
    }
}

pub fn remove_unused_labels(root: &mut Vec<Stmt>) {
    let mut gotos = BTreeSet::new();
    fn collect_gotos(stmts: &[Stmt], gotos: &mut BTreeSet<String>) {
        for s in stmts {
            match s {
                Stmt::Goto(name) => {
                    gotos.insert(name.clone());
                }
                _ => {
                    for_each_block(s, |b| collect_gotos(b, gotos));
                }
            }
        }
    }
    collect_gotos(root, &mut gotos);

    fn remove_labels(stmts: &mut Vec<Stmt>, gotos: &BTreeSet<String>) {
        let mut i = 0;
        while i < stmts.len() {
            let mut remove = false;
            if let Stmt::Label(name) = &stmts[i] {
                if !gotos.contains(name) {
                    remove = true;
                }
            }
            if remove {
                stmts.remove(i);
            } else {
                for_each_block_mut(&mut stmts[i], |b| remove_labels(b, gotos));
                i += 1;
            }
        }
    }
    remove_labels(root, &gotos);
}

pub fn recover_if_else_gotos(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_if_else_gotos);
    }
    while recover_if_else_once(root) {}
}

/// Recover a common forward join shape:
///
/// ```lua
/// if cond then
///     accepted()
///     goto join
/// end
/// fallback()
/// ::join::
/// common()
/// ```
///
/// into:
///
/// ```lua
/// if cond then
///     accepted()
/// else
///     fallback()
/// end
/// common()
/// ```
///
/// The rewrite is limited to one incoming goto and fallback blocks with no nested
/// goto/label, so it does not move arbitrary control flow across branch boundaries.
pub fn recover_if_join_gotos(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_if_join_gotos);
    }
    while recover_if_join_once(root) {}
}

/// Recover short fallback tails left behind when earlier passes already removed the matching
/// join label:
///
/// ```lua
/// if accepted then
///     goto missing_join
/// end
/// fallback()
/// ```
///
/// becomes `if not accepted then fallback() end`. This intentionally only handles short,
/// straight-line tails; a long tail could include real common continuation code and is left as
/// explicit fallback control flow.
pub fn recover_orphan_if_join_gotos(root: &mut Vec<Stmt>) {
    let labels = label_names(root);
    recover_orphan_if_join_gotos_with_labels(root, &labels);
}

fn recover_orphan_if_join_gotos_with_labels(root: &mut Vec<Stmt>, labels: &BTreeSet<String>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, |body| {
            recover_orphan_if_join_gotos_with_labels(body, labels)
        });
    }
    while recover_orphan_if_skip_to_end_once(root, labels)
        || recover_orphan_if_join_once(root, labels)
    {}
}

pub fn recover_else_label_gotos(root: &mut [Stmt]) {
    for s in root.iter_mut() {
        for_each_block_mut(s, |body| recover_else_label_gotos(body));
    }
    while recover_else_label_once(root) {}
}

pub fn recover_gotos_to_later_else_label(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_gotos_to_later_else_label);
    }
    while recover_gotos_to_later_else_label_once(root) {}
}

pub fn recover_branch_gotos_to_following_label(root: &mut Vec<Stmt>) {
    for stmt in root.iter_mut() {
        for_each_block_mut(stmt, recover_branch_gotos_to_following_label);
    }
    while recover_branch_gotos_to_following_label_once(root) {}
}

fn recover_branch_gotos_to_following_label_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        let Stmt::Label(label) = &root[i + 1] else {
            i += 1;
            continue;
        };
        let label = label.clone();
        if count_gotos_named(&root[..i], &label) != 0 {
            i += 1;
            continue;
        }

        let Stmt::If {
            then_body,
            else_body,
            ..
        } = &mut root[i]
        else {
            i += 1;
            continue;
        };

        let changed_then = wrap_gotos_to_label_in_repeat_break(then_body, &label);
        let changed_else = wrap_gotos_to_label_in_repeat_break(else_body, &label);
        if !changed_then && !changed_else {
            i += 1;
            continue;
        }

        root.remove(i + 1);
        return true;
    }
    false
}

fn wrap_gotos_to_label_in_repeat_break(body: &mut Vec<Stmt>, label: &str) -> bool {
    if count_gotos_named(body, label) == 0
        || block_contains_label(body, label)
        || has_goto_in_nested_loop(body, label, false)
    {
        return false;
    }

    let mut wrapped = std::mem::take(body);
    replace_gotos_with_break(&mut wrapped, label);
    *body = vec![Stmt::Repeat {
        body: wrapped,
        cond: Expr::Bool(true),
    }];
    true
}

fn recover_else_label_once(root: &mut [Stmt]) -> bool {
    for stmt in root {
        let Stmt::If {
            then_body,
            else_body,
            ..
        } = stmt
        else {
            continue;
        };
        let Some(Stmt::Label(label)) = else_body.first() else {
            continue;
        };
        let label = label.clone();
        if count_gotos_named(then_body, &label) == 0
            || count_gotos_named(else_body, &label) != 0
            || has_goto_in_nested_loop(then_body, &label, false)
        {
            continue;
        }
        let target_body = else_body[1..].to_vec();
        if contains_label_or_goto(&target_body) {
            continue;
        }
        let Some(routed_then) =
            route_gotos_to_target_body(then_body.clone(), &label, target_body.clone(), Vec::new())
        else {
            continue;
        };
        *then_body = routed_then;
        *else_body = target_body;
        return true;
    }
    false
}

fn recover_gotos_to_later_else_label_once(root: &mut Vec<Stmt>) -> bool {
    let mut i = 0;
    while i + 1 < root.len() {
        let mut target_idx = i + 1;
        while target_idx < root.len().min(i + 48) {
            let Stmt::If {
                cond,
                then_body,
                else_body,
            } = &root[target_idx]
            else {
                target_idx += 1;
                continue;
            };
            let Some(Stmt::Label(label)) = else_body.first() else {
                target_idx += 1;
                continue;
            };
            let label = label.clone();
            let leading = root[i..target_idx].to_vec();
            let leading_gotos = count_gotos_named(&leading, &label);
            if leading_gotos == 0
                || contains_label_or_goto_except_gotos(&leading, &label)
                || has_goto_in_nested_loop(&leading, &label, false)
                || count_gotos_named(root, &label) != leading_gotos
                || count_labels_named_outside(root, &label, i, target_idx) != 0
                || !direct_local_scope_safe(&leading, &root[target_idx + 1..])
            {
                target_idx += 1;
                continue;
            }

            let target_body = else_body[1..].to_vec();
            let target_without_label = Stmt::If {
                cond: cond.clone(),
                then_body: then_body.clone(),
                else_body: target_body.clone(),
            };
            if target_body.is_empty()
                || contains_label_or_goto(&target_body)
                || contains_label_or_goto(std::slice::from_ref(&target_without_label))
            {
                target_idx += 1;
                continue;
            }

            let Some(mut routed) = route_gotos_to_target_body_deep(
                leading,
                &label,
                target_body,
                vec![target_without_label],
            ) else {
                target_idx += 1;
                continue;
            };
            if routed.is_empty() || contains_label_or_goto(&routed) {
                target_idx += 1;
                continue;
            }

            root.splice(i..=target_idx, routed.drain(..));
            return true;
        }
        i += 1;
    }
    false
}

fn route_gotos_to_target_body(
    mut block: Vec<Stmt>,
    label: &str,
    target_body: Vec<Stmt>,
    normal_continuation: Vec<Stmt>,
) -> Option<Vec<Stmt>> {
    if block.is_empty() {
        return Some(normal_continuation);
    }

    let first = block.remove(0);
    if count_gotos_named_stmt(&first, label) == 0 {
        let mut out = vec![first];
        out.extend(route_gotos_to_target_body(
            block,
            label,
            target_body,
            normal_continuation,
        )?);
        return Some(out);
    }

    match first {
        Stmt::Goto(target) if target == label => Some(target_body),
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            let continuation = append_blocks(block, normal_continuation);
            let then_body = if count_gotos_named(&then_body, label) > 0 {
                route_gotos_to_target_body(
                    then_body,
                    label,
                    target_body.clone(),
                    continuation.clone(),
                )?
            } else {
                append_blocks(then_body, continuation.clone())
            };
            let else_body = if count_gotos_named(&else_body, label) > 0 {
                route_gotos_to_target_body(else_body, label, target_body, continuation)?
            } else {
                append_blocks(else_body, continuation)
            };
            Some(vec![Stmt::If {
                cond,
                then_body,
                else_body,
            }])
        }
        _ => None,
    }
}

fn route_gotos_to_target_body_deep(
    mut block: Vec<Stmt>,
    label: &str,
    target_body: Vec<Stmt>,
    normal_continuation: Vec<Stmt>,
) -> Option<Vec<Stmt>> {
    if block.is_empty() {
        return Some(normal_continuation);
    }

    let first = block.remove(0);
    if count_gotos_named_stmt(&first, label) == 0 {
        let mut out = vec![first];
        out.extend(route_gotos_to_target_body_deep(
            block,
            label,
            target_body,
            normal_continuation,
        )?);
        return Some(out);
    }

    match first {
        Stmt::Goto(target) if target == label => Some(target_body),
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            let continuation = append_blocks(block, normal_continuation);
            let then_path = append_blocks(then_body, continuation.clone());
            let else_path = append_blocks(else_body, continuation);
            let then_body = if count_gotos_named(&then_path, label) > 0 {
                route_gotos_to_target_body_deep(then_path, label, target_body.clone(), Vec::new())?
            } else {
                then_path
            };
            let else_body = if count_gotos_named(&else_path, label) > 0 {
                route_gotos_to_target_body_deep(else_path, label, target_body, Vec::new())?
            } else {
                else_path
            };
            Some(vec![Stmt::If {
                cond,
                then_body,
                else_body,
            }])
        }
        _ => None,
    }
}

fn recover_if_join_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        if let Some((label, transformed)) = recover_nested_if_join(root, i) {
            let goto_count = count_gotos_named(root, &label);
            root[i] = transformed;
            let Some(label_idx) = root[i + 1..]
                .iter()
                .position(|stmt| matches!(stmt, Stmt::Label(name) if name == &label))
                .map(|offset| i + 1 + offset)
            else {
                continue;
            };
            let transformed_gotos = count_gotos_named_stmt(&root[i], &label);
            if goto_count == transformed_gotos {
                root.drain(i + 1..=label_idx);
            } else {
                root.drain(i + 1..label_idx);
            }
            return true;
        }

        let Some((label, goto_in_then)) = trailing_branch_goto(&root[i]) else {
            continue;
        };
        let Some(label_idx) = root[i + 1..]
            .iter()
            .position(|stmt| matches!(stmt, Stmt::Label(name) if name == &label))
            .map(|offset| i + 1 + offset)
        else {
            continue;
        };
        if label_idx <= i + 1 {
            continue;
        }

        let mut fallback = root[i + 1..label_idx].to_vec();
        if fallback.is_empty() || contains_label_or_goto(&fallback) {
            continue;
        }
        widen_locals_read_after_join(&mut fallback, &root[label_idx + 1..]);
        if !direct_local_scope_safe(&fallback, &root[label_idx + 1..]) {
            continue;
        }

        let goto_count = count_gotos_named(root, &label);
        if goto_count == 0 {
            continue;
        }

        let Stmt::If {
            cond,
            then_body,
            else_body,
        } = &mut root[i]
        else {
            continue;
        };

        if goto_in_then {
            then_body.pop();
            else_body.extend(fallback);
        } else {
            else_body.pop();
            then_body.extend(fallback);
        }

        let remove_label = goto_count == 1;
        if then_body.is_empty() && else_body.is_empty() {
            if is_pure(cond) {
                root.remove(i);
            } else {
                root[i] = Stmt::Call(cond.clone());
            }
        }
        // The rewrite above acts at index `i`, so it never shifts the `i + 1..` range start;
        // the label itself is consumed only when it was the sole goto target.
        let drain_end = if remove_label { label_idx + 1 } else { label_idx };
        root.drain(i + 1..drain_end);
        return true;
    }
    false
}

fn recover_orphan_if_join_once(root: &mut Vec<Stmt>, labels: &BTreeSet<String>) -> bool {
    for i in 0..root.len() {
        let goto_labels = goto_names_in_stmt(&root[i]);
        if goto_labels.len() != 1 {
            continue;
        }
        let label = goto_labels.into_iter().next().unwrap();
        if labels.contains(&label)
            || has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false)
        {
            continue;
        }
        let continuation = root[i + 1..].to_vec();
        if !is_short_straight_line_tail(&continuation) {
            continue;
        }
        let Some(transformed) = absorb_join_in_stmt(root[i].clone(), &label, continuation) else {
            continue;
        };
        root[i] = transformed;
        root.truncate(i + 1);
        return true;
    }
    false
}

fn recover_orphan_if_skip_to_end_once(root: &mut Vec<Stmt>, labels: &BTreeSet<String>) -> bool {
    for i in 0..root.len() {
        let Some((skip_cond, label)) = conditional_goto_expr(&root[i], None) else {
            continue;
        };
        if labels.contains(&label)
            || has_goto_in_nested_loop(std::slice::from_ref(&root[i]), &label, false)
        {
            continue;
        }
        let tail = root[i + 1..].to_vec();
        if tail.is_empty() || tail.len() > 64 || contains_label_or_goto(&tail) {
            continue;
        }
        root[i] = Stmt::If {
            cond: negate_condition(skip_cond),
            then_body: tail,
            else_body: Vec::new(),
        };
        root.truncate(i + 1);
        return true;
    }
    false
}

fn is_short_straight_line_tail(stmts: &[Stmt]) -> bool {
    !stmts.is_empty()
        && stmts.len() <= 8
        && stmts.iter().all(|stmt| {
            matches!(
                stmt,
                Stmt::Assign { .. }
                    | Stmt::Call(_)
                    | Stmt::Return(_)
                    | Stmt::Break
                    | Stmt::Continue
            )
        })
        && !contains_label_or_goto(stmts)
}

fn recover_nested_if_join(root: &[Stmt], index: usize) -> Option<(String, Stmt)> {
    let stmt = root.get(index)?;
    if !matches!(stmt, Stmt::If { .. }) {
        return None;
    }
    let labels = goto_names_in_stmt(stmt);
    if labels.len() != 1 {
        return None;
    }
    let label = labels.into_iter().next()?;
    if has_goto_in_nested_loop(std::slice::from_ref(stmt), &label, false) {
        return None;
    }
    let label_idx = root[index + 1..]
        .iter()
        .position(|stmt| matches!(stmt, Stmt::Label(name) if name == &label))
        .map(|offset| index + 1 + offset)?;
    if label_idx < index + 1 {
        return None;
    }
    let mut continuation = root[index + 1..label_idx].to_vec();
    if contains_label_or_goto(&continuation) {
        return None;
    }
    if !continuation.is_empty() {
        widen_locals_read_after_join(&mut continuation, &root[label_idx + 1..]);
        if !direct_local_scope_safe(&continuation, &root[label_idx + 1..]) {
            return None;
        }
    }
    let transformed = absorb_join_in_stmt(stmt.clone(), &label, continuation)?;
    Some((label, transformed))
}

fn absorb_join_in_stmt(stmt: Stmt, label: &str, continuation: Vec<Stmt>) -> Option<Stmt> {
    let Stmt::If {
        cond,
        then_body,
        else_body,
    } = stmt
    else {
        return None;
    };
    Some(Stmt::If {
        cond,
        then_body: absorb_join_in_block(then_body, label, continuation.clone())?,
        else_body: absorb_join_in_block(else_body, label, continuation)?,
    })
}

fn absorb_join_in_block(
    mut block: Vec<Stmt>,
    label: &str,
    continuation: Vec<Stmt>,
) -> Option<Vec<Stmt>> {
    if block.is_empty() {
        return Some(continuation);
    }

    let first = block.remove(0);
    if count_gotos_named_stmt(&first, label) == 0 {
        let mut out = vec![first];
        out.extend(absorb_join_in_block(block, label, continuation)?);
        return Some(out);
    }

    match first {
        Stmt::Goto(target) if target == label => Some(Vec::new()),
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            let rest_continuation = append_blocks(block, continuation);
            let then_body = absorb_join_in_block(then_body, label, rest_continuation.clone())?;
            let else_body = absorb_join_in_block(else_body, label, rest_continuation)?;
            Some(vec![Stmt::If {
                cond,
                then_body,
                else_body,
            }])
        }
        _ => None,
    }
}

fn append_blocks(mut first: Vec<Stmt>, second: Vec<Stmt>) -> Vec<Stmt> {
    if block_ends_terminated(&first) {
        first
    } else {
        first.extend(second);
        first
    }
}

fn block_ends_terminated(block: &[Stmt]) -> bool {
    matches!(
        block.last(),
        Some(Stmt::Return(_) | Stmt::Break | Stmt::Continue | Stmt::Goto(_))
    )
}

fn trailing_branch_goto(stmt: &Stmt) -> Option<(String, bool)> {
    let Stmt::If {
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return None;
    };

    match (then_body.last(), else_body.last()) {
        (Some(Stmt::Goto(label)), None) | (Some(Stmt::Goto(label)), Some(_)) => {
            Some((label.clone(), true))
        }
        (None, Some(Stmt::Goto(label))) | (Some(_), Some(Stmt::Goto(label))) => {
            Some((label.clone(), false))
        }
        _ => None,
    }
}

fn widen_locals_read_after_join(stmts: &mut [Stmt], following: &[Stmt]) {
    let mut read_after = BTreeSet::new();
    for stmt in stmts.iter() {
        if let Stmt::Local { names, .. } = stmt {
            for name in names {
                if following
                    .iter()
                    .any(|following_stmt| stmt_reads_var_recursive(following_stmt, name))
                {
                    read_after.insert(name.clone());
                }
            }
        }
    }
    if read_after.is_empty() {
        return;
    }

    for stmt in stmts {
        let Stmt::Local { names, values } = stmt else {
            continue;
        };
        if names.iter().any(|name| read_after.contains(name)) {
            *stmt = Stmt::Assign {
                targets: names.iter().cloned().map(Expr::Var).collect(),
                values: values.clone(),
            };
        }
    }
}

fn recover_if_else_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let Some((exit_cond, l_else)) = conditional_goto_expr(&root[i], None) else {
            continue;
        };
        let Some(else_idx) = root
            .iter()
            .position(|s| matches!(s, Stmt::Label(l) if l == &l_else))
        else {
            continue;
        };
        if else_idx <= i + 1 {
            continue;
        }
        let l_end = match &root[else_idx - 1] {
            Stmt::Goto(l) => l.clone(),
            _ => continue,
        };
        let Some(end_idx) = root
            .iter()
            .position(|s| matches!(s, Stmt::Label(l) if l == &l_end))
        else {
            continue;
        };
        if end_idx <= else_idx {
            continue;
        }

        let then_body = root[i + 1..else_idx - 1].to_vec();
        let else_body = root[else_idx + 1..end_idx].to_vec();

        let if_stmt = Stmt::If {
            cond: negate_condition(exit_cond),
            then_body,
            else_body,
        };

        root[i] = if_stmt;
        root.drain(i + 1..=end_idx);
        return true;
    }
    false
}

/// Last-resort recovery for an unstructured infinite loop: `::L:: <body> goto L`, where the single
/// backward goto to `L` is an unconditional top-level statement, becomes `while true do <body> end`.
/// Unlike [`recover_backward_goto_while`] this needs no exit-test-at-top — the body's own
/// `return`/`break` are its exits (the obfuscator's dispatch/decryption loops have this shape).
/// Processing innermost blocks first means nested same-named labels resolve one loop at a time, so
/// the count-of-one guard holds. This turns the goto/label fallback into legal Luau, which has no
/// `goto`; it only fires on protos that already fell back to goto, so structured output is untouched.
pub fn recover_unstructured_backward_loops(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_unstructured_backward_loops);
    }
    while recover_unstructured_backward_loop_once(root) {}
}

fn recover_unstructured_backward_loop_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let Stmt::Label(label) = &root[i] else {
            continue;
        };
        let label = label.clone();
        // Exactly one goto targets this label (counted recursively), and it is a bare top-level
        // statement after the label — the loop's back-edge.
        if count_gotos_named(root, &label) != 1 {
            continue;
        }
        let Some(j) = (i + 1..root.len()).find(|&k| matches!(&root[k], Stmt::Goto(l) if l == &label))
        else {
            continue;
        };
        if i + 1 >= j {
            continue;
        }
        let body = root[i + 1..j].to_vec();
        root[i] = Stmt::While {
            cond: Expr::Bool(true),
            body,
        };
        root.drain(i + 1..=j);
        return true;
    }
    false
}

pub fn recover_backward_goto_while(root: &mut Vec<Stmt>) {
    for s in root.iter_mut() {
        for_each_block_mut(s, recover_backward_goto_while);
    }
    let mut changed = true;
    while changed {
        changed = recover_backward_goto_while_once(root)
            || recover_while_with_condition_load(root)
            || recover_repeat_return_goto_once(root);
    }
}

fn recover_repeat_return_goto_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let Stmt::Label(label_name) = &root[i] else {
            continue;
        };
        let label_name = label_name.clone();
        let Some(goto_idx) = root[i + 1..]
            .iter()
            .position(|s| matches!(s, Stmt::Goto(name) if name == &label_name))
            .map(|offset| i + 1 + offset)
        else {
            continue;
        };
        if count_gotos_named(root, &label_name) != 1 || goto_idx <= i + 1 {
            continue;
        }

        let mut conds = Vec::new();
        let mut return_values: Option<Vec<Expr>> = None;
        let mut first_cond_idx = goto_idx;

        while first_cond_idx > i + 1 {
            let idx = first_cond_idx - 1;
            let Stmt::If {
                cond,
                then_body,
                else_body,
            } = &root[idx]
            else {
                break;
            };
            if !else_body.is_empty() || then_body.len() != 1 {
                break;
            }
            let Stmt::Return(values) = &then_body[0] else {
                break;
            };
            if let Some(existing) = &return_values {
                if existing != values {
                    break;
                }
            } else {
                return_values = Some(values.clone());
            }
            conds.push(cond.clone());
            first_cond_idx = idx;
        }

        if conds.is_empty()
            || first_cond_idx <= i + 1
            || contains_label_or_goto(&root[i + 1..first_cond_idx])
        {
            continue;
        }

        conds.reverse();
        let Some(cond) = or_all(conds) else {
            continue;
        };
        let values = return_values.unwrap_or_default();
        let body = root[i + 1..first_cond_idx].to_vec();
        root[i] = Stmt::Repeat { body, cond };
        root.drain(i + 1..=goto_idx);
        root.insert(i + 1, Stmt::Return(values));
        return true;
    }
    false
}

fn recover_while_with_condition_load(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let Stmt::Label(label_name) = &root[i] else {
            continue;
        };
        let label_name = label_name.clone();

        if i + 2 >= root.len() {
            continue;
        }

        let (cond_var, cond_expr) = match &root[i + 1] {
            Stmt::Local { names, values } if names.len() == 1 && values.len() == 1 => {
                (names[0].clone(), values[0].clone())
            }
            Stmt::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
                if let Expr::Var(name) = &targets[0] {
                    (name.clone(), values[0].clone())
                } else {
                    continue;
                }
            }
            _ => continue,
        };

        let Stmt::If {
            cond,
            then_body,
            else_body,
        } = &root[i + 2]
        else {
            continue;
        };

        let matches_cond = match cond {
            Expr::Unary("not ", expr) => {
                if let Expr::Var(name) = &**expr {
                    name == &cond_var
                } else {
                    false
                }
            }
            Expr::Var(name) => name == &cond_var,
            _ => false,
        };
        if !matches_cond {
            continue;
        }

        if then_body.is_empty() {
            continue;
        }
        let last_idx = then_body.len() - 1;
        let Stmt::Goto(goto_target) = &then_body[last_idx] else {
            continue;
        };
        if goto_target != &label_name {
            continue;
        }

        if !else_body.is_empty() {
            continue;
        }

        let loop_body = then_body[..last_idx].to_vec();

        let loop_cond = if let Expr::Unary("not ", _) = cond {
            negate_condition(cond_expr)
        } else {
            cond_expr
        };

        let while_stmt = Stmt::While {
            cond: loop_cond,
            body: loop_body,
        };

        root[i] = while_stmt;
        root.drain(i + 1..=i + 2);
        return true;
    }
    false
}

fn recover_backward_goto_while_once(root: &mut Vec<Stmt>) -> bool {
    for i in 0..root.len() {
        let Stmt::Label(label_name) = &root[i] else {
            continue;
        };
        let label_name = label_name.clone();
        let mut goto_idx = None;
        for (k, stmt) in root.iter().enumerate().skip(i + 1) {
            if let Stmt::Goto(name) = stmt {
                if name == &label_name {
                    goto_idx = Some(k);
                    break;
                }
            }
        }
        let Some(j) = goto_idx else {
            continue;
        };
        if count_gotos_named(root, &label_name) != 1 {
            continue;
        }
        if i + 1 >= j {
            continue;
        }
        let Some((exit_cond, exit_label)) = conditional_goto_expr(&root[i + 1], None) else {
            continue;
        };
        let Some(exit_idx) = root
            .iter()
            .position(|s| matches!(s, Stmt::Label(l) if l == &exit_label))
        else {
            continue;
        };
        if exit_idx < j {
            continue;
        }

        let loop_body = root[i + 2..j].to_vec();
        if has_goto_in_nested_loop(&loop_body, &exit_label, false) {
            continue;
        }

        let mut loop_body = loop_body;
        replace_gotos_with_break(&mut loop_body, &exit_label);

        let while_stmt = Stmt::While {
            cond: negate_condition(exit_cond),
            body: loop_body,
        };

        root[i] = while_stmt;
        root.drain(i + 1..=j);

        if count_gotos_named(root, &exit_label) == 0 {
            if let Some(pos) = root
                .iter()
                .position(|s| matches!(s, Stmt::Label(l) if l == &exit_label))
            {
                root.remove(pos);
            }
        }
        return true;
    }
    false
}

fn replace_gotos_with_break(stmts: &mut [Stmt], target_label: &str) {
    for s in stmts.iter_mut() {
        match s {
            Stmt::Goto(name) if name == target_label => {
                *s = Stmt::Break;
            }
            _ => {
                for_each_block_mut(s, |b| replace_gotos_with_break(b, target_label));
            }
        }
    }
}

fn replace_gotos_with_continue(stmts: &mut [Stmt], target_label: &str) {
    for s in stmts.iter_mut() {
        match s {
            Stmt::Goto(name) if name == target_label => {
                *s = Stmt::Continue;
            }
            _ => {
                for_each_block_mut(s, |b| replace_gotos_with_continue(b, target_label));
            }
        }
    }
}

fn has_goto_in_nested_loop(stmts: &[Stmt], target_label: &str, in_loop: bool) -> bool {
    for s in stmts {
        match s {
            Stmt::Goto(name) if name == target_label => {
                if in_loop {
                    return true;
                }
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. } => {
                if has_goto_in_nested_loop(body, target_label, true) {
                    return true;
                }
            }
            _ => {
                let mut found = false;
                for_each_block(s, |b| {
                    if !found {
                        found = has_goto_in_nested_loop(b, target_label, in_loop);
                    }
                });
                if found {
                    return true;
                }
            }
        }
    }
    false
}

// --- Register/Value Splitting (Slice 5) --------------------------------------------------

fn is_synthetic(name: &str) -> bool {
    if !name.starts_with('v') || name.len() < 2 {
        return false;
    }
    let rest = &name[1..];
    if let Some(pos) = rest.find('_') {
        let before = &rest[..pos];
        let after = &rest[pos + 1..];
        !before.is_empty()
            && before.chars().all(|c| c.is_ascii_digit())
            && !after.is_empty()
            && after.chars().all(|c| c.is_ascii_digit())
    } else {
        rest.chars().all(|c| c.is_ascii_digit())
    }
}

fn is_parameter(name: &str) -> bool {
    name.len() >= 2 && name.starts_with('p') && name[1..].chars().all(|c| c.is_ascii_digit())
}

fn collect_unsplittable(stmts: &[Stmt], in_nested: bool, unsplittable: &mut BTreeSet<String>) {
    for s in stmts {
        match s {
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                collect_expr_vars(cond, in_nested, unsplittable);
                collect_unsplittable(then_body, true, unsplittable);
                collect_unsplittable(else_body, true, unsplittable);
            }
            Stmt::While { cond, body } => {
                collect_expr_vars(cond, true, unsplittable);
                collect_unsplittable(body, true, unsplittable);
            }
            Stmt::Repeat { body, cond } => {
                collect_unsplittable(body, true, unsplittable);
                collect_expr_vars(cond, true, unsplittable);
            }
            Stmt::NumericFor {
                var,
                start,
                limit,
                step,
                body,
            } => {
                unsplittable.insert(var.clone());
                collect_expr_vars(start, true, unsplittable);
                collect_expr_vars(limit, true, unsplittable);
                if let Some(step_expr) = step {
                    collect_expr_vars(step_expr, true, unsplittable);
                }
                collect_unsplittable(body, true, unsplittable);
            }
            Stmt::GenericFor { vars, exprs, body } => {
                for v in vars {
                    unsplittable.insert(v.clone());
                }
                for e in exprs {
                    collect_expr_vars(e, true, unsplittable);
                }
                collect_unsplittable(body, true, unsplittable);
            }
            Stmt::Local { names, values } => {
                for name in names {
                    if in_nested {
                        unsplittable.insert(name.clone());
                    }
                }
                for val in values {
                    collect_expr_vars(val, in_nested, unsplittable);
                }
            }
            Stmt::Assign { targets, values } => {
                for t in targets {
                    collect_expr_vars(t, in_nested, unsplittable);
                }
                for val in values {
                    collect_expr_vars(val, in_nested, unsplittable);
                }
            }
            Stmt::Call(expr) => {
                collect_expr_vars(expr, in_nested, unsplittable);
            }
            Stmt::Return(exprs) => {
                for e in exprs {
                    collect_expr_vars(e, in_nested, unsplittable);
                }
            }
            _ => {}
        }
    }
}

fn collect_expr_vars(e: &Expr, in_nested: bool, unsplittable: &mut BTreeSet<String>) {
    match e {
        Expr::Var(name) if in_nested => {
            unsplittable.insert(name.clone());
        }
        Expr::Raw(text) => {
            for word in text.split(|c: char| !c.is_ascii_alphanumeric() && c != '_') {
                if is_synthetic(word) || is_parameter(word) {
                    unsplittable.insert(word.to_string());
                }
            }
        }
        Expr::Index(t, k) => {
            collect_expr_vars(t, in_nested, unsplittable);
            collect_expr_vars(k, in_nested, unsplittable);
        }
        Expr::Field(t, _) => {
            collect_expr_vars(t, in_nested, unsplittable);
        }
        Expr::Call(f, args) => {
            collect_expr_vars(f, in_nested, unsplittable);
            for arg in args {
                collect_expr_vars(arg, in_nested, unsplittable);
            }
        }
        Expr::MethodCall(o, _, args) => {
            collect_expr_vars(o, in_nested, unsplittable);
            for arg in args {
                collect_expr_vars(arg, in_nested, unsplittable);
            }
        }
        Expr::Unary(_, a) => {
            collect_expr_vars(a, in_nested, unsplittable);
        }
        Expr::Binary(_, a, b) => {
            collect_expr_vars(a, in_nested, unsplittable);
            collect_expr_vars(b, in_nested, unsplittable);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => {
                        collect_expr_vars(e, in_nested, unsplittable);
                    }
                    TableField::Keyed(k, v) => {
                        collect_expr_vars(k, in_nested, unsplittable);
                        collect_expr_vars(v, in_nested, unsplittable);
                    }
                }
            }
        }
        _ => {}
    }
}

fn collect_block_vars(stmts: &[Stmt], vars: &mut BTreeSet<String>) {
    for s in stmts {
        match s {
            Stmt::Local { names, values } => {
                for name in names {
                    vars.insert(name.clone());
                }
                for val in values {
                    collect_expr_vars_simple(val, vars);
                }
            }
            Stmt::Assign { targets, values } => {
                for t in targets {
                    collect_expr_vars_simple(t, vars);
                }
                for val in values {
                    collect_expr_vars_simple(val, vars);
                }
            }
            Stmt::Call(e) => collect_expr_vars_simple(e, vars),
            Stmt::Return(es) => es.iter().for_each(|e| collect_expr_vars_simple(e, vars)),
            Stmt::If { cond, .. } => collect_expr_vars_simple(cond, vars),
            Stmt::While { cond, .. } => collect_expr_vars_simple(cond, vars),
            Stmt::Repeat { cond, .. } => collect_expr_vars_simple(cond, vars),
            _ => {}
        }
    }
}

fn collect_expr_vars_simple(e: &Expr, vars: &mut BTreeSet<String>) {
    match e {
        Expr::Var(name) => {
            vars.insert(name.clone());
        }
        Expr::Index(t, k) => {
            collect_expr_vars_simple(t, vars);
            collect_expr_vars_simple(k, vars);
        }
        Expr::Field(t, _) => {
            collect_expr_vars_simple(t, vars);
        }
        Expr::Call(f, args) => {
            collect_expr_vars_simple(f, vars);
            for arg in args {
                collect_expr_vars_simple(arg, vars);
            }
        }
        Expr::MethodCall(o, _, args) => {
            collect_expr_vars_simple(o, vars);
            for arg in args {
                collect_expr_vars_simple(arg, vars);
            }
        }
        Expr::Unary(_, a) => {
            collect_expr_vars_simple(a, vars);
        }
        Expr::Binary(_, a, b) => {
            collect_expr_vars_simple(a, vars);
            collect_expr_vars_simple(b, vars);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => {
                        collect_expr_vars_simple(e, vars);
                    }
                    TableField::Keyed(k, v) => {
                        collect_expr_vars_simple(k, vars);
                        collect_expr_vars_simple(v, vars);
                    }
                }
            }
        }
        _ => {}
    }
}

fn rename_var_in_expr(e: &mut Expr, var: &str, new_name: &str) {
    match e {
        Expr::Var(name) if name == var => {
            *name = new_name.to_string();
        }
        Expr::Index(t, k) => {
            rename_var_in_expr(t, var, new_name);
            rename_var_in_expr(k, var, new_name);
        }
        Expr::Field(t, _) => {
            rename_var_in_expr(t, var, new_name);
        }
        Expr::Call(f, args) => {
            rename_var_in_expr(f, var, new_name);
            for arg in args {
                rename_var_in_expr(arg, var, new_name);
            }
        }
        Expr::MethodCall(o, _, args) => {
            rename_var_in_expr(o, var, new_name);
            for arg in args {
                rename_var_in_expr(arg, var, new_name);
            }
        }
        Expr::Unary(_, a) => {
            rename_var_in_expr(a, var, new_name);
        }
        Expr::Binary(_, a, b) => {
            rename_var_in_expr(a, var, new_name);
            rename_var_in_expr(b, var, new_name);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => {
                        rename_var_in_expr(e, var, new_name);
                    }
                    TableField::Keyed(k, v) => {
                        rename_var_in_expr(k, var, new_name);
                        rename_var_in_expr(v, var, new_name);
                    }
                }
            }
        }
        _ => {}
    }
}

fn rename_var_in_stmt(s: &mut Stmt, var: &str, read_ver: usize, write_ver: usize) {
    let read_name = format!("{var}_{read_ver}");
    let write_name = format!("{var}_{write_ver}");
    match s {
        Stmt::Local { names, values } => {
            for val in values {
                rename_var_in_expr(val, var, &read_name);
            }
            for name in names {
                if name == var {
                    *name = write_name.clone();
                }
            }
        }
        Stmt::Assign { targets, values } => {
            for val in values {
                rename_var_in_expr(val, var, &read_name);
            }
            for target in targets {
                match target {
                    Expr::Var(name) if name == var => {
                        *name = write_name.clone();
                    }
                    _ => {
                        rename_var_in_expr(target, var, &read_name);
                    }
                }
            }
        }
        Stmt::Call(e) => {
            rename_var_in_expr(e, var, &read_name);
        }
        Stmt::Return(es) => {
            for e in es {
                rename_var_in_expr(e, var, &read_name);
            }
        }
        Stmt::If { cond, .. } => {
            rename_var_in_expr(cond, var, &read_name);
        }
        Stmt::While { cond, .. } => {
            rename_var_in_expr(cond, var, &read_name);
        }
        Stmt::Repeat { cond, .. } => {
            rename_var_in_expr(cond, var, &read_name);
        }
        _ => {}
    }
}

fn split_reused_registers_in_block(stmts: &mut [Stmt], unsplittable: &BTreeSet<String>) {
    // 1. Recurse into subblocks
    for s in stmts.iter_mut() {
        match s {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                split_reused_registers_in_block(then_body, unsplittable);
                split_reused_registers_in_block(else_body, unsplittable);
            }
            Stmt::While { body, .. } => {
                split_reused_registers_in_block(body, unsplittable);
            }
            Stmt::Repeat { body, .. } => {
                split_reused_registers_in_block(body, unsplittable);
            }
            Stmt::NumericFor { body, .. } => {
                split_reused_registers_in_block(body, unsplittable);
            }
            Stmt::GenericFor { body, .. } => {
                split_reused_registers_in_block(body, unsplittable);
            }
            _ => {}
        }
    }

    // 2. Process current block candidates
    let mut candidates = BTreeSet::new();
    collect_block_vars(stmts, &mut candidates);
    let candidates: Vec<String> = candidates
        .into_iter()
        .filter(|name| is_synthetic(name) && !unsplittable.contains(name))
        .collect();

    for var in candidates {
        let mut current_version = 1;
        let mut stmt_versions = Vec::new();
        let mut ever_written = false;
        let mut referenced = false;

        for s in stmts.iter() {
            let reads = stmt_reads_var(s, &var);
            let writes = directly_writes_var(s, &var);

            let read_ver = current_version;
            let mut write_ver = current_version;

            if writes {
                if ever_written || reads {
                    current_version += 1;
                    write_ver = current_version;
                }
                ever_written = true;
            }
            if reads || writes {
                referenced = true;
            }

            stmt_versions.push((read_ver, write_ver));
        }

        if referenced && current_version > 1 {
            for (i, s) in stmts.iter_mut().enumerate() {
                let (read_ver, write_ver) = stmt_versions[i];
                rename_var_in_stmt(s, &var, read_ver, write_ver);
            }
        }
    }
}

fn collect_split_candidates_recursive(
    stmts: &[Stmt],
    unsplittable: &BTreeSet<String>,
    candidates: &mut BTreeSet<String>,
) {
    let mut block_vars = BTreeSet::new();
    collect_block_vars(stmts, &mut block_vars);
    candidates.extend(
        block_vars
            .into_iter()
            .filter(|name| is_synthetic(name) && !unsplittable.contains(name)),
    );

    for stmt in stmts {
        for_each_block(stmt, |b| {
            collect_split_candidates_recursive(b, unsplittable, candidates)
        });
    }
}

pub fn split_reused_registers(stmts: &mut [Stmt], protected: &BTreeSet<String>) {
    // These bounds cap this O(candidates * statements) pass, but they are ALSO a correctness guard:
    // splitting multiplies the number of distinct locals, and a large proto can blow past Luau's
    // hard 200-locals-per-function limit (the compiler rejects the output with "out of local
    // registers"). Keeping large protos un-split keeps their registers fused and under the limit.
    // Raising these caused real fixtures (e.g. Networking) to stop recompiling, so they stay put.
    if count_stmts(stmts) > 600 {
        return;
    }
    let mut unsplittable = protected.clone();
    collect_unsplittable(stmts, false, &mut unsplittable);
    let mut candidates = BTreeSet::new();
    collect_split_candidates_recursive(stmts, &unsplittable, &mut candidates);
    if candidates.len() > 80 {
        return;
    }
    split_reused_registers_in_block(stmts, &unsplittable);
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
    fn inlines_table_literal_fill_temps() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["parent".into()],
                values: vec![Expr::Table(Vec::new())],
            },
            Stmt::Local {
                names: vec!["tmp".into()],
                values: vec![Expr::Table(vec![TableField::Named(
                    "ConstraintType".into(),
                    Expr::Str("\"Hinge\"".into()),
                )])],
            },
            Stmt::Assign {
                targets: vec![Expr::Index(
                    Box::new(Expr::Var("parent".into())),
                    Box::new(Expr::Var("motor".into())),
                )],
                values: vec![Expr::Var("tmp".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("tmp".into())],
                values: vec![Expr::Table(Vec::new())],
            },
        ];

        inline_table_literal_fill_temps(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("parent[motor] = {ConstraintType = \"Hinge\"}"),
            "{rendered}"
        );
        assert!(
            !rendered.contains("local tmp = {ConstraintType"),
            "{rendered}"
        );
    }

    #[test]
    fn folds_pure_constructor_temps_into_table_literals() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["palette".into()],
                values: vec![Expr::Table(Vec::new())],
            },
            Stmt::Local {
                names: vec!["color".into()],
                values: vec![Expr::Call(
                    Box::new(Expr::Field(
                        Box::new(Expr::Var("Color3".into())),
                        "fromRGB".into(),
                    )),
                    vec![
                        Expr::Num("71".into()),
                        Expr::Num("184".into()),
                        Expr::Num("197".into()),
                    ],
                )],
            },
            Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("palette".into())),
                    "Teal".into(),
                )],
                values: vec![Expr::Var("color".into())],
            },
            Stmt::Return(vec![Expr::Var("palette".into())]),
        ];

        single_use_inline(&mut stmts, &BTreeSet::new());
        fold_table_literals(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("Teal = Color3.fromRGB(71, 184, 197)"),
            "{rendered}"
        );
        assert!(!rendered.contains("local color"), "{rendered}");
        assert!(!rendered.contains("palette.Teal"), "{rendered}");
    }

    #[test]
    fn recovers_loop_carried_callback_update_before_nil_guard() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Binary(
                    "~=",
                    Box::new(Expr::Call(
                        Box::new(Expr::Var("callback".into())),
                        vec![Expr::Var("current".into())],
                    )),
                    Box::new(Expr::Nil),
                ),
                then_body: vec![Stmt::Continue],
                else_body: Vec::new(),
            },
            Stmt::Return(vec![Expr::Nil]),
        ];

        recover_loop_carried_call_updates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("current = callback(current)"),
            "{rendered}"
        );
        assert!(rendered.contains("if current == nil then"), "{rendered}");
        assert!(rendered.contains("return nil"), "{rendered}");
        assert!(!rendered.contains("if callback(current)"), "{rendered}");
    }

    #[test]
    fn simplifies_repeat_return_guard_and_temp_limit() {
        let mut stmts = vec![
            Stmt::Repeat {
                body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("tries".into())],
                        values: vec![Expr::Binary(
                            "+",
                            Box::new(Expr::Var("tries".into())),
                            Box::new(Expr::Num("1".into())),
                        )],
                    },
                    Stmt::If {
                        cond: Expr::Var("saved".into()),
                        then_body: vec![Stmt::Return(vec![
                            Expr::Var("saved".into()),
                            Expr::Var("lastError".into()),
                        ])],
                        else_body: Vec::new(),
                    },
                    Stmt::Assign {
                        targets: vec![Expr::Var("v8".into())],
                        values: vec![Expr::Num("3".into())],
                    },
                ],
                cond: Expr::Binary(
                    "<=",
                    Box::new(Expr::Var("v8".into())),
                    Box::new(Expr::Var("tries".into())),
                ),
            },
            Stmt::Return(vec![
                Expr::Var("saved".into()),
                Expr::Var("lastError".into()),
            ]),
        ];

        simplify_repeat_return_guards(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("until saved or tries >= 3"), "{rendered}");
        assert!(!rendered.contains("v8 = 3"), "{rendered}");
        assert!(!rendered.contains("if saved then"), "{rendered}");
    }

    #[test]
    fn simplifies_duplicate_nested_guards() {
        let mut stmts = vec![Stmt::If {
            cond: Expr::Unary("not ", Box::new(Expr::Var("value".into()))),
            then_body: vec![Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("value".into()))),
                then_body: vec![Stmt::Return(vec![Expr::Table(Vec::new())])],
                else_body: Vec::new(),
            }],
            else_body: Vec::new(),
        }];

        simplify_redundant_conditions(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert_eq!(
            rendered.matches("if not value then").count(),
            1,
            "{rendered}"
        );
        assert!(rendered.contains("return {}"), "{rendered}");
    }

    #[test]
    fn simplifies_duplicate_pure_boolean_operands() {
        let mut stmts = vec![Stmt::While {
            cond: Expr::Binary(
                "and",
                Box::new(Expr::Binary(
                    "and",
                    Box::new(Expr::Unary("not ", Box::new(Expr::Var("track".into())))),
                    Box::new(Expr::Unary("not ", Box::new(Expr::Var("track".into())))),
                )),
                Box::new(Expr::Field(
                    Box::new(Expr::Var("model".into())),
                    "Parent".into(),
                )),
            ),
            body: vec![Stmt::Call(Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("task".into())),
                    "wait".into(),
                )),
                Vec::new(),
            ))],
        }];

        simplify_redundant_conditions(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("while not track and model.Parent do"),
            "{rendered}"
        );
        assert!(!rendered.contains("not track and not track"), "{rendered}");
    }

    #[test]
    fn keeps_loop_body_assignment_read_by_repeat_condition() {
        let mut stmts = vec![Stmt::Repeat {
            body: vec![
                Stmt::Assign {
                    targets: vec![Expr::Var("saved".into())],
                    values: vec![Expr::Var("ok".into())],
                },
                Stmt::If {
                    cond: Expr::Unary("not ", Box::new(Expr::Var("saved".into()))),
                    then_body: vec![Stmt::Call(Expr::Call(
                        Box::new(Expr::Field(
                            Box::new(Expr::Var("task".into())),
                            "wait".into(),
                        )),
                        Vec::new(),
                    ))],
                    else_body: Vec::new(),
                },
            ],
            cond: Expr::Binary(
                "or",
                Box::new(Expr::Var("saved".into())),
                Box::new(Expr::Binary(
                    ">=",
                    Box::new(Expr::Var("tries".into())),
                    Box::new(Expr::Num("3".into())),
                )),
            ),
        }];

        single_use_inline(&mut stmts, &BTreeSet::new());
        dead_store_elim(&mut stmts, &BTreeSet::new());

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("saved = ok"), "{rendered}");
        assert!(rendered.contains("if not saved then"), "{rendered}");
        assert!(rendered.contains("until saved or tries >= 3"), "{rendered}");
    }

    #[test]
    fn removes_pure_store_after_final_read_in_block() {
        let mut stmts = vec![
            Stmt::GenericFor {
                vars: vec!["key".into(), "value".into()],
                exprs: vec![Expr::Call(
                    Box::new(Expr::Var("pairs".into())),
                    vec![Expr::Var("defaults".into())],
                )],
                body: vec![Stmt::Assign {
                    targets: vec![Expr::Index(
                        Box::new(Expr::Var("config".into())),
                        Box::new(Expr::Var("key".into())),
                    )],
                    values: vec![Expr::Var("value".into())],
                }],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("timeout".into())],
                values: vec![Expr::Call(
                    Box::new(Expr::Field(
                        Box::new(Expr::Var("math".into())),
                        "clamp".into(),
                    )),
                    vec![
                        Expr::Var("timeout".into()),
                        Expr::Num("1".into()),
                        Expr::Num("60".into()),
                    ],
                )],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("key".into())],
                values: vec![Expr::Num("60".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("config".into())),
                    "Timeout".into(),
                )],
                values: vec![Expr::Var("timeout".into())],
            },
        ];

        remove_dead_pure_stores_after_last_read(&mut stmts, &BTreeSet::new());

        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("key = 60"), "{rendered}");
        assert!(rendered.contains("config.Timeout = timeout"), "{rendered}");
    }

    #[test]
    fn keeps_pure_store_before_goto_after_last_local_read() {
        let mut stmts = vec![Stmt::If {
            cond: Expr::Var("bad".into()),
            then_body: vec![
                Stmt::Assign {
                    targets: vec![Expr::Var("valid".into())],
                    values: vec![Expr::Bool(false)],
                },
                Stmt::Goto("join".into()),
            ],
            else_body: Vec::new(),
        }];

        remove_dead_pure_stores_after_last_read(&mut stmts, &BTreeSet::new());

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("valid = false"), "{rendered}");
        assert!(rendered.contains("goto join"), "{rendered}");
    }

    #[test]
    fn does_not_inline_join_value_after_prior_goto() {
        let mut stmts = vec![
            Stmt::NumericFor {
                var: "i".into(),
                start: Expr::Num("1".into()),
                limit: Expr::Var("n".into()),
                step: None,
                body: vec![Stmt::If {
                    cond: Expr::Var("bad".into()),
                    then_body: vec![Stmt::Goto("join".into())],
                    else_body: Vec::new(),
                }],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("valid".into())],
                values: vec![Expr::Bool(true)],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("valid".into()))),
                then_body: vec![Stmt::Return(vec![Expr::Str("\"bad\"".into())])],
                else_body: Vec::new(),
            },
        ];

        single_use_inline(&mut stmts, &BTreeSet::new());

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("valid = true"), "{rendered}");
        assert!(rendered.contains("if not valid then"), "{rendered}");
        assert!(!rendered.contains("if not true then"), "{rendered}");
    }

    #[test]
    fn loop_bool_selector_gotos_become_breaks() {
        let mut stmts = vec![
            Stmt::NumericFor {
                var: "i".into(),
                start: Expr::Num("1".into()),
                limit: Expr::Var("len".into()),
                step: None,
                body: vec![Stmt::If {
                    cond: Expr::Var("bad".into()),
                    then_body: vec![
                        Stmt::Assign {
                            targets: vec![Expr::Var("valid".into())],
                            values: vec![Expr::Bool(false)],
                        },
                        Stmt::Goto("join".into()),
                    ],
                    else_body: Vec::new(),
                }],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("valid".into())],
                values: vec![Expr::Bool(true)],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Bool(true))),
                then_body: vec![Stmt::Return(vec![Expr::Str("\"bad\"".into())])],
                else_body: Vec::new(),
            },
        ];

        recover_loop_bool_selector_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("valid = true"), "{rendered}");
        assert!(rendered.contains("valid = false"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("if not valid then"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("if not true then"), "{rendered}");
    }

    #[test]
    fn loop_bool_assignment_gotos_become_breaks() {
        let mut stmts = vec![
            Stmt::NumericFor {
                var: "i".into(),
                start: Expr::Num("1".into()),
                limit: Expr::Var("len".into()),
                step: None,
                body: vec![Stmt::If {
                    cond: Expr::Var("bad".into()),
                    then_body: vec![
                        Stmt::Assign {
                            targets: vec![Expr::Var("valid".into())],
                            values: vec![Expr::Bool(false)],
                        },
                        Stmt::Goto("join".into()),
                    ],
                    else_body: Vec::new(),
                }],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("valid".into())],
                values: vec![Expr::Bool(true)],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("valid".into()))),
                then_body: vec![Stmt::Return(vec![Expr::Str("\"bad\"".into())])],
                else_body: Vec::new(),
            },
        ];

        recover_loop_bool_selector_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.starts_with("valid = true"), "{rendered}");
        assert!(rendered.contains("valid = false"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("if not valid then"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn loop_bool_assignment_false_default_rewrites_constant_guard() {
        let mut stmts = vec![
            Stmt::GenericFor {
                vars: vec!["i".into()],
                exprs: vec![Expr::Var("items".into())],
                body: vec![Stmt::If {
                    cond: Expr::Var("missing".into()),
                    then_body: vec![
                        Stmt::Assign {
                            targets: vec![Expr::Var("found".into())],
                            values: vec![Expr::Bool(true)],
                        },
                        Stmt::Goto("join".into()),
                    ],
                    else_body: Vec::new(),
                }],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("found".into())],
                values: vec![Expr::Bool(false)],
            },
            Stmt::If {
                cond: Expr::Bool(false),
                then_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("useFound".into())),
                    Vec::new(),
                ))],
                else_body: Vec::new(),
            },
        ];

        recover_loop_bool_selector_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.starts_with("found = false"), "{rendered}");
        assert!(rendered.contains("found = true"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("if found then"), "{rendered}");
        assert!(!rendered.contains("if false then"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn loop_bool_guard_gotos_become_breaks() {
        let mut stmts = vec![
            Stmt::While {
                cond: Expr::Var("running".into()),
                body: vec![Stmt::If {
                    cond: Expr::Var("hit".into()),
                    then_body: vec![
                        Stmt::Assign {
                            targets: vec![Expr::Var("checked".into())],
                            values: vec![Expr::Bool(true)],
                        },
                        Stmt::Goto("join".into()),
                    ],
                    else_body: Vec::new(),
                }],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("checked".into()))),
                then_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("fallback".into())),
                    Vec::new(),
                ))],
                else_body: Vec::new(),
            },
        ];

        recover_loop_bool_selector_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("checked = true"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("if not checked then"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn trailing_missing_loop_goto_is_removed() {
        let mut stmts = vec![Stmt::While {
            cond: Expr::Var("running".into()),
            body: vec![
                Stmt::Call(Expr::Call(Box::new(Expr::Var("step".into())), Vec::new())),
                Stmt::Goto("loop_head".into()),
            ],
        }];

        recover_loop_bool_selector_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("step()"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn tail_branch_missing_loop_gotos_are_removed() {
        let mut stmts = vec![Stmt::While {
            cond: Expr::Var("running".into()),
            body: vec![Stmt::If {
                cond: Expr::Var("left".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("index".into())],
                        values: vec![Expr::Var("leftIndex".into())],
                    },
                    Stmt::Goto("loop_head".into()),
                ],
                else_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("index".into())],
                        values: vec![Expr::Var("rightIndex".into())],
                    },
                    Stmt::Goto("loop_head".into()),
                ],
            }],
        }];

        recover_loop_bool_selector_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("index = leftIndex"), "{rendered}");
        assert!(rendered.contains("index = rightIndex"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn terminal_label_gotos_become_returns() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Binary(
                    "==",
                    Box::new(Expr::Var("event".into())),
                    Box::new(Expr::Str("\"RunTween\"".into())),
                ),
                then_body: vec![
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("run".into())), Vec::new())),
                    Stmt::Goto("done".into()),
                    Stmt::Call(Expr::Call(
                        Box::new(Expr::Var("unreachable".into())),
                        Vec::new(),
                    )),
                ],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("after".into())), Vec::new())),
            Stmt::Label("done".into()),
            Stmt::Return(Vec::new()),
        ];

        replace_terminal_label_gotos_with_return(&mut stmts);
        drop_unreachable(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("return"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::done::"), "{rendered}");
        assert!(!rendered.contains("unreachable"), "{rendered}");
        assert!(rendered.contains("after()"), "{rendered}");
    }

    #[test]
    fn terminal_label_tail_gotos_become_tail_returns() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("is_value".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("next".into())],
                        values: vec![Expr::Var("value".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("is_velocity".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("next".into())],
                        values: vec![Expr::Var("velocity".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("next".into())],
                values: vec![Expr::Var("fallback".into())],
            },
            Stmt::Label("done".into()),
            Stmt::Assign {
                targets: vec![Expr::Var("current".into())],
                values: vec![Expr::Var("next".into())],
            },
        ];

        replace_terminal_label_tail_gotos(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert_eq!(rendered.matches("current = next").count(), 3, "{rendered}");
        assert_eq!(rendered.matches("return").count(), 2, "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::done::"), "{rendered}");
    }

    #[test]
    fn loop_gotos_to_terminal_label_tail_become_tail_returns() {
        let mut stmts = vec![
            Stmt::While {
                cond: Expr::Bool(true),
                body: vec![
                    Stmt::If {
                        cond: Expr::Var("finished".into()),
                        then_body: vec![Stmt::Goto("done".into())],
                        else_body: Vec::new(),
                    },
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("step".into())), Vec::new())),
                ],
            },
            Stmt::Label("done".into()),
            Stmt::Call(Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("debug".into())),
                    "profileend".into(),
                )),
                Vec::new(),
            )),
            Stmt::Return(vec![Expr::Var("result".into())]),
        ];

        replace_loop_gotos_to_terminal_label_tail(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert_eq!(
            rendered.matches("debug.profileend()").count(),
            2,
            "{rendered}"
        );
        assert!(rendered.contains("return result"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::done::"), "{rendered}");
    }

    #[test]
    fn terminal_label_tail_rewrites_direct_gotos_before_removing_label() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("fast_path".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("result".into())],
                        values: vec![Expr::Var("fast".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("result".into())],
                values: vec![Expr::Var("middle".into())],
            },
            Stmt::Goto("done".into()),
            Stmt::Assign {
                targets: vec![Expr::Var("result".into())],
                values: vec![Expr::Var("fallback".into())],
            },
            Stmt::Label("done".into()),
            Stmt::Assign {
                targets: vec![Expr::Var("out".into())],
                values: vec![Expr::Var("result".into())],
            },
        ];

        replace_terminal_label_tail_gotos(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert_eq!(rendered.matches("out = result").count(), 3, "{rendered}");
        assert!(!rendered.contains("goto done"), "{rendered}");
        assert!(!rendered.contains("::done::"), "{rendered}");
    }

    #[test]
    fn orphan_gotos_to_terminal_continuation_are_duplicated() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::MethodCall(
                    Box::new(Expr::Var("candidate".into())),
                    "IsA".into(),
                    vec![Expr::Str("\"Sound\"".into())],
                ),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("sound".into())],
                        values: vec![Expr::Var("candidate".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("sound".into())],
                values: vec![Expr::MethodCall(
                    Box::new(Expr::Var("candidate".into())),
                    "FindFirstChildWhichIsA".into(),
                    vec![Expr::Str("\"Sound\"".into())],
                )],
            },
            Stmt::If {
                cond: Expr::Binary(
                    "==",
                    Box::new(Expr::Var("sound".into())),
                    Box::new(Expr::Nil),
                ),
                then_body: vec![Stmt::Return(vec![Expr::Nil])],
                else_body: Vec::new(),
            },
            Stmt::Return(vec![Expr::Var("sound".into())]),
        ];

        replace_orphan_gotos_with_terminal_continuation(&mut stmts);
        drop_unreachable(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("goto done"), "{rendered}");
        assert_eq!(rendered.matches("return sound").count(), 2, "{rendered}");
        assert!(rendered.contains("if sound == nil then"), "{rendered}");
    }

    #[test]
    fn orphan_terminal_continuation_keeps_ambiguous_join_vars() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("use_a".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("a".into())],
                        values: vec![Expr::Num("1".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("use_b".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("b".into())],
                        values: vec![Expr::Num("2".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Return(vec![Expr::Var("a".into())]),
        ];

        replace_orphan_gotos_with_terminal_continuation(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("goto done"), "{rendered}");
    }

    #[test]
    fn orphan_fallback_gotos_become_else_branch() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("cached".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("value".into())],
                        values: vec![Expr::Var("cached".into())],
                    },
                    Stmt::Goto("joined".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Local {
                names: vec!["computed".into()],
                values: vec![Expr::Call(
                    Box::new(Expr::Var("compute".into())),
                    Vec::new(),
                )],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("value".into())],
                values: vec![Expr::Var("computed".into())],
            },
            Stmt::If {
                cond: Expr::Var("value".into()),
                then_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("use".into())),
                    vec![Expr::Var("value".into())],
                ))],
                else_body: Vec::new(),
            },
        ];

        recover_orphan_if_fallback_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("if cached then"), "{rendered}");
        assert!(
            rendered.contains("else\n\tlocal computed = compute()"),
            "{rendered}"
        );
        assert!(
            rendered.contains("if value then\n\tuse(value)\nend"),
            "{rendered}"
        );
        assert!(!rendered.contains("goto joined"), "{rendered}");
    }

    #[test]
    fn orphan_skip_block_gotos_become_guarded_block() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("cursorFree".into()),
                then_body: vec![Stmt::Goto("joined".into())],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Binary(
                    "==",
                    Box::new(Expr::Var("currentInput".into())),
                    Box::new(Expr::Str("\"Touch\"".into())),
                ),
                then_body: vec![Stmt::Goto("joined".into())],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("mouseDelta".into())],
                values: vec![Expr::Call(
                    Box::new(Expr::Field(
                        Box::new(Expr::Var("UserInputService".into())),
                        "GetMouseDelta".into(),
                    )),
                    Vec::new(),
                )],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("cursorFree".into()))),
                then_body: vec![Stmt::Assign {
                    targets: vec![Expr::Var("mouseDelta".into())],
                    values: vec![Expr::Binary(
                        "+",
                        Box::new(Expr::Var("mouseDelta".into())),
                        Box::new(Expr::Var("pendingDelta".into())),
                    )],
                }],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("controller".into())),
                    "PendingTouchLookDelta".into(),
                )],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("Vector2".into())),
                    "zero".into(),
                )],
            },
            Stmt::Local {
                names: vec!["now".into()],
                values: vec![Expr::Call(Box::new(Expr::Var("tick".into())), Vec::new())],
            },
        ];

        recover_orphan_skip_blocks(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if not cursorFree and currentInput ~= \"Touch\" then"),
            "{rendered}"
        );
        assert!(
            rendered.contains("mouseDelta = UserInputService.GetMouseDelta()"),
            "{rendered}"
        );
        assert!(
            rendered.contains("controller.PendingTouchLookDelta = Vector2.zero"),
            "{rendered}"
        );
        assert!(rendered.contains("local now = tick()"), "{rendered}");
        assert!(!rendered.contains("goto joined"), "{rendered}");
    }

    #[test]
    fn orphan_skip_block_stops_at_first_value_read() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("skip".into()),
                then_body: vec![Stmt::Goto("joined".into())],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("value".into())],
                values: vec![Expr::Call(
                    Box::new(Expr::Var("compute".into())),
                    Vec::new(),
                )],
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("use".into())),
                vec![Expr::Var("value".into())],
            )),
        ];

        recover_orphan_skip_blocks(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if not skip then\n\tvalue = compute()\nend"),
            "{rendered}"
        );
        assert!(rendered.contains("use(value)"), "{rendered}");
        assert!(!rendered.contains("goto joined"), "{rendered}");
    }

    #[test]
    fn nested_orphan_skip_goto_routes_following_block() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("hasDirectDelta".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("opened".into())],
                        values: vec![Expr::Var("directDelta".into())],
                    },
                    Stmt::Goto("joined".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Local {
                names: vec!["thumbstick".into()],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("self".into())),
                    "LastThumbstickInput".into(),
                )],
            },
            Stmt::If {
                cond: Expr::Var("thumbstick".into()),
                then_body: vec![Stmt::Assign {
                    targets: vec![Expr::Var("opened".into())],
                    values: vec![Expr::Call(
                        Box::new(Expr::Var("fromThumbstick".into())),
                        vec![Expr::Var("thumbstick".into())],
                    )],
                }],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("opened".into()),
                then_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("apply".into())),
                    vec![Expr::Var("opened".into())],
                ))],
                else_body: Vec::new(),
            },
        ];

        recover_nested_orphan_skip_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("if hasDirectDelta then"), "{rendered}");
        assert!(
            rendered.contains("else\n\tthumbstick = self.LastThumbstickInput"),
            "{rendered}"
        );
        assert!(rendered.contains("apply(opened)"), "{rendered}");
        assert!(!rendered.contains("goto joined"), "{rendered}");
    }

    #[test]
    fn return_only_labels_become_direct_returns() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("done".into()),
                then_body: vec![Stmt::Goto("exit".into())],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("work".into())), Vec::new())),
            Stmt::If {
                cond: Expr::Var("failed".into()),
                then_body: vec![Stmt::Label("exit".into()), Stmt::Return(Vec::new())],
                else_body: Vec::new(),
            },
        ];

        replace_return_label_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if done then\n\treturn\nend"),
            "{rendered}"
        );
        assert!(!rendered.contains("goto exit"), "{rendered}");
        assert!(!rendered.contains("::exit::"), "{rendered}");
    }

    #[test]
    fn return_only_labels_keep_conflicting_return_values() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("done".into()),
                then_body: vec![Stmt::Goto("exit".into())],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("a".into()),
                then_body: vec![
                    Stmt::Label("exit".into()),
                    Stmt::Return(vec![Expr::Bool(true)]),
                ],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("b".into()),
                then_body: vec![
                    Stmt::Label("exit".into()),
                    Stmt::Return(vec![Expr::Bool(false)]),
                ],
                else_body: Vec::new(),
            },
        ];

        replace_return_label_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("goto exit"), "{rendered}");
        assert!(rendered.contains("::exit::"), "{rendered}");
    }

    #[test]
    fn orphan_terminal_goto_becomes_return_and_enables_guard_cleanup() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Binary(
                    "~=",
                    Box::new(Expr::Var("name".into())),
                    Box::new(Expr::Str("\"damper\"".into())),
                ),
                then_body: vec![Stmt::If {
                    cond: Expr::Binary(
                        "~=",
                        Box::new(Expr::Var("name".into())),
                        Box::new(Expr::Str("\"d\"".into())),
                    ),
                    then_body: vec![Stmt::Goto("missing_end".into())],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("value".into())],
                values: vec![Expr::Var("damper".into())],
            },
            Stmt::Goto("missing_tail".into()),
            Stmt::Return(Vec::new()),
        ];

        replace_orphan_terminal_goto_with_return(&mut stmts);
        recover_orphan_if_join_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("if name == \"damper\" or name == \"d\" then"));
        assert!(rendered.contains("return"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn removes_dead_literal_markers_but_keeps_read_strings() {
        let mut stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("marker".into())],
                values: vec![Expr::Str("\"Model\"".into())],
            },
            Stmt::If {
                cond: Expr::Var("ok".into()),
                then_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("touch".into())),
                    Vec::new(),
                ))],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("marker".into())],
                values: vec![Expr::Call(
                    Box::new(Expr::Field(
                        Box::new(Expr::Var("Instance".into())),
                        "new".into(),
                    )),
                    vec![Expr::Str("\"Weld\"".into())],
                )],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("kind".into())],
                values: vec![Expr::Str("\"BasePart\"".into())],
            },
            Stmt::If {
                cond: Expr::Binary(
                    "==",
                    Box::new(Expr::Var("kind".into())),
                    Box::new(Expr::Str("\"BasePart\"".into())),
                ),
                then_body: Vec::new(),
                else_body: Vec::new(),
            },
        ];

        remove_dead_literal_markers(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("marker = \"Model\""), "{rendered}");
        assert!(rendered.contains("kind = \"BasePart\""), "{rendered}");
    }

    #[test]
    fn removes_dead_literal_marker_before_nested_overwrite() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("primaryPart".into()))),
                then_body: vec![Stmt::Assign {
                    targets: vec![Expr::Var("cframe".into())],
                    values: vec![Expr::Str("\"Middle\"".into())],
                }],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("useMotor".into()))),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("cframe".into())],
                        values: vec![Expr::Call(
                            Box::new(Expr::Field(
                                Box::new(Expr::Var("CFrame".into())),
                                "new".into(),
                            )),
                            Vec::new(),
                        )],
                    },
                    Stmt::Assign {
                        targets: vec![Expr::Field(Box::new(Expr::Var("weld".into())), "C0".into())],
                        values: vec![Expr::Var("cframe".into())],
                    },
                    Stmt::Return(vec![Expr::Var("weld".into())]),
                ],
                else_body: Vec::new(),
            },
            Stmt::Return(vec![Expr::Var("motor".into())]),
        ];

        remove_dead_literal_markers(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("cframe = \"Middle\""), "{rendered}");
        assert!(rendered.contains("cframe = CFrame.new()"), "{rendered}");
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

    #[test]
    fn recovers_goto_into_labeled_if_gate_with_unrelated_backedge() {
        let mut stmts = vec![
            Stmt::Label("loop_start".into()),
            Stmt::If {
                cond: Expr::Var("missing_a".into()),
                then_body: vec![Stmt::Goto("retry".into())],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("missing_b".into()),
                then_body: vec![
                    Stmt::Label("retry".into()),
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("wait".into())), Vec::new())),
                    Stmt::Goto("loop_start".into()),
                ],
                else_body: Vec::new(),
            },
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if missing_a or missing_b then"),
            "{rendered}"
        );
        assert!(rendered.contains("goto loop_start"), "{rendered}");
        assert!(!rendered.contains("goto retry"), "{rendered}");
        assert!(!rendered.contains("::retry::"), "{rendered}");
    }

    #[test]
    fn recovers_goto_into_later_labeled_if_gate() {
        let mut stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("allowed".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("item".into())),
                    "IsMolotov".into(),
                )],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("allowed".into()))),
                then_body: vec![Stmt::Goto("accepted".into())],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("allowed".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("item".into())),
                    "Lit".into(),
                )],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("allowed".into()))),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("allowed".into())],
                        values: vec![Expr::Field(
                            Box::new(Expr::Var("item".into())),
                            "Thrown".into(),
                        )],
                    },
                    Stmt::If {
                        cond: Expr::Unary("not ", Box::new(Expr::Var("allowed".into()))),
                        then_body: vec![
                            Stmt::Label("accepted".into()),
                            Stmt::Call(Expr::Call(Box::new(Expr::Var("equip".into())), Vec::new())),
                        ],
                        else_body: Vec::new(),
                    },
                ],
                else_body: Vec::new(),
            },
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if not allowed then\n\tequip()"),
            "{rendered}"
        );
        assert!(
            rendered.contains("else\n\tallowed = item.Lit"),
            "{rendered}"
        );
        assert_eq!(rendered.matches("equip()").count(), 2, "{rendered}");
        assert!(!rendered.contains("goto accepted"), "{rendered}");
        assert!(!rendered.contains("::accepted::"), "{rendered}");
    }

    #[test]
    fn later_labeled_if_gate_allows_reused_label_names_outside_region() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("first".into()),
                then_body: vec![Stmt::Goto("L6".into())],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("first".into())],
                values: vec![Expr::Var("fallback".into())],
            },
            Stmt::If {
                cond: Expr::Var("fallback".into()),
                then_body: vec![
                    Stmt::Label("L6".into()),
                    Stmt::Call(Expr::Call(
                        Box::new(Expr::Var("useFirst".into())),
                        Vec::new(),
                    )),
                ],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("second".into()),
                then_body: vec![Stmt::Goto("L6".into())],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("second".into())],
                values: vec![Expr::Var("fallback2".into())],
            },
            Stmt::If {
                cond: Expr::Var("fallback2".into()),
                then_body: vec![
                    Stmt::Label("L6".into()),
                    Stmt::Call(Expr::Call(
                        Box::new(Expr::Var("useSecond".into())),
                        Vec::new(),
                    )),
                ],
                else_body: Vec::new(),
            },
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("useFirst()"), "{rendered}");
        assert!(rendered.contains("useSecond()"), "{rendered}");
        assert!(!rendered.contains("goto L6"), "{rendered}");
        assert!(!rendered.contains("::L6::"), "{rendered}");
    }

    #[test]
    fn nested_goto_to_later_label_routes_fallthrough_prefix() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("upright".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("allowed".into())],
                        values: vec![Expr::Field(
                            Box::new(Expr::Var("item".into())),
                            "IsDynamite".into(),
                        )],
                    },
                    Stmt::If {
                        cond: Expr::Unary("not ", Box::new(Expr::Var("allowed".into()))),
                        then_body: vec![
                            Stmt::Assign {
                                targets: vec![Expr::Var("allowed".into())],
                                values: vec![Expr::Field(
                                    Box::new(Expr::Var("item".into())),
                                    "IsMolotov".into(),
                                )],
                            },
                            Stmt::If {
                                cond: Expr::Unary("not ", Box::new(Expr::Var("allowed".into()))),
                                then_body: vec![Stmt::Goto("accepted".into())],
                                else_body: Vec::new(),
                            },
                        ],
                        else_body: Vec::new(),
                    },
                ],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("allowed".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("item".into())),
                    "Lit".into(),
                )],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("allowed".into()))),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("allowed".into())],
                        values: vec![Expr::Field(
                            Box::new(Expr::Var("item".into())),
                            "Thrown".into(),
                        )],
                    },
                    Stmt::If {
                        cond: Expr::Unary("not ", Box::new(Expr::Var("allowed".into()))),
                        then_body: vec![
                            Stmt::Label("accepted".into()),
                            Stmt::Call(Expr::Call(Box::new(Expr::Var("equip".into())), Vec::new())),
                        ],
                        else_body: Vec::new(),
                    },
                ],
                else_body: Vec::new(),
            },
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("equip()"), "{rendered}");
        assert!(!rendered.contains("goto accepted"), "{rendered}");
        assert!(!rendered.contains("::accepted::"), "{rendered}");
    }

    #[test]
    fn recovers_goto_into_labeled_elseif_chain() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("skip".into()),
                then_body: vec![Stmt::Goto("fallback".into())],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("isSprinting".into()),
                then_body: vec![
                    Stmt::Label("fallback".into()),
                    Stmt::Assign {
                        targets: vec![Expr::Var("canCrouch".into())],
                        values: vec![Expr::Bool(false)],
                    },
                ],
                else_body: vec![Stmt::If {
                    cond: Expr::Var("isSwimming".into()),
                    then_body: vec![
                        Stmt::Label("fallback".into()),
                        Stmt::Assign {
                            targets: vec![Expr::Var("canCrouch".into())],
                            values: vec![Expr::Bool(false)],
                        },
                    ],
                    else_body: vec![Stmt::Assign {
                        targets: vec![Expr::Var("canCrouch".into())],
                        values: vec![Expr::Bool(true)],
                    }],
                }],
            },
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if skip or isSprinting then"),
            "{rendered}"
        );
        assert!(rendered.contains("elseif isSwimming then"), "{rendered}");
        assert!(!rendered.contains("goto fallback"), "{rendered}");
        assert!(!rendered.contains("::fallback::"), "{rendered}");
    }

    #[test]
    fn recovers_goto_into_later_duplicated_labeled_elseif_chain() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("skipSetup".into()),
                then_body: vec![Stmt::Goto("blocked".into())],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("sprinting".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("self".into())),
                    "IsSprinting".into(),
                )],
            },
            Stmt::If {
                cond: Expr::Var("sprinting".into()),
                then_body: vec![
                    Stmt::Label("blocked".into()),
                    Stmt::Assign {
                        targets: vec![Expr::Var("canCrouch".into())],
                        values: vec![Expr::Bool(false)],
                    },
                ],
                else_body: vec![Stmt::If {
                    cond: Expr::Unary("not ", Box::new(Expr::Var("upright".into()))),
                    then_body: vec![
                        Stmt::Label("blocked".into()),
                        Stmt::Assign {
                            targets: vec![Expr::Var("canCrouch".into())],
                            values: vec![Expr::Bool(false)],
                        },
                    ],
                    else_body: vec![Stmt::Assign {
                        targets: vec![Expr::Var("canCrouch".into())],
                        values: vec![Expr::Bool(true)],
                    }],
                }],
            },
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("if skipSetup then"), "{rendered}");
        assert!(rendered.contains("canCrouch = false"), "{rendered}");
        assert!(
            rendered.contains("else\n\tsprinting = self.IsSprinting"),
            "{rendered}"
        );
        assert!(rendered.contains("elseif not upright then"), "{rendered}");
        assert!(!rendered.contains("goto blocked"), "{rendered}");
        assert!(!rendered.contains("::blocked::"), "{rendered}");
    }

    #[test]
    fn recovers_gotos_to_later_else_label() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Binary(
                    "<=",
                    Box::new(Expr::Var("magnitude".into())),
                    Box::new(Expr::Num("0".into())),
                ),
                then_body: vec![
                    Stmt::If {
                        cond: Expr::Unary("not ", Box::new(Expr::Var("swimming".into()))),
                        then_body: vec![Stmt::Goto("reset".into())],
                        else_body: Vec::new(),
                    },
                    Stmt::Assign {
                        targets: vec![Expr::Var("magnitude".into())],
                        values: vec![Expr::Field(
                            Box::new(Expr::Var("velocity".into())),
                            "Y".into(),
                        )],
                    },
                    Stmt::If {
                        cond: Expr::Binary(
                            "<=",
                            Box::new(Expr::Var("magnitude".into())),
                            Box::new(Expr::Num("2".into())),
                        ),
                        then_body: vec![Stmt::Goto("reset".into())],
                        else_body: Vec::new(),
                    },
                    Stmt::Assign {
                        targets: vec![Expr::Var("deg".into())],
                        values: vec![Expr::Num("2".into())],
                    },
                ],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("sitting".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("self".into())),
                    "Sitting".into(),
                )],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("sitting".into()))),
                then_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("move".into())),
                    Vec::new(),
                ))],
                else_body: vec![
                    Stmt::Label("reset".into()),
                    Stmt::Assign {
                        targets: vec![Expr::Var("lastMoveAngle".into())],
                        values: vec![Expr::Nil],
                    },
                ],
            },
        ];

        recover_gotos_to_later_else_label(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("lastMoveAngle = nil"), "{rendered}");
        assert!(rendered.contains("move()"), "{rendered}");
        assert!(!rendered.contains("goto reset"), "{rendered}");
        assert!(!rendered.contains("::reset::"), "{rendered}");
    }

    #[test]
    fn retargets_missing_goto_to_next_sibling_label() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("skip".into()),
                then_body: vec![Stmt::Goto("missing".into())],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("fallback".into())),
                Vec::new(),
            )),
            Stmt::Label("join".into()),
            Stmt::Call(Expr::Call(Box::new(Expr::Var("tail".into())), Vec::new())),
        ];

        retarget_missing_gotos_to_next_label(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("goto join"), "{rendered}");
        assert!(!rendered.contains("goto missing"), "{rendered}");
    }

    #[test]
    fn recovers_multistmt_orphan_skip_gotos() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("first".into()),
                then_body: vec![
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("setup".into())), Vec::new())),
                    Stmt::If {
                        cond: Expr::Var("done".into()),
                        then_body: vec![Stmt::Goto("join".into())],
                        else_body: Vec::new(),
                    },
                ],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("fallback".into())),
                Vec::new(),
            )),
            Stmt::If {
                cond: Expr::Var("done".into()),
                then_body: vec![Stmt::Goto("join".into())],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("tail".into())), Vec::new())),
        ];

        recover_nested_orphan_skip_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("setup()"), "{rendered}");
        assert!(rendered.contains("fallback()"), "{rendered}");
        assert!(rendered.contains("tail()"), "{rendered}");
        assert!(!rendered.contains("goto join"), "{rendered}");
    }

    #[test]
    fn multistmt_orphan_skip_includes_fallback_assignment() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("fromConfig".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("text".into())],
                        values: vec![Expr::Field(
                            Box::new(Expr::Var("config".into())),
                            "Display".into(),
                        )],
                    },
                    Stmt::Goto("join".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("fromItem".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("text".into())],
                        values: vec![Expr::Field(
                            Box::new(Expr::Var("item".into())),
                            "Display".into(),
                        )],
                    },
                    Stmt::Goto("join".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("text".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("item".into())),
                    "Type".into(),
                )],
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("tail".into())), Vec::new())),
        ];

        recover_nested_orphan_skip_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("text = item.Type"), "{rendered}");
        assert!(rendered.contains("tail()"), "{rendered}");
        assert!(!rendered.contains("goto join"), "{rendered}");
    }

    #[test]
    fn loop_find_goto_becomes_break_with_default_before_loop() {
        let mut stmts = vec![
            Stmt::GenericFor {
                vars: vec!["i".into(), "item".into()],
                exprs: vec![Expr::Var("items".into())],
                body: vec![
                    Stmt::If {
                        cond: Expr::Binary(
                            "~=",
                            Box::new(Expr::Field(Box::new(Expr::Var("item".into())), "id".into())),
                            Box::new(Expr::Var("wanted".into())),
                        ),
                        then_body: vec![Stmt::Continue],
                        else_body: Vec::new(),
                    },
                    Stmt::Assign {
                        targets: vec![Expr::Var("found".into())],
                        values: vec![Expr::Var("item".into())],
                    },
                    Stmt::Goto("found_join".into()),
                ],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("found".into())],
                values: vec![Expr::Nil],
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("found".into()))),
                then_body: vec![Stmt::Return(Vec::new())],
                else_body: Vec::new(),
            },
        ];

        recover_loop_find_breaks(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.starts_with("found = nil"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("if not found then"), "{rendered}");
        assert!(!rendered.contains("goto found_join"), "{rendered}");
    }

    #[test]
    fn loop_find_labeled_join_moves_default_before_loop() {
        let mut stmts = vec![
            Stmt::GenericFor {
                vars: vec!["i".into(), "item".into()],
                exprs: vec![Expr::Var("items".into())],
                body: vec![
                    Stmt::If {
                        cond: Expr::Binary(
                            "~=",
                            Box::new(Expr::Field(
                                Box::new(Expr::Var("item".into())),
                                "Name".into(),
                            )),
                            Box::new(Expr::Str("\"Fruit Magnet\"".into())),
                        ),
                        then_body: vec![Stmt::Continue],
                        else_body: Vec::new(),
                    },
                    Stmt::Assign {
                        targets: vec![Expr::Var("range".into())],
                        values: vec![Expr::Binary(
                            "or",
                            Box::new(Expr::Field(
                                Box::new(Expr::Var("item".into())),
                                "Range".into(),
                            )),
                            Box::new(Expr::Num("63".into())),
                        )],
                    },
                    Stmt::Goto("join".into()),
                ],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("range".into())],
                values: vec![Expr::Num("63".into())],
            },
            Stmt::Label("join".into()),
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("useRange".into())),
                Vec::new(),
            )),
        ];

        recover_loop_find_breaks(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.starts_with("range = 63"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("useRange()"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::join::"), "{rendered}");
    }

    #[test]
    fn loop_find_labeled_join_moves_pure_fallback_block_before_loop() {
        let mut stmts = vec![
            Stmt::GenericFor {
                vars: vec!["i".into(), "entry".into()],
                exprs: vec![Expr::Var("buckets".into())],
                body: vec![
                    Stmt::If {
                        cond: Expr::Binary(
                            ">=",
                            Box::new(Expr::Var("amount".into())),
                            Box::new(Expr::Field(
                                Box::new(Expr::Var("entry".into())),
                                "Max".into(),
                            )),
                        ),
                        then_body: vec![Stmt::Continue],
                        else_body: Vec::new(),
                    },
                    Stmt::Assign {
                        targets: vec![Expr::Var("name".into())],
                        values: vec![Expr::Field(
                            Box::new(Expr::Var("entry".into())),
                            "Name".into(),
                        )],
                    },
                    Stmt::Goto("join".into()),
                ],
            },
            Stmt::Local {
                names: vec!["last".into()],
                values: vec![Expr::Var("buckets".into())],
            },
            Stmt::Local {
                names: vec!["count".into()],
                values: vec![Expr::Unary("#", Box::new(Expr::Var("last".into())))],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("name".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Index(
                        Box::new(Expr::Var("last".into())),
                        Box::new(Expr::Var("count".into())),
                    )),
                    "Name".into(),
                )],
            },
            Stmt::Label("join".into()),
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("useName".into())),
                Vec::new(),
            )),
        ];

        recover_loop_find_breaks(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.starts_with("local last = buckets"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("useName()"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::join::"), "{rendered}");
    }

    #[test]
    fn forward_label_skip_gotos_wrap_short_region() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Unary(
                    "not ",
                    Box::new(Expr::Call(
                        Box::new(Expr::Var("isMouse".into())),
                        Vec::new(),
                    )),
                ),
                then_body: vec![Stmt::If {
                    cond: Expr::Binary(
                        "~=",
                        Box::new(Expr::Var("kind".into())),
                        Box::new(Expr::Var("Keyboard".into())),
                    ),
                    then_body: vec![Stmt::Goto("touch".into())],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("debounced".into()),
                then_body: vec![Stmt::Return(Vec::new())],
                else_body: Vec::new(),
            },
            Stmt::Label("touch".into()),
            Stmt::If {
                cond: Expr::Var("isTouch".into()),
                then_body: vec![Stmt::Assign {
                    targets: vec![Expr::Var("device".into())],
                    values: vec![Expr::Str("\"PC\"".into())],
                }],
                else_body: Vec::new(),
            },
        ];

        recover_forward_label_skip_gotos(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("repeat"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("if isTouch then"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::touch::"), "{rendered}");
    }

    #[test]
    fn forward_label_skip_gotos_wrap_multiple_guards() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("ready".into()))),
                then_body: vec![Stmt::Goto("done".into())],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("elapsed".into())],
                values: vec![Expr::Call(Box::new(Expr::Var("tick".into())), Vec::new())],
            },
            Stmt::If {
                cond: Expr::Var("blocked".into()),
                then_body: vec![Stmt::Goto("done".into())],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Binary(
                    "<",
                    Box::new(Expr::Var("elapsed".into())),
                    Box::new(Expr::Var("duration".into())),
                ),
                then_body: vec![Stmt::Goto("done".into())],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("advance".into())),
                Vec::new(),
            )),
            Stmt::Label("done".into()),
            Stmt::Assign {
                targets: vec![Expr::Var("holding".into())],
                values: vec![Expr::Bool(true)],
            },
        ];

        recover_forward_label_skip_gotos(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("repeat"), "{rendered}");
        assert_eq!(rendered.matches("break").count(), 3, "{rendered}");
        assert!(rendered.contains("holding = true"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::done::"), "{rendered}");
    }

    #[test]
    fn missing_label_skip_to_block_end_wraps_suffix() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("active".into()))),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("state".into())],
                        values: vec![Expr::Str("\"CHARGING\"".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("target".into()))),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("state".into())],
                        values: vec![Expr::Str("\"CHARGING\"".into())],
                    },
                    Stmt::Goto("done".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("root".into()),
                then_body: vec![Stmt::Assign {
                    targets: vec![Expr::Var("state".into())],
                    values: vec![Expr::Str("\"CHARGING\"".into())],
                }],
                else_body: vec![Stmt::Return(Vec::new())],
            },
        ];

        recover_missing_label_skip_to_block_end_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("repeat"), "{rendered}");
        assert_eq!(rendered.matches("break").count(), 2, "{rendered}");
        assert!(rendered.contains("if root then"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn missing_guard_skip_to_block_end_inverts_tail_with_break() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("hasTool".into()))),
                then_body: vec![Stmt::If {
                    cond: Expr::Call(Box::new(Expr::Var("insidePlot".into())), Vec::new()),
                    then_body: vec![Stmt::Goto("done".into())],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("cancelled".into()),
                then_body: vec![Stmt::Break],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("createArrow".into())),
                Vec::new(),
            )),
        ];

        recover_missing_guard_skip_to_block_end_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("if "), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("createArrow()"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn duplicate_labeled_terminal_body_replaces_goto() {
        let terminal_body = vec![
            Stmt::Call(Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("prompt".into())),
                    "Connect".into(),
                )),
                Vec::new(),
            )),
            Stmt::Return(Vec::new()),
        ];
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("humanoid".into()))),
                then_body: {
                    let mut body = vec![Stmt::Label("setup".into())];
                    body.extend(terminal_body.clone());
                    body
                },
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("animator".into()))),
                then_body: {
                    let mut body = vec![Stmt::Label("setup".into())];
                    body.extend(terminal_body.clone());
                    body
                },
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("track".into())],
                values: vec![Expr::Call(
                    Box::new(Expr::Var("loadAnimation".into())),
                    Vec::new(),
                )],
            },
            Stmt::Goto("setup".into()),
        ];

        recover_duplicate_labeled_terminal_bodies(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("track = loadAnimation()"), "{rendered}");
        assert_eq!(rendered.matches("return").count(), 3, "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::setup::"), "{rendered}");
    }

    #[test]
    fn duplicate_labeled_nonterminal_body_replaces_goto() {
        let shared_body = vec![
            Stmt::If {
                cond: Expr::Var("touchInput".into()),
                then_body: vec![Stmt::Return(Vec::new())],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("handler".into())),
                    "Run".into(),
                )),
                Vec::new(),
            )),
        ];
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("mouseInput".into()))),
                then_body: {
                    let mut body = vec![Stmt::Label("fallback".into())];
                    body.extend(shared_body.clone());
                    body
                },
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Unary("not ", Box::new(Expr::Var("permitted".into()))),
                then_body: {
                    let mut body = vec![Stmt::Label("fallback".into())];
                    body.extend(shared_body.clone());
                    body
                },
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("commit".into())), Vec::new())),
            Stmt::Goto("fallback".into()),
        ];

        recover_duplicate_labeled_bodies(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("commit()"), "{rendered}");
        assert_eq!(rendered.matches("handler.Run()").count(), 3, "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::fallback::"), "{rendered}");
    }

    #[test]
    fn recovers_goto_into_nested_labeled_if_gate() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("reuseTrack".into()),
                then_body: vec![Stmt::Goto("sync".into())],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Var("oppositeTrack".into()),
                then_body: vec![Stmt::If {
                    cond: Expr::Var("samePair".into()),
                    then_body: vec![
                        Stmt::Label("sync".into()),
                        Stmt::Call(Expr::Call(
                            Box::new(Expr::Var("syncTracks".into())),
                            Vec::new(),
                        )),
                    ],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
        ];

        recover_goto_into_if_gates(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if reuseTrack or oppositeTrack then"),
            "{rendered}"
        );
        assert!(
            rendered.contains("if reuseTrack or samePair then"),
            "{rendered}"
        );
        assert!(!rendered.contains("goto sync"), "{rendered}");
        assert!(!rendered.contains("::sync::"), "{rendered}");
    }

    #[test]
    fn recovers_top_test_while_goto() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["total".into()],
                values: vec![Expr::Num("0".into())],
            },
            Stmt::Label("loop".into()),
            Stmt::If {
                cond: Expr::Binary(
                    "<",
                    Box::new(Expr::Var("total".into())),
                    Box::new(Expr::Var("limit".into())),
                ),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Var("total".into())],
                        values: vec![Expr::Binary(
                            "+",
                            Box::new(Expr::Var("total".into())),
                            Box::new(Expr::Num("1".into())),
                        )],
                    },
                    Stmt::Goto("loop".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Return(vec![Expr::Var("total".into())]),
        ];

        recover_top_test_while_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("while total < limit do"), "{rendered}");
        assert!(rendered.contains("total += 1"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::loop::"), "{rendered}");
    }

    #[test]
    fn recovers_nested_top_test_while_goto() {
        let mut stmts = vec![
            Stmt::Label("L0".into()),
            Stmt::If {
                cond: Expr::Binary(
                    "<",
                    Box::new(Expr::Var("distance".into())),
                    Box::new(Expr::Var("magnitude".into())),
                ),
                then_body: vec![Stmt::If {
                    cond: Expr::Binary(
                        "<=",
                        Box::new(Expr::Var("total".into())),
                        Box::new(Expr::Var("limit".into())),
                    ),
                    then_body: vec![
                        Stmt::Assign {
                            targets: vec![Expr::Var("total".into())],
                            values: vec![Expr::Binary(
                                "+",
                                Box::new(Expr::Var("total".into())),
                                Box::new(Expr::Num("1".into())),
                            )],
                        },
                        Stmt::Call(Expr::MethodCall(
                            Box::new(Expr::Var("solver".into())),
                            "Step".into(),
                            vec![Expr::Var("target".into())],
                        )),
                        Stmt::Goto("L0".into()),
                    ],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
        ];

        recover_top_test_while_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("while distance < magnitude and total <= limit do"),
            "{rendered}"
        );
        assert!(rendered.contains("solver:Step(target)"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::L0::"), "{rendered}");
    }

    #[test]
    fn keeps_label_with_multiple_incoming_gotos() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("restart".into()),
                then_body: vec![Stmt::Goto("L0".into())],
                else_body: Vec::new(),
            },
            Stmt::Label("L0".into()),
            Stmt::If {
                cond: Expr::Var("running".into()),
                then_body: vec![Stmt::Goto("L0".into())],
                else_body: Vec::new(),
            },
        ];

        recover_top_test_while_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("::L0::"), "{rendered}");
        assert_eq!(rendered.matches("goto L0").count(), 2, "{rendered}");
    }

    #[test]
    fn recovers_if_join_goto_as_else_branch() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("has_canvas_size".into()),
                then_body: vec![
                    Stmt::Assign {
                        targets: vec![Expr::Field(
                            Box::new(Expr::Var("surfaceGui".into())),
                            "CanvasSize".into(),
                        )],
                        values: vec![Expr::Var("canvasSize".into())],
                    },
                    Stmt::Goto("join".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("surfaceGui".into())),
                    "CanvasSize".into(),
                )],
                values: vec![Expr::Call(
                    Box::new(Expr::Field(
                        Box::new(Expr::Var("Vector2".into())),
                        "new".into(),
                    )),
                    vec![Expr::Var("x".into()), Expr::Var("y".into())],
                )],
            },
            Stmt::Label("join".into()),
            Stmt::Return(vec![Expr::Var("surfaceGui".into())]),
        ];

        recover_if_join_gotos(&mut stmts);
        remove_unused_labels(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("else"), "{rendered}");
        assert!(rendered.contains("Vector2.new(x, y)"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::"), "{rendered}");
    }

    #[test]
    fn branch_gotos_to_following_label_become_repeat_breaks() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("enabled".into()),
                then_body: vec![
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("start".into())), Vec::new())),
                    Stmt::If {
                        cond: Expr::Var("done".into()),
                        then_body: vec![Stmt::Goto("joined".into())],
                        else_body: Vec::new(),
                    },
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("finish".into())), Vec::new())),
                    Stmt::Goto("joined".into()),
                ],
                else_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("fallback".into())),
                    Vec::new(),
                ))],
            },
            Stmt::Label("joined".into()),
            Stmt::Call(Expr::Call(Box::new(Expr::Var("after".into())), Vec::new())),
        ];

        recover_branch_gotos_to_following_label(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("repeat"), "{rendered}");
        assert!(rendered.contains("until true"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("after()"), "{rendered}");
        assert!(!rendered.contains("goto joined"), "{rendered}");
        assert!(!rendered.contains("::joined::"), "{rendered}");
    }

    #[test]
    fn recovers_short_orphan_if_join_tail() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("is_model".into()),
                then_body: vec![Stmt::If {
                    cond: Expr::Var("primary_part".into()),
                    then_body: vec![
                        Stmt::Assign {
                            targets: vec![Expr::Var("base_part".into())],
                            values: vec![Expr::Var("primary_part".into())],
                        },
                        Stmt::Goto("missing_join".into()),
                    ],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("base_part".into())],
                values: vec![Expr::MethodCall(
                    Box::new(Expr::Var("instance".into())),
                    "FindFirstChildWhichIsA".into(),
                    vec![Expr::Str("\"BasePart\"".into()), Expr::Bool(true)],
                )],
            },
        ];

        recover_orphan_if_join_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("else"), "{rendered}");
        assert!(rendered.contains("base_part = primary_part"), "{rendered}");
        assert!(
            rendered.contains("base_part = instance:FindFirstChildWhichIsA"),
            "{rendered}"
        );
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn leaves_long_orphan_if_join_tail() {
        let mut stmts = vec![Stmt::If {
            cond: Expr::Var("accepted".into()),
            then_body: vec![Stmt::Goto("missing_join".into())],
            else_body: Vec::new(),
        }];
        for i in 0..9 {
            stmts.push(Stmt::Assign {
                targets: vec![Expr::Var(format!("v{i}"))],
                values: vec![Expr::Num(i.to_string())],
            });
        }
        stmts.push(Stmt::Goto("other".into()));

        recover_orphan_if_join_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("goto missing_join"), "{rendered}");
    }

    #[test]
    fn recovers_orphan_skip_to_terminal_tail() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Binary(
                    "~=",
                    Box::new(Expr::Var("name".into())),
                    Box::new(Expr::Str("\"acceleration\"".into())),
                ),
                then_body: vec![Stmt::If {
                    cond: Expr::Binary(
                        "~=",
                        Box::new(Expr::Var("name".into())),
                        Box::new(Expr::Str("\"a\"".into())),
                    ),
                    then_body: vec![Stmt::Goto("missing_end".into())],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("value".into())],
                values: vec![Expr::Call(
                    Box::new(Expr::Var("compute".into())),
                    Vec::new(),
                )],
            },
            Stmt::Return(vec![Expr::Var("value".into())]),
        ];

        recover_orphan_if_join_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("if name == \"acceleration\" or name == \"a\" then"),
            "{rendered}"
        );
        assert!(rendered.contains("return value"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
    }

    #[test]
    fn leaves_orphan_skip_tail_with_fallback_control_flow() {
        let mut stmts = vec![Stmt::If {
            cond: Expr::Var("skip".into()),
            then_body: vec![Stmt::Goto("missing_end".into())],
            else_body: Vec::new(),
        }];
        for i in 0..9 {
            stmts.push(Stmt::Assign {
                targets: vec![Expr::Var("value".into())],
                values: vec![Expr::Num(i.to_string())],
            });
        }
        stmts.push(Stmt::Goto("other".into()));

        recover_orphan_if_join_gotos(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("goto missing_end"), "{rendered}");
    }

    #[test]
    fn merges_leading_while_break_guard() {
        let mut stmts = vec![Stmt::While {
            cond: Expr::Binary(
                "<",
                Box::new(Expr::Var("distance".into())),
                Box::new(Expr::Var("magnitude".into())),
            ),
            body: vec![
                Stmt::If {
                    cond: Expr::Binary(
                        ">",
                        Box::new(Expr::Var("total".into())),
                        Box::new(Expr::Var("limit".into())),
                    ),
                    then_body: vec![Stmt::Break],
                    else_body: Vec::new(),
                },
                Stmt::Assign {
                    targets: vec![Expr::Var("total".into())],
                    values: vec![Expr::Binary(
                        "+",
                        Box::new(Expr::Var("total".into())),
                        Box::new(Expr::Num("1".into())),
                    )],
                },
            ],
        }];

        merge_leading_while_break_guards(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(
            rendered.contains("while distance < magnitude and total <= limit do"),
            "{rendered}"
        );
        assert!(!rendered.contains("break"), "{rendered}");
        assert!(rendered.contains("total += 1"), "{rendered}");
    }

    #[test]
    fn keeps_nonleading_while_break_guard() {
        let mut stmts = vec![Stmt::While {
            cond: Expr::Var("running".into()),
            body: vec![
                Stmt::Call(Expr::Call(Box::new(Expr::Var("step".into())), Vec::new())),
                Stmt::If {
                    cond: Expr::Var("done".into()),
                    then_body: vec![Stmt::Break],
                    else_body: Vec::new(),
                },
            ],
        }];

        merge_leading_while_break_guards(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("while running do"), "{rendered}");
        assert!(rendered.contains("if done then"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
    }

    #[test]
    fn removes_redundant_goto_adjacent_to_label() {
        let mut stmts = vec![
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Str("\"hello\"".into())],
            )),
            Stmt::Goto("L0".into()),
            Stmt::Comment("some comment".into()),
            Stmt::Label("L0".into()),
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Str("\"world\"".into())],
            )),
        ];
        remove_redundant_gotos(&mut stmts);
        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("goto L0"), "{rendered}");
        assert!(rendered.contains("::L0::"), "{rendered}");
    }

    #[test]
    fn removes_trailing_sibling_gotos_in_if() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("enabled".into()),
                then_body: vec![
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("print".into())), Vec::new())),
                    Stmt::Goto("L1".into()),
                ],
                else_body: vec![
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("warn".into())), Vec::new())),
                    Stmt::Goto("L1".into()),
                ],
            },
            Stmt::Label("L1".into()),
        ];
        remove_trailing_sibling_gotos(&mut stmts);
        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("goto L1"), "{rendered}");
        assert!(rendered.contains("::L1::"), "{rendered}");
    }

    #[test]
    fn removes_unused_labels_recursively() {
        let mut stmts = vec![
            Stmt::Label("Unused".into()),
            Stmt::Call(Expr::Call(Box::new(Expr::Var("print".into())), Vec::new())),
            Stmt::Label("Used".into()),
            Stmt::If {
                cond: Expr::Var("cond".into()),
                then_body: vec![Stmt::Goto("Used".into())],
                else_body: Vec::new(),
            },
        ];
        remove_unused_labels(&mut stmts);
        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("::Unused::"), "{rendered}");
        assert!(rendered.contains("::Used::"), "{rendered}");
    }

    #[test]
    fn recovers_if_else_from_gotos() {
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::Var("enabled".into()),
                then_body: vec![Stmt::Goto("L_else".into())],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Str("\"then\"".into())],
            )),
            Stmt::Goto("L_end".into()),
            Stmt::Label("L_else".into()),
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Str("\"else\"".into())],
            )),
            Stmt::Label("L_end".into()),
        ];
        recover_if_else_gotos(&mut stmts);
        remove_unused_labels(&mut stmts);
        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("if not enabled then"), "{rendered}");
        assert!(rendered.contains("print(\"then\")"), "{rendered}");
        assert!(rendered.contains("else"), "{rendered}");
        assert!(rendered.contains("print(\"else\")"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::L_else::"), "{rendered}");
        assert!(!rendered.contains("::L_end::"), "{rendered}");
    }

    #[test]
    fn recovers_backward_goto_while_loop() {
        let mut stmts = vec![
            Stmt::Label("L0".into()),
            Stmt::If {
                cond: Expr::Var("exit_cond".into()),
                then_body: vec![Stmt::Goto("L1".into())],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Str("\"body\"".into())],
            )),
            Stmt::Goto("L0".into()),
            Stmt::Label("L1".into()),
        ];
        recover_backward_goto_while(&mut stmts);
        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("while not exit_cond do"), "{rendered}");
        assert!(rendered.contains("print(\"body\")"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::L0::"), "{rendered}");
        assert!(!rendered.contains("::L1::"), "{rendered}");
    }

    #[test]
    fn recovers_label_loop_with_iteration_setup_and_nested_backedge() {
        let mut stmts = vec![
            Stmt::Label("L0".into()),
            Stmt::Local {
                names: vec!["remaining".into()],
                values: vec![Expr::Var("budget".into())],
            },
            Stmt::Local {
                names: vec!["step".into()],
                values: vec![Expr::Num("1".into())],
            },
            Stmt::If {
                cond: Expr::Binary(
                    ">",
                    Box::new(Expr::Var("remaining".into())),
                    Box::new(Expr::Num("0".into())),
                ),
                then_body: vec![Stmt::If {
                    cond: Expr::Binary(
                        "<",
                        Box::new(Expr::Var("count".into())),
                        Box::new(Expr::Num("7".into())),
                    ),
                    then_body: vec![
                        Stmt::NumericFor {
                            var: "i".into(),
                            start: Expr::Num("1".into()),
                            limit: Expr::Num("2".into()),
                            step: None,
                            body: vec![Stmt::Call(Expr::Call(
                                Box::new(Expr::Var("tick".into())),
                                Vec::new(),
                            ))],
                        },
                        Stmt::Assign {
                            targets: vec![Expr::Var("budget".into())],
                            values: vec![Expr::Binary(
                                "-",
                                Box::new(Expr::Var("budget".into())),
                                Box::new(Expr::Var("step".into())),
                            )],
                        },
                        Stmt::Assign {
                            targets: vec![Expr::Var("count".into())],
                            values: vec![Expr::Binary(
                                "+",
                                Box::new(Expr::Var("count".into())),
                                Box::new(Expr::Num("1".into())),
                            )],
                        },
                        Stmt::Goto("L0".into()),
                    ],
                    else_body: Vec::new(),
                }],
                else_body: Vec::new(),
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("done".into())), Vec::new())),
        ];

        recover_natural_loops(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("while true do"), "{rendered}");
        assert!(rendered.contains("continue"), "{rendered}");
        assert!(rendered.contains("break"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::L0::"), "{rendered}");
    }

    #[test]
    fn recovers_repeat_until_return_goto_loop() {
        let mut stmts = vec![
            Stmt::Label("L0".into()),
            Stmt::Assign {
                targets: vec![Expr::Var("tries".into())],
                values: vec![Expr::Binary(
                    "+",
                    Box::new(Expr::Var("tries".into())),
                    Box::new(Expr::Num("1".into())),
                )],
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("save".into())), Vec::new())),
            Stmt::If {
                cond: Expr::Var("saved".into()),
                then_body: vec![Stmt::Return(vec![
                    Expr::Var("saved".into()),
                    Expr::Var("lastError".into()),
                ])],
                else_body: Vec::new(),
            },
            Stmt::If {
                cond: Expr::Binary(
                    ">=",
                    Box::new(Expr::Var("tries".into())),
                    Box::new(Expr::Num("3".into())),
                ),
                then_body: vec![Stmt::Return(vec![
                    Expr::Var("saved".into()),
                    Expr::Var("lastError".into()),
                ])],
                else_body: Vec::new(),
            },
            Stmt::Goto("L0".into()),
        ];

        recover_backward_goto_while(&mut stmts);

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("repeat"), "{rendered}");
        assert!(rendered.contains("until saved or tries >= 3"), "{rendered}");
        assert!(rendered.contains("return saved, lastError"), "{rendered}");
        assert!(!rendered.contains("goto"), "{rendered}");
        assert!(!rendered.contains("::L0::"), "{rendered}");
    }

    #[test]
    fn folds_table_literals_respects_intermediate_dependencies() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["t".into()],
                values: vec![Expr::Table(Vec::new())],
            },
            Stmt::Local {
                names: vec!["temp".into()],
                values: vec![Expr::Num("1".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Index(
                    Box::new(Expr::Var("t".into())),
                    Box::new(Expr::Num("1".into())),
                )],
                values: vec![Expr::Var("temp".into())],
            },
        ];

        fold_table_literals(&mut stmts);

        // Should NOT fold yet because temp is written in between
        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("t[1] = temp"), "{rendered}");
        assert!(!rendered.contains("t = {temp}"), "{rendered}");
    }

    #[test]
    fn split_reused_registers_disjoint() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["v1".into()],
                values: vec![Expr::Num("5".into())],
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Var("v1".into())],
            )),
            Stmt::Assign {
                targets: vec![Expr::Var("v1".into())],
                values: vec![Expr::Num("10".into())],
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Var("v1".into())],
            )),
        ];

        split_reused_registers(&mut stmts, &BTreeSet::new());

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("local v1_1 = 5"), "{rendered}");
        assert!(rendered.contains("print(v1_1)"), "{rendered}");
        assert!(rendered.contains("v1_2 = 10"), "{rendered}");
        assert!(rendered.contains("print(v1_2)"), "{rendered}");
    }

    #[test]
    fn split_reused_registers_skip_unsplittable() {
        let mut stmts = vec![
            Stmt::Local {
                names: vec!["v1".into()],
                values: vec![Expr::Num("5".into())],
            },
            Stmt::If {
                cond: Expr::Bool(true),
                then_body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("print".into())),
                    vec![Expr::Var("v1".into())],
                ))],
                else_body: Vec::new(),
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v1".into())],
                values: vec![Expr::Num("10".into())],
            },
            Stmt::Call(Expr::Call(
                Box::new(Expr::Var("print".into())),
                vec![Expr::Var("v1".into())],
            )),
        ];

        split_reused_registers(&mut stmts, &BTreeSet::new());

        let rendered = render_block(&stmts, 0);
        assert!(rendered.contains("local v1 = 5"), "{rendered}");
        assert!(rendered.contains("v1 = 10"), "{rendered}");
    }

    #[test]
    fn recovers_unstructured_backward_goto_loop() {
        // `::L1:: <body> goto L1` (unconditional back-edge) -> `while true do <body> end`.
        let mut stmts = vec![
            Stmt::Label("L1".into()),
            Stmt::Assign {
                targets: vec![Expr::Var("x".into())],
                values: vec![Expr::Num("1".into())],
            },
            Stmt::If {
                cond: Expr::Var("done".into()),
                then_body: vec![Stmt::Return(vec![])],
                else_body: Vec::new(),
            },
            Stmt::Goto("L1".into()),
        ];
        recover_unstructured_backward_loops(&mut stmts);
        assert_eq!(stmts.len(), 1, "{}", render_block(&stmts, 0));
        let Stmt::While { cond, body } = &stmts[0] else {
            panic!("expected while loop, got {}", render_block(&stmts, 0));
        };
        assert_eq!(*cond, Expr::Bool(true));
        assert_eq!(body.len(), 2); // the assign and the if; no goto/label remain
        let rendered = render_block(&stmts, 0);
        assert!(!rendered.contains("goto") && !rendered.contains("::"), "{rendered}");

        // Nested same-named labels: inner loop is recovered first (count-of-one holds per level).
        let mut nested = vec![
            Stmt::Label("L1".into()),
            Stmt::If {
                cond: Expr::Var("c".into()),
                then_body: vec![
                    Stmt::Label("L1".into()),
                    Stmt::Call(Expr::Call(Box::new(Expr::Var("f".into())), vec![])),
                    Stmt::Goto("L1".into()),
                ],
                else_body: Vec::new(),
            },
            Stmt::Goto("L1".into()),
        ];
        recover_unstructured_backward_loops(&mut nested);
        let rendered = render_block(&nested, 0);
        assert!(!rendered.contains("goto") && !rendered.contains("::"), "{rendered}");
    }
}

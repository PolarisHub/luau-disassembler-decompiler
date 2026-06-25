//! A small Luau AST and a printer. The decompiler builds this tree, then renders it.
//!
//! Some statement/expression variants (the structured loops, `if`, table fields) are part
//! of the AST and printer but are only produced once native structuring is wired up; the
//! first-pass decompiler emits the goto/label fallback instead. They are exercised by the
//! printer unit tests, so the `allow(dead_code)` is about "not yet produced by the
//! reconstructor", not unused code.
#![allow(dead_code)]

use std::fmt::Write;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Nil,
    Bool(bool),
    /// A number rendered already as text (so we can reuse the disassembler's exact float
    /// formatting and integer rendering).
    Num(String),
    /// A quoted, escaped string literal (already includes the quotes).
    Str(String),
    Vector(String),
    /// A bare identifier: a local name, a synthesized name, or a resolved global/import path.
    Var(String),
    /// `table[key]`
    Index(Box<Expr>, Box<Expr>),
    /// `table.field` (field is a valid identifier)
    Field(Box<Expr>, String),
    Call(Box<Expr>, Vec<Expr>),
    MethodCall(Box<Expr>, String, Vec<Expr>),
    Unary(&'static str, Box<Expr>),
    /// Binary op; `op` is the Luau operator text (`+`, `..`, `==`, `and`, ...).
    Binary(&'static str, Box<Expr>, Box<Expr>),
    Table(Vec<TableField>),
    /// `...`
    Vararg,
    /// A function literal: the rendered body text plus, in order, what each upvalue captures
    /// from the enclosing function. The upvalues read as `u0`, `u1`, … in `text` until the
    /// enclosing function resolves them to its real names (see `resolve_closure_upvalues`).
    Closure {
        text: String,
        captures: Vec<Capture>,
    },
    /// Fallback raw text (e.g. `R3 --[[?]]`) for things we couldn't reconstruct.
    Raw(String),
}

/// What a closure upvalue captures from its enclosing function.
#[derive(Debug, Clone, PartialEq)]
pub enum Capture {
    /// A register (local) of the enclosing function.
    Reg(u8),
    /// An upvalue of the enclosing function (a chained capture).
    Upval(u8),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TableField {
    /// positional array item
    Item(Expr),
    /// `name = value`
    Named(String, Expr),
    /// `[key] = value`
    Keyed(Expr, Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// `local a, b = e1, e2`
    Local {
        names: Vec<String>,
        values: Vec<Expr>,
    },
    /// `lhs1, lhs2 = e1, e2`
    Assign {
        targets: Vec<Expr>,
        values: Vec<Expr>,
    },
    /// an expression (a call) evaluated for its effects
    Call(Expr),
    Return(Vec<Expr>),
    Break,
    Continue,
    /// `if cond then <then> [else <else_>] end`. elseif chains are nested else-ifs.
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    While {
        cond: Expr,
        body: Vec<Stmt>,
    },
    Repeat {
        body: Vec<Stmt>,
        cond: Expr,
    },
    NumericFor {
        var: String,
        start: Expr,
        limit: Expr,
        step: Option<Expr>,
        body: Vec<Stmt>,
    },
    GenericFor {
        vars: Vec<String>,
        exprs: Vec<Expr>,
        body: Vec<Stmt>,
    },
    /// A `::label::` marker (used by the goto fallback).
    Label(String),
    /// `goto label`
    Goto(String),
    /// A free-standing comment line, e.g. honesty markers.
    Comment(String),
}

pub fn render_block(stmts: &[Stmt], indent: usize) -> String {
    let mut out = String::new();
    let block_len = stmts.len();
    for (index, s) in stmts.iter().enumerate() {
        if index > 0 && wants_blank_line_between(&stmts[index - 1], s, block_len, indent) {
            out.push('\n');
        }
        render_stmt(&mut out, s, indent);
    }
    out
}

fn wants_blank_line_between(prev: &Stmt, next: &Stmt, block_len: usize, indent: usize) -> bool {
    if block_len <= 2 && indent > 0 {
        return renders_as_function(prev) || renders_as_function(next);
    }
    if block_len <= 4 && indent > 0 && matches!(next, Stmt::Return(_)) {
        return false;
    }
    renders_as_function(prev)
        || renders_as_function(next)
        || renders_as_block(prev)
        || renders_as_block(next)
        || matches!(next, Stmt::Return(_))
}

fn renders_as_function(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Local { names, values } => local_function_text(names, values, 0).is_some(),
        Stmt::Assign { targets, values } => assignment_function_text(targets, values, 0).is_some(),
        _ => false,
    }
}

fn renders_as_block(stmt: &Stmt) -> bool {
    matches!(
        stmt,
        Stmt::If { .. }
            | Stmt::While { .. }
            | Stmt::Repeat { .. }
            | Stmt::NumericFor { .. }
            | Stmt::GenericFor { .. }
    )
}

fn pad(out: &mut String, indent: usize) {
    for _ in 0..indent {
        out.push('\t');
    }
}

fn render_stmt(out: &mut String, s: &Stmt, indent: usize) {
    match s {
        Stmt::Local { names, values } => {
            if let Some(text) = local_function_text(names, values, indent) {
                pad(out, indent);
                out.push_str(&text);
                out.push('\n');
                return;
            }
            pad(out, indent);
            let _ = write!(out, "local {}", names.join(", "));
            if !values.is_empty() {
                let _ = write!(out, " = {}", join_exprs_at(values, indent));
            }
            out.push('\n');
        }
        Stmt::Assign { targets, values } => {
            if let Some(text) = assignment_function_text(targets, values, indent) {
                pad(out, indent);
                out.push_str(&text);
                out.push('\n');
                return;
            }
            if let Some((target, op, rhs)) = compound_assignment_parts(targets, values) {
                pad(out, indent);
                let _ = writeln!(
                    out,
                    "{} {op}= {}",
                    render_expr_at(target, indent),
                    render_expr_at(rhs, indent)
                );
                return;
            }
            pad(out, indent);
            let _ = writeln!(
                out,
                "{} = {}",
                join_exprs_at(targets, indent),
                join_exprs_at(values, indent)
            );
        }
        Stmt::Call(e) => {
            pad(out, indent);
            let _ = writeln!(out, "{}", render_expr_at(e, indent));
        }
        Stmt::Return(exprs) => {
            pad(out, indent);
            if exprs.is_empty() {
                out.push_str("return\n");
            } else {
                let _ = writeln!(out, "return {}", join_exprs_at(exprs, indent));
            }
        }
        Stmt::Break => {
            pad(out, indent);
            out.push_str("break\n");
        }
        Stmt::Continue => {
            pad(out, indent);
            out.push_str("continue\n");
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            render_if_statement(out, cond, then_body, else_body, indent);
        }
        Stmt::While { cond, body } => {
            pad(out, indent);
            let _ = writeln!(out, "while {} do", render_expr_at(cond, indent));
            out.push_str(&render_block(body, indent + 1));
            pad(out, indent);
            out.push_str("end\n");
        }
        Stmt::Repeat { body, cond } => {
            pad(out, indent);
            out.push_str("repeat\n");
            out.push_str(&render_block(body, indent + 1));
            pad(out, indent);
            let _ = writeln!(out, "until {}", render_expr_at(cond, indent));
        }
        Stmt::NumericFor {
            var,
            start,
            limit,
            step,
            body,
        } => {
            pad(out, indent);
            match step {
                Some(s) => {
                    let _ = writeln!(
                        out,
                        "for {var} = {}, {}, {} do",
                        render_expr_at(start, indent),
                        render_expr_at(limit, indent),
                        render_expr_at(s, indent)
                    );
                }
                None => {
                    let _ = writeln!(
                        out,
                        "for {var} = {}, {} do",
                        render_expr_at(start, indent),
                        render_expr_at(limit, indent)
                    );
                }
            }
            out.push_str(&render_block(body, indent + 1));
            pad(out, indent);
            out.push_str("end\n");
        }
        Stmt::GenericFor { vars, exprs, body } => {
            pad(out, indent);
            let _ = writeln!(
                out,
                "for {} in {} do",
                vars.join(", "),
                join_generic_for_exprs_at(exprs, indent)
            );
            out.push_str(&render_block(body, indent + 1));
            pad(out, indent);
            out.push_str("end\n");
        }
        Stmt::Label(name) => {
            pad(out, indent);
            let _ = writeln!(out, "::{name}::");
        }
        Stmt::Goto(name) => {
            pad(out, indent);
            let _ = writeln!(out, "goto {name}");
        }
        Stmt::Comment(text) => {
            pad(out, indent);
            let _ = writeln!(out, "-- {text}");
        }
    }
}

fn render_if_statement(
    out: &mut String,
    cond: &Expr,
    then_body: &[Stmt],
    else_body: &[Stmt],
    indent: usize,
) {
    pad(out, indent);
    let _ = writeln!(out, "if {} then", render_expr_at(cond, indent));
    out.push_str(&render_block(then_body, indent + 1));
    render_else_tail(out, else_body, indent);
}

fn render_else_tail(out: &mut String, else_body: &[Stmt], indent: usize) {
    match else_body {
        [] => {}
        [Stmt::If {
            cond,
            then_body,
            else_body,
        }] => {
            pad(out, indent);
            let _ = writeln!(out, "elseif {} then", render_expr_at(cond, indent));
            out.push_str(&render_block(then_body, indent + 1));
            render_else_tail(out, else_body, indent);
            return;
        }
        _ => {
            pad(out, indent);
            out.push_str("else\n");
            out.push_str(&render_block(else_body, indent + 1));
        }
    }
    pad(out, indent);
    out.push_str("end\n");
}

fn local_function_text(names: &[String], values: &[Expr], indent: usize) -> Option<String> {
    let [name] = names else {
        return None;
    };
    let [Expr::Closure { text, .. }] = values else {
        return None;
    };
    let tail = text.strip_prefix("function")?;
    Some(format!(
        "local function {name}{}",
        indent_multiline(tail, indent)
    ))
}

fn assignment_function_text(targets: &[Expr], values: &[Expr], indent: usize) -> Option<String> {
    let [target] = targets else {
        return None;
    };
    let [Expr::Closure { text, .. }] = values else {
        return None;
    };
    if let Some(sugared) = method_colon_sugar(target, text, indent) {
        return Some(sugared);
    }
    let name = function_assignment_target(target)?;
    let tail = text.strip_prefix("function")?;
    Some(format!("function {name}{}", indent_multiline(tail, indent)))
}

fn method_colon_sugar(target: &Expr, text: &str, indent: usize) -> Option<String> {
    let Expr::Field(base, field) = target else {
        return None;
    };
    let base_name = function_assignment_target(base)?;
    let tail = text.strip_prefix("function")?;
    let tail_trimmed = tail.trim_start();
    if !tail_trimmed.starts_with('(') {
        return None;
    }
    let after_paren = &tail_trimmed[1..];
    let close_paren_idx = after_paren.find(')')?;
    let params_part = &after_paren[..close_paren_idx];
    let params_trimmed = params_part.trim();

    let (new_params, body_part) = if params_trimmed == "self" {
        ("()".to_string(), &after_paren[close_paren_idx + 1..])
    } else if let Some(rest) = params_trimmed.strip_prefix("self") {
        let rest = rest.trim_start();
        if let Some(remaining) = rest.strip_prefix(',') {
            let remaining = remaining.trim();
            (
                format!("({remaining})"),
                &after_paren[close_paren_idx + 1..],
            )
        } else {
            return None;
        }
    } else {
        return None;
    };

    let sugar_signature = format!("function {base_name}:{field}{new_params}{body_part}");
    Some(indent_multiline(&sugar_signature, indent))
}

fn function_assignment_target(target: &Expr) -> Option<String> {
    match target {
        Expr::Var(name) => Some(name.clone()),
        Expr::Field(base, field) => {
            function_assignment_target(base).map(|base| format!("{base}.{field}"))
        }
        _ => None,
    }
}

fn compound_assignment_parts<'a>(
    targets: &'a [Expr],
    values: &'a [Expr],
) -> Option<(&'a Expr, &'static str, &'a Expr)> {
    let [target @ Expr::Var(name)] = targets else {
        return None;
    };
    let [Expr::Binary(op, left, right)] = values else {
        return None;
    };
    if !compound_assignment_op(op)
        || !matches!(left.as_ref(), Expr::Var(left_name) if left_name == name)
    {
        return None;
    }
    Some((target, op, right))
}

fn compound_assignment_op(op: &str) -> bool {
    matches!(op, "+" | "-" | "*" | "/" | "//" | "%" | "^" | "..")
}

fn join_exprs(exprs: &[Expr]) -> String {
    exprs.iter().map(render_expr).collect::<Vec<_>>().join(", ")
}

fn join_exprs_at(exprs: &[Expr], indent: usize) -> String {
    exprs
        .iter()
        .map(|e| render_expr_at(e, indent))
        .collect::<Vec<_>>()
        .join(", ")
}

fn join_generic_for_exprs_at(exprs: &[Expr], indent: usize) -> String {
    let mut end = exprs.len();
    while end > 1 && matches!(exprs[end - 1], Expr::Nil) {
        end -= 1;
    }
    join_exprs_at(&exprs[..end], indent)
}

pub fn render_expr(e: &Expr) -> String {
    render_expr_at(e, 0)
}

fn render_expr_at(e: &Expr, indent: usize) -> String {
    match e {
        Expr::Nil => "nil".to_string(),
        Expr::Bool(b) => b.to_string(),
        Expr::Num(s) => render_number(s),
        Expr::Str(s) | Expr::Vector(s) | Expr::Var(s) | Expr::Raw(s) => s.clone(),
        Expr::Closure { text, .. } => indent_multiline(text, indent),
        Expr::Vararg => "...".to_string(),
        Expr::Index(t, k) => format!("{}[{}]", prefix_at(t, indent), render_expr_at(k, indent)),
        Expr::Field(t, f) => format!("{}.{}", prefix_at(t, indent), f),
        Expr::Call(f, args) => format!("{}({})", prefix_at(f, indent), join_exprs_at(args, indent)),
        Expr::MethodCall(o, m, args) => {
            format!(
                "{}:{}({})",
                prefix_at(o, indent),
                m,
                join_exprs_at(args, indent)
            )
        }
        Expr::Unary(op, a) => {
            // `not` needs a space; symbolic ops don't.
            if *op == "not " {
                format!("not {}", unary_operand_at(op, a, indent))
            } else {
                format!("{op}{}", unary_operand_at(op, a, indent))
            }
        }
        Expr::Binary(op, a, b) => {
            if let Some(flipped) = flipped_comparison(op) {
                if is_literal_expr(a) && !is_literal_expr(b) {
                    let lhs = binary_operand_at(b, flipped, false, indent);
                    let rhs = binary_operand_at(a, flipped, true, indent);
                    return format!("{lhs} {flipped} {rhs}");
                }
            }
            let lhs = binary_operand_at(a, op, false, indent);
            let rhs = binary_operand_at(b, op, true, indent);
            format!("{lhs} {op} {rhs}")
        }
        Expr::Table(fields) => render_table(fields, indent),
    }
}

fn render_number(text: &str) -> String {
    let Ok(value) = text.parse::<f64>() else {
        return text.to_string();
    };
    if !value.is_finite() {
        return text.to_string();
    }

    let candidate = value.to_string();
    if candidate.len() >= text.len() {
        return text.to_string();
    }
    match candidate.parse::<f64>() {
        Ok(roundtrip) if roundtrip.to_bits() == value.to_bits() => candidate,
        _ => text.to_string(),
    }
}

fn op_precedence(op: &str) -> usize {
    match op {
        "or" => 1,
        "and" => 2,
        "==" | "~=" | "<" | "<=" | ">" | ">=" => 3,
        ".." => 4,
        "+" | "-" => 5,
        "*" | "/" | "//" | "%" => 6,
        "^" => 8,
        _ => 0,
    }
}

fn is_right_associative(op: &str) -> bool {
    matches!(op, "^" | "..")
}

fn unary_operand_at(op: &str, a: &Expr, indent: usize) -> String {
    let needs_paren = match a {
        Expr::Binary(bin_op, _, _) => op_precedence(bin_op) < 7,
        Expr::Unary(inner_op, _) => op.trim() == "-" && inner_op.trim() == "-",
        _ => false,
    };

    if needs_paren {
        format!("({})", render_expr_at(a, indent))
    } else {
        render_expr_at(a, indent)
    }
}

fn binary_operand_at(e: &Expr, parent_op: &str, is_rhs: bool, indent: usize) -> String {
    if !matches!(e, Expr::Binary(..) | Expr::Unary(..)) {
        return render_expr_at(e, indent);
    }

    let needs_paren = match e {
        Expr::Unary(..) => {
            let p_parent = op_precedence(parent_op);
            p_parent > 7
        }
        Expr::Binary(op, _, _) => {
            let p_parent = op_precedence(parent_op);
            let p_child = op_precedence(op);
            if p_child < p_parent {
                true
            } else if p_child > p_parent {
                parent_op == "or" && *op == "and"
            } else {
                if is_comparison_op(parent_op) {
                    true
                } else {
                    let right_assoc = is_right_associative(parent_op);
                    if right_assoc {
                        !is_rhs
                    } else {
                        is_rhs
                    }
                }
            }
        }
        _ => false,
    };

    if needs_paren {
        format!("({})", render_expr_at(e, indent))
    } else {
        render_expr_at(e, indent)
    }
}

fn is_comparison_op(op: &str) -> bool {
    matches!(op, "==" | "~=" | "<" | "<=" | ">" | ">=")
}

fn flipped_comparison(op: &str) -> Option<&'static str> {
    Some(match op {
        "<" => ">",
        "<=" => ">=",
        ">" => "<",
        ">=" => "<=",
        "==" => "==",
        "~=" => "~=",
        _ => return None,
    })
}

fn is_literal_expr(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Nil | Expr::Bool(_) | Expr::Num(_) | Expr::Str(_) | Expr::Vector(_)
    )
}

fn render_table(fields: &[TableField], indent: usize) -> String {
    if fields.is_empty() {
        return "{}".to_string();
    }
    if !table_needs_multiline(fields) {
        let parts: Vec<String> = fields
            .iter()
            .map(|fld| render_table_field(fld, indent))
            .collect();
        return format!("{{{}}}", parts.join(", "));
    }

    let mut out = String::new();
    out.push_str("{\n");
    for fld in fields {
        pad(&mut out, indent + 1);
        out.push_str(&render_table_field(fld, indent + 1));
        out.push_str(",\n");
    }
    pad(&mut out, indent);
    out.push('}');
    out
}

fn render_table_field(fld: &TableField, indent: usize) -> String {
    match fld {
        TableField::Item(e) => render_expr_at(e, indent),
        TableField::Named(n, e) => format!("{n} = {}", render_expr_at(e, indent)),
        TableField::Keyed(k, v) => {
            format!(
                "[{}] = {}",
                render_expr_at(k, indent),
                render_expr_at(v, indent)
            )
        }
    }
}

fn table_needs_multiline(fields: &[TableField]) -> bool {
    fields.len() > 3
        || fields.iter().any(|f| match f {
            TableField::Item(e) | TableField::Named(_, e) => expr_needs_multiline(e),
            TableField::Keyed(k, v) => expr_needs_multiline(k) || expr_needs_multiline(v),
        })
}

fn expr_needs_multiline(e: &Expr) -> bool {
    match e {
        Expr::Closure { .. } => true,
        Expr::Table(fields) => table_needs_multiline(fields),
        Expr::Index(t, k) => expr_needs_multiline(t) || expr_needs_multiline(k),
        Expr::Field(t, _) => expr_needs_multiline(t),
        Expr::Call(f, args) => expr_needs_multiline(f) || args.iter().any(expr_needs_multiline),
        Expr::MethodCall(o, _, args) => {
            expr_needs_multiline(o) || args.iter().any(expr_needs_multiline)
        }
        Expr::Unary(_, a) => expr_needs_multiline(a),
        Expr::Binary(_, a, b) => expr_needs_multiline(a) || expr_needs_multiline(b),
        _ => false,
    }
}

fn indent_multiline(text: &str, indent: usize) -> String {
    if !text.contains('\n') || indent == 0 {
        return text.to_string();
    }
    let mut out = String::new();
    for (i, line) in text.lines().enumerate() {
        if i > 0 {
            out.push('\n');
            if !line.is_empty() {
                pad(&mut out, indent);
            }
        }
        out.push_str(line);
    }
    if text.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Parenthesize a sub-expression when needed to keep precedence unambiguous. We are
/// conservative: wrap any binary/unary operand that is itself a binary/unary expression.
fn paren(e: &Expr) -> String {
    paren_at(e, 0)
}

fn paren_at(e: &Expr, indent: usize) -> String {
    match e {
        Expr::Binary(..) | Expr::Unary(..) => format!("({})", render_expr_at(e, indent)),
        _ => render_expr_at(e, indent),
    }
}

/// Render an expression used as a *prefix expression* — the base of a call, method call,
/// index, or field access. Lua's grammar only allows a name, another prefix expression, or a
/// parenthesized expression there, so anything else (a function literal, string, table,
/// binary op, …) must be wrapped: `(function() end)()`, `("s"):upper()`, `({}).x`.
fn prefix(e: &Expr) -> String {
    prefix_at(e, 0)
}

fn prefix_at(e: &Expr, indent: usize) -> String {
    match e {
        Expr::Var(_)
        | Expr::Raw(_)
        | Expr::Index(..)
        | Expr::Field(..)
        | Expr::Call(..)
        | Expr::MethodCall(..) => render_expr_at(e, indent),
        _ => format!("({})", render_expr_at(e, indent)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prints_structured_constructs() {
        let body = vec![Stmt::Assign {
            targets: vec![Expr::Var("acc".into())],
            values: vec![Expr::Binary(
                "+",
                Box::new(Expr::Var("acc".into())),
                Box::new(Expr::Var("i".into())),
            )],
        }];
        let nf = Stmt::NumericFor {
            var: "i".into(),
            start: Expr::Num("1".into()),
            limit: Expr::Var("n".into()),
            step: None,
            body: body.clone(),
        };
        let rendered = render_block(&[nf], 0);
        assert_eq!(rendered, "for i = 1, n do\n\tacc += i\nend\n");

        let iff = Stmt::If {
            cond: Expr::Binary(
                ">",
                Box::new(Expr::Var("n".into())),
                Box::new(Expr::Num("0".into())),
            ),
            then_body: vec![Stmt::Return(vec![Expr::Str("\"pos\"".into())])],
            else_body: vec![Stmt::Return(vec![Expr::Str("\"neg\"".into())])],
        };
        let rendered = render_block(&[iff], 0);
        assert!(rendered.contains("if n > 0 then"));
        assert!(rendered.contains("else"));
        assert!(rendered.trim_end().ends_with("end"));
    }

    #[test]
    fn method_call_and_table() {
        let e = Expr::MethodCall(Box::new(Expr::Var("s".into())), "upper".into(), vec![]);
        assert_eq!(render_expr(&e), "s:upper()");

        let t = Expr::Table(vec![
            TableField::Item(Expr::Num("1".into())),
            TableField::Named("k".into(), Expr::Str("\"v\"".into())),
            TableField::Keyed(Expr::Num("2".into()), Expr::Bool(true)),
        ]);
        assert_eq!(render_expr(&t), "{1, k = \"v\", [2] = true}");
    }

    #[test]
    fn prints_literal_left_comparisons_naturally() {
        let e = Expr::Binary(
            "<",
            Box::new(Expr::Num("0".into())),
            Box::new(Expr::Var("n".into())),
        );
        assert_eq!(render_expr(&e), "n > 0");

        let e = Expr::Binary(
            "<",
            Box::new(Expr::Var("n".into())),
            Box::new(Expr::Num("0".into())),
        );
        assert_eq!(render_expr(&e), "n < 0");
    }

    #[test]
    fn trims_generic_for_trailing_nil_iterators() {
        let rendered = render_block(
            &[Stmt::GenericFor {
                vars: vec!["i".into(), "j".into()],
                exprs: vec![Expr::Var("value".into()), Expr::Nil, Expr::Nil],
                body: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Var("print".into())),
                    vec![Expr::Var("j".into())],
                ))],
            }],
            0,
        );

        assert!(rendered.contains("for i, j in value do"), "{rendered}");
        assert!(!rendered.contains("value, nil, nil"), "{rendered}");
    }

    #[test]
    fn prints_blank_lines_around_blocks_and_returns() {
        let rendered = render_block(
            &[
                Stmt::Local {
                    names: vec!["value".into()],
                    values: vec![Expr::Num("0".into())],
                },
                Stmt::If {
                    cond: Expr::Var("ok".into()),
                    then_body: vec![Stmt::Assign {
                        targets: vec![Expr::Var("value".into())],
                        values: vec![Expr::Num("1".into())],
                    }],
                    else_body: Vec::new(),
                },
                Stmt::Assign {
                    targets: vec![Expr::Var("value".into())],
                    values: vec![Expr::Binary(
                        "+",
                        Box::new(Expr::Var("value".into())),
                        Box::new(Expr::Num("1".into())),
                    )],
                },
                Stmt::Return(vec![Expr::Var("value".into())]),
            ],
            0,
        );

        assert!(
            rendered.contains("local value = 0\n\nif ok then"),
            "{rendered}"
        );
        assert!(rendered.contains("end\n\nvalue += 1"), "{rendered}");
        assert!(
            rendered.contains("value += 1\n\nreturn value"),
            "{rendered}"
        );
    }

    #[test]
    fn prints_compound_assignments_for_simple_self_updates() {
        let rendered = render_block(
            &[
                Stmt::Assign {
                    targets: vec![Expr::Var("total".into())],
                    values: vec![Expr::Binary(
                        "+",
                        Box::new(Expr::Var("total".into())),
                        Box::new(Expr::Num("1".into())),
                    )],
                },
                Stmt::Assign {
                    targets: vec![Expr::Var("total".into())],
                    values: vec![Expr::Binary(
                        "-",
                        Box::new(Expr::Var("total".into())),
                        Box::new(Expr::Binary(
                            "+",
                            Box::new(Expr::Var("penalty".into())),
                            Box::new(Expr::Num("1".into())),
                        )),
                    )],
                },
                Stmt::Assign {
                    targets: vec![Expr::Var("total".into())],
                    values: vec![Expr::Binary(
                        "+",
                        Box::new(Expr::Var("other".into())),
                        Box::new(Expr::Num("1".into())),
                    )],
                },
            ],
            0,
        );

        assert!(rendered.contains("total += 1"), "{rendered}");
        assert!(rendered.contains("total -= penalty + 1"), "{rendered}");
        assert!(rendered.contains("total = other + 1"), "{rendered}");
    }

    #[test]
    fn shortens_roundtripping_float_literals() {
        assert_eq!(render_expr(&Expr::Num("0.90000000000000002".into())), "0.9");
        assert_eq!(
            render_expr(&Expr::Num("3.1415926535897931".into())),
            "3.141592653589793"
        );
        assert_eq!(render_expr(&Expr::Num("42".into())), "42");
    }

    #[test]
    fn prints_elseif_chains() {
        let rendered = render_block(
            &[Stmt::If {
                cond: Expr::Var("a".into()),
                then_body: vec![Stmt::Return(vec![Expr::Num("1".into())])],
                else_body: vec![Stmt::If {
                    cond: Expr::Var("b".into()),
                    then_body: vec![Stmt::Return(vec![Expr::Num("2".into())])],
                    else_body: vec![Stmt::Return(vec![Expr::Num("3".into())])],
                }],
            }],
            0,
        );

        assert!(rendered.contains("elseif b then"), "{rendered}");
        assert!(!rendered.contains("else\n\tif b then"), "{rendered}");
        assert_eq!(rendered.matches("end").count(), 1, "{rendered}");
    }

    #[test]
    fn prints_function_sugar() {
        let closure = Expr::Closure {
            text: "function(x)\n\treturn x\nend".into(),
            captures: Vec::new(),
        };
        let rendered = render_block(
            &[
                Stmt::Local {
                    names: vec!["id".into()],
                    values: vec![closure.clone()],
                },
                Stmt::Assign {
                    targets: vec![Expr::Field(
                        Box::new(Expr::Var("module".into())),
                        "id".into(),
                    )],
                    values: vec![closure],
                },
            ],
            0,
        );
        assert!(rendered.contains("local function id(x)"));
        assert!(rendered.contains("function module.id(x)"));
        assert!(
            rendered.contains("end\n\nfunction module.id(x)"),
            "{rendered}"
        );
    }

    #[test]
    fn indented_function_literals_keep_blank_lines_empty() {
        let rendered = render_expr_at(
            &Expr::Closure {
                text: "function()\n\tif ok then\n\t\treturn true\n\tend\n\n\treturn false\nend"
                    .into(),
                captures: Vec::new(),
            },
            2,
        );

        for line in rendered.lines() {
            assert!(
                line.is_empty() || !line.chars().all(|ch| ch == '\t' || ch == ' '),
                "blank line has indentation: {rendered:?}"
            );
        }
    }

    #[test]
    fn prints_precedence_and_associativity() {
        let a = Box::new(Expr::Var("a".into()));
        let b = Box::new(Expr::Var("b".into()));
        let c = Box::new(Expr::Var("c".into()));

        // (a + b) * c
        let e1 = Expr::Binary(
            "*",
            Box::new(Expr::Binary("+", a.clone(), b.clone())),
            c.clone(),
        );
        assert_eq!(render_expr(&e1), "(a + b) * c");

        // a + b * c
        let e2 = Expr::Binary(
            "+",
            a.clone(),
            Box::new(Expr::Binary("*", b.clone(), c.clone())),
        );
        assert_eq!(render_expr(&e2), "a + b * c");

        // a ^ (b ^ c)
        let e3 = Expr::Binary(
            "^",
            a.clone(),
            Box::new(Expr::Binary("^", b.clone(), c.clone())),
        );
        assert_eq!(render_expr(&e3), "a ^ b ^ c");

        // (a ^ b) ^ c
        let e4 = Expr::Binary(
            "^",
            Box::new(Expr::Binary("^", a.clone(), b.clone())),
            c.clone(),
        );
        assert_eq!(render_expr(&e4), "(a ^ b) ^ c");

        // a .. (b .. c)
        let e5 = Expr::Binary(
            "..",
            a.clone(),
            Box::new(Expr::Binary("..", b.clone(), c.clone())),
        );
        assert_eq!(render_expr(&e5), "a .. b .. c");

        // (a .. b) .. c
        let e6 = Expr::Binary(
            "..",
            Box::new(Expr::Binary("..", a.clone(), b.clone())),
            c.clone(),
        );
        assert_eq!(render_expr(&e6), "(a .. b) .. c");

        // not (a and b)
        let e7 = Expr::Unary("not ", Box::new(Expr::Binary("and", a.clone(), b.clone())));
        assert_eq!(render_expr(&e7), "not (a and b)");

        // a or (b and c)
        let e8 = Expr::Binary(
            "or",
            a.clone(),
            Box::new(Expr::Binary("and", b.clone(), c.clone())),
        );
        assert_eq!(render_expr(&e8), "a or (b and c)");

        // (a or b) and c
        let e9 = Expr::Binary(
            "and",
            Box::new(Expr::Binary("or", a.clone(), b.clone())),
            c.clone(),
        );
        assert_eq!(render_expr(&e9), "(a or b) and c");

        // not not a
        let e10 = Expr::Unary("not ", Box::new(Expr::Unary("not ", a.clone())));
        assert_eq!(render_expr(&e10), "not not a");

        // -(-a)
        let e11 = Expr::Unary("-", Box::new(Expr::Unary("-", a.clone())));
        assert_eq!(render_expr(&e11), "-(-a)");
    }

    #[test]
    fn prefix_parentheses_on_literals() {
        let str_lit = Box::new(Expr::Str("\"hello\"".into()));
        let call1 = Expr::MethodCall(str_lit, "upper".into(), vec![]);
        assert_eq!(render_expr(&call1), "(\"hello\"):upper()");

        let table_lit = Box::new(Expr::Table(vec![]));
        let call2 = Expr::MethodCall(table_lit, "insert".into(), vec![]);
        assert_eq!(render_expr(&call2), "({}):insert()");

        let func_lit = Box::new(Expr::Closure {
            text: "function() end".into(),
            captures: vec![],
        });
        let call3 = Expr::Call(func_lit, vec![]);
        assert_eq!(render_expr(&call3), "(function() end)()");
    }

    #[test]
    fn table_formatting_styles() {
        let t1 = Expr::Table(vec![
            TableField::Item(Expr::Num("1".into())),
            TableField::Item(Expr::Num("2".into())),
            TableField::Item(Expr::Num("3".into())),
        ]);
        assert_eq!(render_expr(&t1), "{1, 2, 3}");

        let t2 = Expr::Table(vec![
            TableField::Named("x".into(), Expr::Num("10".into())),
            TableField::Named("y".into(), Expr::Num("20".into())),
        ]);
        assert_eq!(render_expr(&t2), "{x = 10, y = 20}");

        let t3 = Expr::Table(vec![
            TableField::Item(Expr::Num("1".into())),
            TableField::Named("key".into(), Expr::Str("\"val\"".into())),
            TableField::Keyed(Expr::Str("\"other\"".into()), Expr::Bool(true)),
        ]);
        assert_eq!(render_expr(&t3), "{1, key = \"val\", [\"other\"] = true}");

        let t4 = Expr::Table(vec![
            TableField::Item(Expr::Table(vec![TableField::Item(Expr::Num("1".into()))])),
            TableField::Item(Expr::Table(vec![TableField::Item(Expr::Num("2".into()))])),
        ]);
        assert_eq!(render_expr(&t4), "{{1}, {2}}");

        let t5 = Expr::Table(vec![TableField::Item(Expr::Table(vec![
            TableField::Item(Expr::Num("1".into())),
            TableField::Item(Expr::Num("2".into())),
            TableField::Item(Expr::Num("3".into())),
            TableField::Item(Expr::Num("4".into())),
        ]))]);
        let rendered_t5 = render_expr(&t5);
        assert!(
            rendered_t5.contains("{\n\t{\n\t\t1,\n\t\t2,\n\t\t3,\n\t\t4,\n\t},\n}"),
            "{rendered_t5}"
        );

        let t6 = Expr::Table(vec![TableField::Named(
            "foo".into(),
            Expr::Closure {
                text: "function(x)\n\treturn x\nend".into(),
                captures: vec![],
            },
        )]);
        let rendered_t6 = render_expr(&t6);
        assert!(
            rendered_t6.contains("foo = function(x)\n\t\treturn x\n\tend"),
            "{rendered_t6}"
        );

        let t7 = Expr::Table(vec![
            TableField::Item(Expr::Num("1".into())),
            TableField::Item(Expr::Num("2".into())),
            TableField::Item(Expr::Num("3".into())),
            TableField::Item(Expr::Num("4".into())),
        ]);
        assert_eq!(render_expr(&t7), "{\n\t1,\n\t2,\n\t3,\n\t4,\n}");
    }

    #[test]
    fn method_colon_sugar_rendering() {
        let closure = Expr::Closure {
            text: "function(self, x)\n\treturn x\nend".into(),
            captures: vec![],
        };
        let rendered = render_block(
            &[Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("module".into())),
                    "foo".into(),
                )],
                values: vec![closure],
            }],
            0,
        );
        assert!(
            rendered.contains("function module:foo(x)\n\treturn x\nend"),
            "{rendered}"
        );
    }

    #[test]
    fn float_literals_shorten_cleanup() {
        assert_eq!(render_expr(&Expr::Num("0.80000000000000004".into())), "0.8");
    }
}

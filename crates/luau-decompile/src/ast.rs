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
    for s in stmts {
        render_stmt(&mut out, s, indent);
    }
    out
}

fn pad(out: &mut String, indent: usize) {
    for _ in 0..indent {
        out.push('\t');
    }
}

fn render_stmt(out: &mut String, s: &Stmt, indent: usize) {
    match s {
        Stmt::Local { names, values } => {
            pad(out, indent);
            let _ = write!(out, "local {}", names.join(", "));
            if !values.is_empty() {
                let _ = write!(out, " = {}", join_exprs_at(values, indent));
            }
            out.push('\n');
        }
        Stmt::Assign { targets, values } => {
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
            pad(out, indent);
            let _ = writeln!(out, "if {} then", render_expr_at(cond, indent));
            out.push_str(&render_block(then_body, indent + 1));
            if !else_body.is_empty() {
                // Collapse `else { if ... }` into `elseif` for readability.
                if else_body.len() == 1 {
                    if let Stmt::If { .. } = &else_body[0] {
                        pad(out, indent);
                        out.push_str("else\n");
                        out.push_str(&render_block(else_body, indent + 1));
                        pad(out, indent);
                        out.push_str("end\n");
                        return;
                    }
                }
                pad(out, indent);
                out.push_str("else\n");
                out.push_str(&render_block(else_body, indent + 1));
            }
            pad(out, indent);
            out.push_str("end\n");
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
                join_exprs_at(exprs, indent)
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

pub fn render_expr(e: &Expr) -> String {
    render_expr_at(e, 0)
}

fn render_expr_at(e: &Expr, indent: usize) -> String {
    match e {
        Expr::Nil => "nil".to_string(),
        Expr::Bool(b) => b.to_string(),
        Expr::Num(s) | Expr::Str(s) | Expr::Vector(s) | Expr::Var(s) | Expr::Raw(s) => s.clone(),
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
                format!("not {}", paren_at(a, indent))
            } else {
                format!("{op}{}", paren_at(a, indent))
            }
        }
        Expr::Binary(op, a, b) => {
            // `and`/`or` are associative and left-grouped by the compiler; a same-operator
            // left operand doesn't need parens (`a and b and c`, not `(a and b) and c`).
            let lhs = match (a.as_ref(), *op) {
                (Expr::Binary(inner, ..), "and") if *inner == "and" => render_expr_at(a, indent),
                (Expr::Binary(inner, ..), "or") if *inner == "or" => render_expr_at(a, indent),
                _ => paren_at(a, indent),
            };
            format!("{lhs} {op} {}", paren_at(b, indent))
        }
        Expr::Table(fields) => render_table(fields, indent),
    }
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
        Expr::Closure { .. } | Expr::Table(_) => true,
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
            pad(&mut out, indent);
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
        assert_eq!(rendered, "for i = 1, n do\n\tacc = acc + i\nend\n");

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
}

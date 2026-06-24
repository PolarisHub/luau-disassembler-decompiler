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
    /// A function literal (rendered separately and spliced in).
    Closure(String),
    /// Fallback raw text (e.g. `R3 --[[?]]`) for things we couldn't reconstruct.
    Raw(String),
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
                let _ = write!(out, " = {}", join_exprs(values));
            }
            out.push('\n');
        }
        Stmt::Assign { targets, values } => {
            pad(out, indent);
            let _ = writeln!(out, "{} = {}", join_exprs(targets), join_exprs(values));
        }
        Stmt::Call(e) => {
            pad(out, indent);
            let _ = writeln!(out, "{}", render_expr(e));
        }
        Stmt::Return(exprs) => {
            pad(out, indent);
            if exprs.is_empty() {
                out.push_str("return\n");
            } else {
                let _ = writeln!(out, "return {}", join_exprs(exprs));
            }
        }
        Stmt::Break => {
            pad(out, indent);
            out.push_str("break\n");
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            pad(out, indent);
            let _ = writeln!(out, "if {} then", render_expr(cond));
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
            let _ = writeln!(out, "while {} do", render_expr(cond));
            out.push_str(&render_block(body, indent + 1));
            pad(out, indent);
            out.push_str("end\n");
        }
        Stmt::Repeat { body, cond } => {
            pad(out, indent);
            out.push_str("repeat\n");
            out.push_str(&render_block(body, indent + 1));
            pad(out, indent);
            let _ = writeln!(out, "until {}", render_expr(cond));
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
                        render_expr(start),
                        render_expr(limit),
                        render_expr(s)
                    );
                }
                None => {
                    let _ = writeln!(
                        out,
                        "for {var} = {}, {} do",
                        render_expr(start),
                        render_expr(limit)
                    );
                }
            }
            out.push_str(&render_block(body, indent + 1));
            pad(out, indent);
            out.push_str("end\n");
        }
        Stmt::GenericFor { vars, exprs, body } => {
            pad(out, indent);
            let _ = writeln!(out, "for {} in {} do", vars.join(", "), join_exprs(exprs));
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

pub fn render_expr(e: &Expr) -> String {
    match e {
        Expr::Nil => "nil".to_string(),
        Expr::Bool(b) => b.to_string(),
        Expr::Num(s) | Expr::Str(s) | Expr::Vector(s) | Expr::Var(s) | Expr::Raw(s) => s.clone(),
        Expr::Closure(s) => s.clone(),
        Expr::Vararg => "...".to_string(),
        Expr::Index(t, k) => format!("{}[{}]", render_expr(t), render_expr(k)),
        Expr::Field(t, f) => format!("{}.{}", render_expr(t), f),
        Expr::Call(f, args) => format!("{}({})", render_expr(f), join_exprs(args)),
        Expr::MethodCall(o, m, args) => {
            format!("{}:{}({})", render_expr(o), m, join_exprs(args))
        }
        Expr::Unary(op, a) => {
            // `not` needs a space; symbolic ops don't.
            if *op == "not " {
                format!("not {}", paren(a))
            } else {
                format!("{op}{}", paren(a))
            }
        }
        Expr::Binary(op, a, b) => format!("{} {op} {}", paren(a), paren(b)),
        Expr::Table(fields) => {
            let parts: Vec<String> = fields
                .iter()
                .map(|fld| match fld {
                    TableField::Item(e) => render_expr(e),
                    TableField::Named(n, e) => format!("{n} = {}", render_expr(e)),
                    TableField::Keyed(k, v) => {
                        format!("[{}] = {}", render_expr(k), render_expr(v))
                    }
                })
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
    }
}

/// Parenthesize a sub-expression when needed to keep precedence unambiguous. We are
/// conservative: wrap any binary/unary operand that is itself a binary/unary expression.
fn paren(e: &Expr) -> String {
    match e {
        Expr::Binary(..) | Expr::Unary(..) => format!("({})", render_expr(e)),
        _ => render_expr(e),
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

//! Render constant-table entries to text, matching `BytecodeBuilder::dumpConstant` with
//! `detailed = false` (the form that appears inside `[...]` in the instruction listing).

use luau_bytecode::{Constant, Module, Proto};

use crate::format::format_g;

/// Render the constant at index `k` of `proto`. Out-of-range indices render as a marker
/// rather than panicking (the reader validates indices, but the disassembler stays total).
pub fn render_constant_at(module: &Module, proto: &Proto, k: usize) -> String {
    match proto.constants.get(k) {
        Some(c) => render_constant(module, proto, c),
        None => format!("<bad K{k}>"),
    }
}

pub fn render_constant(module: &Module, proto: &Proto, c: &Constant) -> String {
    match c {
        Constant::Nil => "nil".to_string(),
        Constant::Boolean(b) => if *b { "true" } else { "false" }.to_string(),
        Constant::Number(n) => format_g(*n, 17),
        Constant::Integer(i) => i.to_string(),
        Constant::Vector { x, y, z, w } => {
            // 3-vectors are most common; Luau truncates to 3 components when w == 0.
            if *w == 0.0 {
                format!(
                    "{}, {}, {}",
                    format_g(*x as f64, 9),
                    format_g(*y as f64, 9),
                    format_g(*z as f64, 9)
                )
            } else {
                format!(
                    "{}, {}, {}, {}",
                    format_g(*x as f64, 9),
                    format_g(*y as f64, 9),
                    format_g(*z as f64, 9),
                    format_g(*w as f64, 9)
                )
            }
        }
        Constant::String(sref) => match sref.index().and_then(|i| module.string_bytes(i)) {
            Some(bytes) => render_string(bytes),
            None => "''".to_string(),
        },
        Constant::Import { path, .. } => render_import(module, proto, path),
        // detailed = false renders any table template as a placeholder.
        Constant::Table { .. } | Constant::TableWithConstants { .. } => "{...}".to_string(),
        Constant::Closure { proto: pid } => match module
            .protos
            .get(*pid as usize)
            .and_then(|p| module.resolve(p.debug_name))
        {
            Some(name) if !name.is_empty() => format!("'{name}'"),
            _ => String::new(),
        },
        Constant::ClassShape {
            name,
            num_properties,
            num_methods,
            ..
        } => {
            let class_name = proto
                .constants
                .get(*name as usize)
                .map(|c| render_constant(module, proto, c))
                .unwrap_or_default();
            // class_name renders as a quoted string; strip the quotes for `class NAME`.
            let class_name = class_name.trim_matches('\'');
            format!("class {class_name} (props: {num_properties}, methods: {num_methods})")
        }
    }
}

/// Resolve an import path (constant-table indices, each a string constant) to a dotted path
/// with no quotes, e.g. `game.Players`.
fn render_import(module: &Module, proto: &Proto, path: &[u32]) -> String {
    let mut parts = Vec::with_capacity(path.len());
    for &k in path {
        let text = match proto.constants.get(k as usize) {
            Some(Constant::String(sref)) => sref
                .index()
                .and_then(|i| module.string_bytes(i))
                .map(|b| String::from_utf8_lossy(b).into_owned())
                .unwrap_or_default(),
            _ => "?".to_string(),
        };
        parts.push(text);
    }
    parts.join(".")
}

/// Render a string constant like Luau: printable strings are quoted as-is (truncated to 32
/// chars with a trailing `...`); strings with control bytes escape them as `\xXX`.
fn render_string(bytes: &[u8]) -> String {
    let printable = bytes.iter().all(|&b| b >= b' ');
    let mut out = String::new();
    out.push('\'');
    if printable {
        let shown = &bytes[..bytes.len().min(32)];
        out.push_str(&String::from_utf8_lossy(shown));
        out.push('\'');
        if bytes.len() >= 32 {
            out.push_str("...");
        }
    } else {
        for &b in bytes.iter().take(32) {
            if b < b' ' {
                out.push_str(&format!("\\x{b:02X}"));
            } else {
                out.push(b as char);
            }
        }
        if bytes.len() >= 32 {
            out.push_str("'...");
        } else {
            out.push('\'');
        }
    }
    out
}

//! Readability heuristics: derive meaningful names for synthesized locals from the
//! expression they are assigned, and rewrite the AST consistently.
//!
//! Renaming a local is always semantically safe as long as it is applied consistently and
//! de-duplicated against every other in-scope name and against Luau keywords. So these
//! heuristics can be aggressive: the worst case is a slightly misleading name, never a
//! wrong program. Heuristics that would change behavior live elsewhere, not here.
//!
//! The catalog below is a first batch (require/module, Roblox services & instances, method
//! results, length, field access). It is structured as a single first-match-wins
//! `derive_name` so more rules slot in cleanly.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{Expr, Stmt, TableField};

/// Names matching this shape are decompiler-synthesized locals and may be renamed. Debug
/// names and parameters (`pN`) are left untouched.
fn is_synthetic(name: &str) -> bool {
    name.len() >= 2 && name.starts_with('v') && name[1..].chars().all(|c| c.is_ascii_digit())
}

/// Compute a rename map for synthesized locals, keyed by their current name.
pub fn smart_rename(stmts: &[Stmt], hoist_names: &[String]) -> BTreeMap<String, String> {
    let candidates: BTreeSet<String> = hoist_names
        .iter()
        .filter(|n| is_synthetic(n))
        .cloned()
        .collect();
    if candidates.is_empty() {
        return BTreeMap::new();
    }

    // All assignments to each candidate, in order.
    let mut defs: BTreeMap<String, Vec<Expr>> = BTreeMap::new();
    collect_all_defs(stmts, &candidates, &mut defs);

    // Names we must not collide with: everything already in use that we are not renaming,
    // plus the synthesized names themselves (until each is mapped), plus Luau keywords.
    let mut reserved: BTreeSet<String> = BTreeSet::new();
    collect_used_names(stmts, &mut reserved);
    reserved.extend(LUAU_KEYWORDS.iter().map(|s| s.to_string()));

    let mut map = BTreeMap::new();
    // Deterministic order by the numeric suffix.
    let mut ordered: Vec<&String> = candidates.iter().collect();
    ordered.sort_by_key(|n| n[1..].parse::<u32>().unwrap_or(0));

    for orig in ordered {
        let Some(list) = defs.get(orig) else {
            continue;
        };
        // Single-definition guard (a key correctness/clarity rule): only derive a name for a
        // register that holds one logical value. A refinement chain — where every later
        // assignment reads the register it refines, e.g. `x = a.b; x = x.c` — counts as one
        // value, so we name it from the final form. Truly unrelated reuse stays `vN`.
        let chosen: &Expr = if list.len() == 1 {
            &list[0]
        } else if list[1..].iter().all(|e| expr_references(e, orig)) {
            list.last().unwrap()
        } else {
            continue;
        };
        let Some(base) = derive_name(chosen) else {
            continue;
        };
        // Avoid colliding with reserved names and other still-unmapped synthesized names.
        let mut taken = reserved.clone();
        taken.extend(candidates.iter().filter(|c| *c != orig).cloned());
        taken.extend(map.values().cloned());
        let unique = unique_name(&base, &taken);
        reserved.insert(unique.clone());
        map.insert(orig.clone(), unique);
    }
    map
}

/// Fold chained refinements: `x = a.b; x = x.c` -> `x = a.b.c`, the compiler's reuse of one
/// register for a field/method chain. Only fires in the safe shape where `x` is the head of
/// the second expression and everything else in it is pure, so the single evaluation of `a.b`
/// and the order of any side effects are preserved (see the synthesized pitfalls list).
pub fn fold_refinements(stmts: &mut Vec<Stmt>) {
    // Recurse into nested blocks first.
    for s in stmts.iter_mut() {
        match s {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                fold_refinements(then_body);
                fold_refinements(else_body);
            }
            Stmt::While { body, .. }
            | Stmt::Repeat { body, .. }
            | Stmt::NumericFor { body, .. }
            | Stmt::GenericFor { body, .. } => fold_refinements(body),
            _ => {}
        }
    }

    let mut i = 0;
    while i + 1 < stmts.len() {
        if let Some(folded) = try_fold_pair(&stmts[i], &stmts[i + 1]) {
            stmts[i] = folded;
            stmts.remove(i + 1);
            // Re-check at the same position so longer chains collapse fully.
            continue;
        }
        i += 1;
    }
}

fn try_fold_pair(s1: &Stmt, s2: &Stmt) -> Option<Stmt> {
    let (
        Stmt::Assign {
            targets: t1,
            values: v1,
        },
        Stmt::Assign {
            targets: t2,
            values: v2,
        },
    ) = (s1, s2)
    else {
        return None;
    };
    if t1.len() != 1 || t2.len() != 1 || v1.len() != 1 || v2.len() != 1 {
        return None;
    }
    let (Expr::Var(x1), Expr::Var(x2)) = (&t1[0], &t2[0]) else {
        return None;
    };
    if x1 != x2 || expr_references(&v1[0], x1) {
        return None;
    }
    let folded = fold_head(&v2[0], x1, &v1[0])?;
    Some(Stmt::Assign {
        targets: vec![Expr::Var(x1.clone())],
        values: vec![folded],
    })
}

/// If `e2` consumes `x` exactly once at its evaluation head (with everything else pure),
/// return `e2` with that `x` replaced by `e1`.
fn fold_head(e2: &Expr, x: &str, e1: &Expr) -> Option<Expr> {
    match e2 {
        Expr::Field(base, f) if is_var(base, x) => {
            Some(Expr::Field(Box::new(e1.clone()), f.clone()))
        }
        Expr::Index(base, k) if is_var(base, x) && is_pure(k) => {
            Some(Expr::Index(Box::new(e1.clone()), k.clone()))
        }
        Expr::MethodCall(o, m, args) if is_var(o, x) && args.iter().all(is_pure) => Some(
            Expr::MethodCall(Box::new(e1.clone()), m.clone(), args.clone()),
        ),
        Expr::Call(c, args) if is_var(c, x) && args.iter().all(is_pure) => {
            Some(Expr::Call(Box::new(e1.clone()), args.clone()))
        }
        Expr::Unary(op, a) if is_var(a, x) => Some(Expr::Unary(op, Box::new(e1.clone()))),
        _ => None,
    }
}

/// Side-effect-free for the purpose of reordering: no calls (which could observe order).
pub(crate) fn is_pure(e: &Expr) -> bool {
    match e {
        Expr::Nil
        | Expr::Bool(_)
        | Expr::Num(_)
        | Expr::Str(_)
        | Expr::Vector(_)
        | Expr::Var(_)
        | Expr::Vararg
        | Expr::Closure(_) => true,
        Expr::Field(b, _) => is_pure(b),
        Expr::Index(b, k) => is_pure(b) && is_pure(k),
        Expr::Unary(_, a) => is_pure(a),
        Expr::Binary(_, a, b) => is_pure(a) && is_pure(b),
        Expr::Table(fields) => fields.iter().all(|f| match f {
            TableField::Item(e) | TableField::Named(_, e) => is_pure(e),
            TableField::Keyed(k, v) => is_pure(k) && is_pure(v),
        }),
        Expr::Call(..) | Expr::MethodCall(..) | Expr::Raw(_) => false,
    }
}

/// Apply a rename map to a statement tree.
pub fn apply_rename(stmts: &mut [Stmt], map: &BTreeMap<String, String>) {
    if map.is_empty() {
        return;
    }
    for s in stmts {
        rename_stmt(s, map);
    }
}

fn rename_stmt(s: &mut Stmt, map: &BTreeMap<String, String>) {
    match s {
        Stmt::Local { names, values } => {
            for n in names.iter_mut() {
                if let Some(new) = map.get(n) {
                    *n = new.clone();
                }
            }
            values.iter_mut().for_each(|e| rename_expr(e, map));
        }
        Stmt::Assign { targets, values } => {
            targets.iter_mut().for_each(|e| rename_expr(e, map));
            values.iter_mut().for_each(|e| rename_expr(e, map));
        }
        Stmt::Call(e) => rename_expr(e, map),
        Stmt::Return(es) => es.iter_mut().for_each(|e| rename_expr(e, map)),
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rename_expr(cond, map);
            apply_rename(then_body, map);
            apply_rename(else_body, map);
        }
        Stmt::While { cond, body } => {
            rename_expr(cond, map);
            apply_rename(body, map);
        }
        Stmt::Repeat { body, cond } => {
            apply_rename(body, map);
            rename_expr(cond, map);
        }
        Stmt::NumericFor {
            start,
            limit,
            step,
            body,
            ..
        } => {
            rename_expr(start, map);
            rename_expr(limit, map);
            if let Some(s) = step {
                rename_expr(s, map);
            }
            apply_rename(body, map);
        }
        Stmt::GenericFor { exprs, body, .. } => {
            exprs.iter_mut().for_each(|e| rename_expr(e, map));
            apply_rename(body, map);
        }
        Stmt::Break | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => {}
    }
}

fn rename_expr(e: &mut Expr, map: &BTreeMap<String, String>) {
    match e {
        Expr::Var(name) => {
            if let Some(new) = map.get(name) {
                *name = new.clone();
            }
        }
        Expr::Index(t, k) => {
            rename_expr(t, map);
            rename_expr(k, map);
        }
        Expr::Field(t, _) => rename_expr(t, map),
        Expr::Call(f, args) => {
            rename_expr(f, map);
            args.iter_mut().for_each(|a| rename_expr(a, map));
        }
        Expr::MethodCall(o, _, args) => {
            rename_expr(o, map);
            args.iter_mut().for_each(|a| rename_expr(a, map));
        }
        Expr::Unary(_, a) => rename_expr(a, map),
        Expr::Binary(_, a, b) => {
            rename_expr(a, map);
            rename_expr(b, map);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) => rename_expr(e, map),
                    TableField::Named(_, e) => rename_expr(e, map),
                    TableField::Keyed(k, v) => {
                        rename_expr(k, map);
                        rename_expr(v, map);
                    }
                }
            }
        }
        Expr::Nil
        | Expr::Bool(_)
        | Expr::Num(_)
        | Expr::Str(_)
        | Expr::Vector(_)
        | Expr::Vararg
        | Expr::Closure(_)
        | Expr::Raw(_) => {}
    }
}

fn collect_all_defs(
    stmts: &[Stmt],
    candidates: &BTreeSet<String>,
    out: &mut BTreeMap<String, Vec<Expr>>,
) {
    for s in stmts {
        if let Stmt::Assign { targets, values } = s {
            if let (Some(Expr::Var(name)), Some(value)) = (targets.first(), values.first()) {
                if targets.len() == 1 && candidates.contains(name) {
                    out.entry(name.clone()).or_default().push(value.clone());
                }
            }
        }
        // Definitions only appear at top level in the current emitter, but recurse so this
        // keeps working once control flow is structured.
        for_each_child_block(s, |body| collect_all_defs(body, candidates, out));
    }
}

/// Whether `e` reads the variable `name` anywhere.
fn expr_references(e: &Expr, name: &str) -> bool {
    let mut found = false;
    let mut set = BTreeSet::new();
    collect_used_in_expr(e, &mut set);
    if set.contains(name) {
        found = true;
    }
    found
}

fn collect_used_names(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for s in stmts {
        match s {
            Stmt::Local { names, values } => {
                out.extend(names.iter().cloned());
                values.iter().for_each(|e| collect_used_in_expr(e, out));
            }
            Stmt::Assign { targets, values } => {
                targets.iter().for_each(|e| collect_used_in_expr(e, out));
                values.iter().for_each(|e| collect_used_in_expr(e, out));
            }
            Stmt::Call(e) => collect_used_in_expr(e, out),
            Stmt::Return(es) => es.iter().for_each(|e| collect_used_in_expr(e, out)),
            Stmt::If { cond, .. } => collect_used_in_expr(cond, out),
            Stmt::While { cond, .. } => collect_used_in_expr(cond, out),
            Stmt::Repeat { cond, .. } => collect_used_in_expr(cond, out),
            Stmt::NumericFor { var, .. } => {
                out.insert(var.clone());
            }
            Stmt::GenericFor { vars, .. } => out.extend(vars.iter().cloned()),
            _ => {}
        }
        for_each_child_block(s, |body| collect_used_names(body, out));
    }
}

fn collect_used_in_expr(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        // Only count a bare single-segment identifier; dotted paths are not local names.
        Expr::Var(name) if !name.contains('.') => {
            out.insert(name.clone());
        }
        Expr::Var(_) => {}
        Expr::Index(t, k) => {
            collect_used_in_expr(t, out);
            collect_used_in_expr(k, out);
        }
        Expr::Field(t, _) => collect_used_in_expr(t, out),
        Expr::Call(f, args) => {
            collect_used_in_expr(f, out);
            args.iter().for_each(|a| collect_used_in_expr(a, out));
        }
        Expr::MethodCall(o, _, args) => {
            collect_used_in_expr(o, out);
            args.iter().for_each(|a| collect_used_in_expr(a, out));
        }
        Expr::Unary(_, a) => collect_used_in_expr(a, out),
        Expr::Binary(_, a, b) => {
            collect_used_in_expr(a, out);
            collect_used_in_expr(b, out);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => collect_used_in_expr(e, out),
                    TableField::Keyed(k, v) => {
                        collect_used_in_expr(k, out);
                        collect_used_in_expr(v, out);
                    }
                }
            }
        }
        _ => {}
    }
}

fn for_each_child_block(s: &Stmt, mut f: impl FnMut(&[Stmt])) {
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

// --- name derivation -------------------------------------------------------------------

/// Derive a readable variable name from the expression a local is assigned, or `None` to
/// keep the synthesized name. First match wins.
pub fn derive_name(e: &Expr) -> Option<String> {
    match e {
        Expr::Call(callee, args) => derive_from_call(callee, args),
        Expr::MethodCall(recv, method, args) => derive_from_method(recv, method, args),
        Expr::Field(base, field) => {
            // require(<module>).member -> module_member (member kept verbatim).
            if let Expr::Call(callee, cargs) = base.as_ref() {
                if is_var(callee, "require") {
                    if let Some(m) = cargs.first().and_then(name_from_value) {
                        return sanitize(&format!("{m}_{field}"));
                    }
                }
            }
            // Players.LocalPlayer -> localPlayer (a conventional fixed name).
            if field == "LocalPlayer" {
                return Some("localPlayer".to_string());
            }
            // Otherwise the trailing field, read as an instance: player.Character -> character.
            sanitize(&lower_first(field))
        }
        Expr::Index(_, key) => {
            if let Expr::Str(lit) = key.as_ref() {
                return sanitize(&strip_quotes(lit));
            }
            None
        }
        // #players -> playerCount ; #t -> count
        Expr::Unary(op, inner) if *op == "#" => Some(length_name(inner)),
        _ => None,
    }
}

fn derive_from_call(callee: &Expr, args: &[Expr]) -> Option<String> {
    // require(<module>) -> module name
    if is_var(callee, "require") {
        return args.first().and_then(name_from_value);
    }

    // tostring/tonumber/typeof: <base>Str / <base>Num / <base>Type
    if let Expr::Var(f) = callee {
        let fname = last_segment(f).unwrap_or_else(|| f.clone());
        match fname.as_str() {
            "tostring" => return Some(suffix_base(args.first(), "Str", "str")),
            "tonumber" => return Some(suffix_base(args.first(), "Num", "num")),
            "typeof" | "type" => return Some(suffix_base(args.first(), "Type", "typeName")),
            _ => {}
        }
    }

    // owner.member style calls (field access or dotted import).
    if let Some((owner, member)) = call_owner_member(callee) {
        // Instance.new("Class") -> lowercased class name.
        if owner == "Instance" && member == "new" {
            if let Some(Expr::Str(lit)) = args.first() {
                return sanitize(&lower_first(&strip_quotes(lit)));
            }
        }
        if member == "GetService" {
            return args.first().and_then(name_from_value);
        }
        // Roblox datatype constructors: Vector3.new -> vector, Color3.fromRGB -> color, ...
        if let Some(n) = datatype_value_name(&owner) {
            return Some(n);
        }
        // table./math. library results worth naming.
        match (owner.as_str(), member.as_str()) {
            ("table", "remove") => return Some("removed".to_string()),
            ("table", "find") => return Some("index".to_string()),
            ("table", "pack") => return Some("args".to_string()),
            ("math", "random") => return Some("random".to_string()),
            _ => {}
        }
        if member == "new" {
            return sanitize(&lower_first(&owner));
        }
    }

    // generic foo(...) -> name from the function identifier.
    if let Expr::Var(f) = callee {
        if !f.contains('.') {
            return name_from_call_ident(f);
        }
        return last_segment(f).and_then(|s| name_from_call_ident(&s));
    }
    None
}

fn derive_from_method(recv: &Expr, method: &str, args: &[Expr]) -> Option<String> {
    match method {
        "GetService" => args.first().and_then(name_from_value),
        // Child lookups by literal name: keep the child name verbatim (PascalCase reads well).
        "FindFirstChild" | "WaitForChild" | "FindFirstAncestor" => {
            args.first().and_then(name_from_value)
        }
        // Child lookups by class: name after the class, as an instance.
        "FindFirstChildOfClass"
        | "FindFirstChildWhichIsA"
        | "FindFirstAncestorOfClass"
        | "FindFirstAncestorWhichIsA" => match args.first() {
            Some(Expr::Str(lit)) => sanitize(&lower_first(&strip_quotes(lit))),
            _ => None,
        },
        // Signal connections -> <event>Connection.
        "Connect" | "ConnectParallel" | "Once" => {
            let event = trailing_noun(recv).map(|n| lower_first(&n));
            Some(match event {
                Some(e) => format!("{e}Connection"),
                None => "connection".to_string(),
            })
        }
        // remote:InvokeServer()/InvokeClient() returns a value.
        "InvokeServer" | "InvokeClient" => Some("result".to_string()),
        // GetChildren -> children, GetPlayers -> players, IsA -> isClass, etc.
        _ => method_to_noun(method),
    }
}

/// The trailing noun of a receiver expression (its last field/path segment).
fn trailing_noun(e: &Expr) -> Option<String> {
    match e {
        Expr::Field(_, f) => Some(f.clone()),
        Expr::Var(path) => last_segment(path),
        _ => None,
    }
}

/// #players -> playerCount, #t -> count.
fn length_name(inner: &Expr) -> String {
    if let Some(base) = name_from_value(inner) {
        if base.len() > 1 && base.ends_with('s') && !base.ends_with("ss") {
            return format!("{}Count", singular(&base));
        }
    }
    "count".to_string()
}

fn singular(s: &str) -> String {
    if let Some(stem) = s.strip_suffix("ies") {
        format!("{stem}y")
    } else if s.len() > 1 && s.ends_with('s') && !s.ends_with("ss") {
        s[..s.len() - 1].to_string()
    } else {
        s.to_string()
    }
}

fn suffix_base(arg: Option<&Expr>, suffix: &str, default: &str) -> String {
    arg.and_then(name_from_value)
        .map(|b| format!("{}{suffix}", b))
        .unwrap_or_else(|| default.to_string())
}

/// Conventional variable name for a Roblox datatype constructor's owner type.
fn datatype_value_name(owner: &str) -> Option<String> {
    let name = match owner {
        "Vector3" | "Vector2" => "vector",
        "CFrame" => "cframe",
        "Color3" => "color",
        "UDim2" => "udim2",
        "UDim" => "udim",
        "TweenInfo" => "tweenInfo",
        "BrickColor" => "brickColor",
        "Ray" => "ray",
        "Region3" => "region3",
        "Rect" => "rect",
        "NumberSequence" | "ColorSequence" => "sequence",
        _ => return None,
    };
    Some(name.to_string())
}

/// A noun extracted from a value used as a path/key (require arg, service name, child name).
fn name_from_value(e: &Expr) -> Option<String> {
    match e {
        Expr::Str(lit) => last_segment(&strip_quotes(lit)).and_then(|s| sanitize(&s)),
        Expr::Var(path) => last_segment(path).and_then(|s| sanitize(&s)),
        Expr::Field(_, f) => sanitize(f),
        Expr::Index(_, k) => {
            if let Expr::Str(lit) = k.as_ref() {
                sanitize(&strip_quotes(lit))
            } else {
                None
            }
        }
        Expr::MethodCall(_, m, args) if matches!(m.as_str(), "WaitForChild" | "FindFirstChild") => {
            args.first().and_then(name_from_value)
        }
        _ => None,
    }
}

/// `GetChildren` -> `children`, `IsGrounded` -> `isGrounded`, `Fire` -> `fire`.
fn method_to_noun(method: &str) -> Option<String> {
    let stripped = method
        .strip_prefix("Get")
        .or_else(|| method.strip_prefix("get"))
        .filter(|rest| !rest.is_empty())
        .unwrap_or(method);
    sanitize(&lower_first(stripped))
}

/// Name a variable from the call's function identifier, stripping common verb prefixes so
/// `GetData()` -> `data`, `computeThing()` -> `thing`.
fn name_from_call_ident(f: &str) -> Option<String> {
    for prefix in [
        "Get", "get", "Create", "create", "Make", "New", "Build", "Compute", "Load", "Fetch",
    ] {
        if let Some(rest) = f.strip_prefix(prefix) {
            if !rest.is_empty() && rest.chars().next().unwrap().is_ascii_uppercase() {
                return sanitize(&lower_first(rest));
            }
        }
    }
    sanitize(&lower_first(f))
}

fn is_var(e: &Expr, name: &str) -> bool {
    matches!(e, Expr::Var(n) if n == name)
}

/// For a call target, return `(owner, member)` whether it is a field access
/// (`Field(Var("Instance"), "new")`) or a dotted import (`Var("Instance.new")`).
fn call_owner_member(callee: &Expr) -> Option<(String, String)> {
    match callee {
        Expr::Field(base, m) => {
            if let Expr::Var(o) = base.as_ref() {
                last_segment(o).map(|o| (o, m.clone()))
            } else {
                None
            }
        }
        Expr::Var(path) if path.contains('.') => {
            let parts: Vec<&str> = path.split('.').collect();
            let n = parts.len();
            Some((parts[n - 2].to_string(), parts[n - 1].to_string()))
        }
        _ => None,
    }
}

/// Last `.`/`:`/`/`-separated segment of a path-like string.
fn last_segment(s: &str) -> Option<String> {
    let seg = s.rsplit(['.', ':', '/']).next().unwrap_or(s).trim();
    if seg.is_empty() {
        None
    } else {
        Some(seg.to_string())
    }
}

fn strip_quotes(s: &str) -> String {
    let s = s.trim();
    let bytes = s.as_bytes();
    if bytes.len() >= 2
        && (bytes[0] == b'"' || bytes[0] == b'\'')
        && bytes[bytes.len() - 1] == bytes[0]
    {
        s[1..s.len() - 1].to_string()
    } else {
        s.to_string()
    }
}

fn lower_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => c.to_ascii_lowercase().to_string() + chars.as_str(),
        None => String::new(),
    }
}

/// Reduce an arbitrary string to a valid Luau identifier, or `None` if nothing usable
/// remains.
fn sanitize(s: &str) -> Option<String> {
    let mut out = String::new();
    for c in s.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            out.push(c);
        }
    }
    if out.is_empty() {
        return None;
    }
    if out.chars().next().unwrap().is_ascii_digit() {
        out.insert(0, '_');
    }
    Some(out)
}

/// Make `base` unique against `taken` by suffixing `2`, `3`, … (and avoiding keywords).
fn unique_name(base: &str, taken: &BTreeSet<String>) -> String {
    let base = if LUAU_KEYWORDS.contains(&base) {
        format!("{base}_")
    } else {
        base.to_string()
    };
    if !taken.contains(&base) {
        return base;
    }
    let mut i = 2u32;
    loop {
        let candidate = format!("{base}{i}");
        if !taken.contains(&candidate) {
            return candidate;
        }
        i += 1;
    }
}

const LUAU_KEYWORDS: &[&str] = &[
    "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in", "local",
    "nil", "not", "or", "repeat", "return", "then", "true", "until", "while", "continue", "self",
];

/// Render bytes as a complete, correctly-escaped Luau double-quoted string literal. Unlike
/// the disassembler's renderer (which truncates to 32 chars for readability), this is
/// lossless — it must round-trip through the compiler.
pub fn lua_string_literal(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() + 2);
    out.push('"');
    for &b in bytes {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7e => out.push(b as char),
            // Non-printable / non-ASCII: emit a numeric escape, valid for any byte.
            _ => out.push_str(&format!("\\{b}")),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Call(Box::new(Expr::Var(name.into())), args)
    }
    fn s(text: &str) -> Expr {
        Expr::Str(format!("\"{text}\""))
    }

    #[test]
    fn derives_roblox_names() {
        assert_eq!(
            derive_name(&call("require", vec![s("MyModule")])).as_deref(),
            Some("MyModule")
        );
        assert_eq!(
            derive_name(&call(
                "require",
                vec![Expr::Var("game.ReplicatedStorage.MyModule".into())]
            ))
            .as_deref(),
            Some("MyModule")
        );
        let getservice = Expr::MethodCall(
            Box::new(Expr::Var("game".into())),
            "GetService".into(),
            vec![s("Players")],
        );
        assert_eq!(derive_name(&getservice).as_deref(), Some("Players"));

        let instance_new = Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Var("Instance".into())),
                "new".into(),
            )),
            vec![s("Part")],
        );
        assert_eq!(derive_name(&instance_new).as_deref(), Some("part"));

        let require_field = Expr::Field(
            Box::new(call("require", vec![Expr::Var("game.X.MyModule".into())])),
            "doThing".into(),
        );
        assert_eq!(
            derive_name(&require_field).as_deref(),
            Some("MyModule_doThing")
        );

        let get_children = Expr::MethodCall(
            Box::new(Expr::Var("workspace".into())),
            "GetChildren".into(),
            vec![],
        );
        assert_eq!(derive_name(&get_children).as_deref(), Some("children"));

        let len = Expr::Unary("#", Box::new(Expr::Var("t".into())));
        assert_eq!(derive_name(&len).as_deref(), Some("count"));
    }

    #[test]
    fn string_literal_is_lossless_and_escaped() {
        assert_eq!(lua_string_literal(b"hi"), "\"hi\"");
        assert_eq!(lua_string_literal(b"a\"b\\c\n"), "\"a\\\"b\\\\c\\n\"");
        // 40-char string is not truncated.
        let long: Vec<u8> = std::iter::repeat(b'x').take(40).collect();
        assert_eq!(lua_string_literal(&long).len(), 42);
    }

    #[test]
    fn keeps_copies_and_literals_unnamed() {
        assert_eq!(derive_name(&Expr::Var("x".into())), None);
        assert_eq!(derive_name(&Expr::Num("3".into())), None);
        assert_eq!(derive_name(&Expr::Nil), None);
    }
}

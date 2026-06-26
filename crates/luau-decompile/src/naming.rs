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

use crate::ast::{Capture, Expr, Stmt, TableField};
use std::collections::{BTreeMap, BTreeSet};

/// Names matching this shape are decompiler-synthesized locals and may be renamed. Debug
/// names and parameters (`pN`) are left untouched.
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

fn collect_raw_locked(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for s in stmts {
        match s {
            Stmt::Local { values, .. } => {
                values.iter().for_each(|e| collect_raw_locked_expr(e, out))
            }
            Stmt::Assign { targets, values } => {
                targets.iter().for_each(|e| collect_raw_locked_expr(e, out));
                values.iter().for_each(|e| collect_raw_locked_expr(e, out));
            }
            Stmt::Call(e) => collect_raw_locked_expr(e, out),
            Stmt::Return(es) => es.iter().for_each(|e| collect_raw_locked_expr(e, out)),
            Stmt::If { cond, .. } => collect_raw_locked_expr(cond, out),
            Stmt::While { cond, .. } => collect_raw_locked_expr(cond, out),
            Stmt::Repeat { cond, .. } => collect_raw_locked_expr(cond, out),
            _ => {}
        }
        for_each_child_block(s, |body| collect_raw_locked(body, out));
    }
}

fn collect_raw_locked_expr(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Raw(text) => {
            for word in text.split(|c: char| !c.is_ascii_alphanumeric()) {
                if is_synthetic(word) || is_parameter(word) {
                    out.insert(word.to_string());
                }
            }
        }
        Expr::Index(t, k) => {
            collect_raw_locked_expr(t, out);
            collect_raw_locked_expr(k, out);
        }
        Expr::Field(t, _) => collect_raw_locked_expr(t, out),
        Expr::Call(f, args) => {
            collect_raw_locked_expr(f, out);
            args.iter().for_each(|a| collect_raw_locked_expr(a, out));
        }
        Expr::MethodCall(o, _, args) => {
            collect_raw_locked_expr(o, out);
            args.iter().for_each(|a| collect_raw_locked_expr(a, out));
        }
        Expr::Unary(_, a) => collect_raw_locked_expr(a, out),
        Expr::Binary(_, a, b) => {
            collect_raw_locked_expr(a, out);
            collect_raw_locked_expr(b, out);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => {
                        collect_raw_locked_expr(e, out)
                    }
                    TableField::Keyed(k, v) => {
                        collect_raw_locked_expr(k, out);
                        collect_raw_locked_expr(v, out);
                    }
                }
            }
        }
        _ => {}
    }
}

fn collect_captured_names(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for s in stmts {
        match s {
            Stmt::Local { values, .. } => values.iter().for_each(|e| collect_captured_expr(e, out)),
            Stmt::Assign { targets, values } => {
                targets.iter().for_each(|e| collect_captured_expr(e, out));
                values.iter().for_each(|e| collect_captured_expr(e, out));
            }
            Stmt::Call(e) => collect_captured_expr(e, out),
            Stmt::Return(es) => es.iter().for_each(|e| collect_captured_expr(e, out)),
            Stmt::If { cond, .. } => collect_captured_expr(cond, out),
            Stmt::While { cond, .. } => collect_captured_expr(cond, out),
            Stmt::Repeat { cond, .. } => collect_captured_expr(cond, out),
            _ => {}
        }
        for_each_child_block(s, |body| collect_captured_names(body, out));
    }
}

fn collect_captured_expr(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Closure { captures, .. } => {
            for cap in captures {
                if let Capture::Reg(r) = cap {
                    out.insert(format!("v{r}"));
                    out.insert(format!("p{r}"));
                }
            }
        }
        Expr::Index(t, k) => {
            collect_captured_expr(t, out);
            collect_captured_expr(k, out);
        }
        Expr::Field(t, _) => collect_captured_expr(t, out),
        Expr::Call(f, args) => {
            collect_captured_expr(f, out);
            args.iter().for_each(|a| collect_captured_expr(a, out));
        }
        Expr::MethodCall(o, _, args) => {
            collect_captured_expr(o, out);
            args.iter().for_each(|a| collect_captured_expr(a, out));
        }
        Expr::Unary(_, a) => collect_captured_expr(a, out),
        Expr::Binary(_, a, b) => {
            collect_captured_expr(a, out);
            collect_captured_expr(b, out);
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::Item(e) | TableField::Named(_, e) => collect_captured_expr(e, out),
                    TableField::Keyed(k, v) => {
                        collect_captured_expr(k, out);
                        collect_captured_expr(v, out);
                    }
                }
            }
        }
        _ => {}
    }
}

struct FactCollector {
    suggestions: BTreeMap<String, Vec<(String, u32)>>,
    param_method_receiver: BTreeSet<String>,
}

impl FactCollector {
    fn add_suggestion(&mut self, var: &str, name: String, score: u32) {
        if is_synthetic(var) || is_parameter(var) {
            self.suggestions
                .entry(var.to_string())
                .or_default()
                .push((name, score));
        }
    }

    fn visit_stmts(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            match s {
                Stmt::Local { names, values } => {
                    for (name, val) in names.iter().zip(values.iter()) {
                        if let Some(derived) = derive_name(val) {
                            self.add_suggestion(name, derived, 15);
                        }
                        self.visit_expr(val);
                    }
                }
                Stmt::Assign { targets, values } => {
                    if targets.len() == 1 && values.len() == 1 {
                        let target = &targets[0];
                        let value = &values[0];

                        if let Expr::Var(t_name) = target {
                            if let Some(derived) = derive_name(value) {
                                self.add_suggestion(t_name, derived, 15);
                            }
                        }

                        if let Expr::Field(_, field) = target {
                            if let Expr::Var(x_name) = value {
                                self.add_suggestion(x_name, lower_first(field), 8);
                            }
                        }

                        if let Expr::Index(_, key) = target {
                            if let Expr::Str(lit) = key.as_ref() {
                                if let Expr::Var(x_name) = value {
                                    self.add_suggestion(x_name, lower_first(&strip_quotes(lit)), 8);
                                }
                            }
                        }

                        if let Expr::Index(base, _) = target {
                            if let Expr::Var(x_name) = value {
                                if let Expr::Var(base_name) = base.as_ref() {
                                    self.add_suggestion(x_name, singular(base_name), 8);
                                }
                            }
                        }
                    }

                    for t in targets {
                        self.visit_expr(t);
                    }
                    for v in values {
                        self.visit_expr(v);
                    }
                }
                Stmt::Call(e) => self.visit_expr(e),
                Stmt::Return(es) => {
                    for e in es {
                        self.visit_expr(e);
                    }
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                } => {
                    if let Expr::Var(cond_name) = cond {
                        self.add_suggestion(cond_name, "enabled".to_string(), 5);
                    }
                    self.visit_expr(cond);
                    self.visit_stmts(then_body);
                    self.visit_stmts(else_body);
                }
                Stmt::While { cond, body } => {
                    self.visit_expr(cond);
                    self.visit_stmts(body);
                }
                Stmt::Repeat { body, cond } => {
                    self.visit_stmts(body);
                    self.visit_expr(cond);
                }
                Stmt::NumericFor {
                    var,
                    start,
                    limit,
                    step,
                    body,
                } => {
                    self.add_suggestion(var, "index".to_string(), 8);
                    self.add_suggestion(var, "i".to_string(), 6);
                    if let Expr::Var(limit_name) = limit {
                        self.add_suggestion(limit_name, "limit".to_string(), 6);
                    }
                    self.visit_expr(start);
                    self.visit_expr(limit);
                    if let Some(s) = step {
                        self.visit_expr(s);
                    }
                    self.visit_stmts(body);
                }
                Stmt::GenericFor { vars, exprs, body } => {
                    if let Some(first_expr) = exprs.first() {
                        let mut resolved_coll = None;
                        if let Expr::Call(callee, args) = first_expr {
                            if let Expr::Var(callee_name) = callee.as_ref() {
                                if (callee_name == "ipairs" || callee_name == "pairs")
                                    && !args.is_empty()
                                {
                                    resolved_coll = Some(&args[0]);
                                }
                            }
                        }
                        let coll_expr = resolved_coll.unwrap_or(first_expr);
                        if let Some(item_suggestion) = loop_item_suggestion(coll_expr) {
                            let item_suggestion = lower_first(&item_suggestion);
                            if vars.len() >= 2 {
                                self.add_suggestion(&vars[0], "index".to_string(), 8);
                                self.add_suggestion(&vars[0], "key".to_string(), 5);
                                self.add_suggestion(&vars[1], item_suggestion, 10);
                            } else if vars.len() == 1 {
                                self.add_suggestion(&vars[0], item_suggestion, 10);
                            }
                        } else if vars.len() >= 2 {
                            self.add_suggestion(&vars[0], "key".to_string(), 5);
                            self.add_suggestion(&vars[1], "value".to_string(), 5);
                        }
                    }
                    for e in exprs {
                        self.visit_expr(e);
                    }
                    self.visit_stmts(body);
                }
                _ => {}
            }
        }
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Field(base, field) => {
                if let Expr::Var(base_name) = base.as_ref() {
                    match field.as_str() {
                        "Character" => self.add_suggestion(base_name, "player".to_string(), 8),
                        "Parent" => {
                            self.add_suggestion(base_name, "instance".to_string(), 6);
                            self.add_suggestion(base_name, "part".to_string(), 4);
                        }
                        "Name" => {
                            self.add_suggestion(base_name, "instance".to_string(), 5);
                        }
                        "Humanoid" => self.add_suggestion(base_name, "character".to_string(), 8),
                        "HumanoidRootPart" => {
                            self.add_suggestion(base_name, "character".to_string(), 8)
                        }
                        "Position" | "CFrame" => {
                            self.add_suggestion(base_name, "part".to_string(), 5);
                            self.add_suggestion(base_name, "attachment".to_string(), 5);
                        }
                        _ => {}
                    }
                }
                self.visit_expr(base);
            }
            Expr::MethodCall(recv, method, args) => {
                if let Expr::Var(recv_name) = recv.as_ref() {
                    self.param_method_receiver.insert(recv_name.clone());

                    match method.as_str() {
                        "IsA" => {
                            self.add_suggestion(recv_name, "instance".to_string(), 8);
                            self.add_suggestion(recv_name, "part".to_string(), 6);
                        }
                        "FindFirstChild" | "WaitForChild" => {
                            self.add_suggestion(recv_name, "instance".to_string(), 8);
                        }
                        "GetChildren" | "GetDescendants" => {
                            self.add_suggestion(recv_name, "instance".to_string(), 8);
                        }
                        "Connect" | "ConnectParallel" | "Once" => {
                            self.add_suggestion(recv_name, "event".to_string(), 8);
                        }
                        "Fire" => {
                            self.add_suggestion(recv_name, "event".to_string(), 8);
                        }
                        "FireServer" | "InvokeServer" => {
                            self.add_suggestion(recv_name, "remoteEvent".to_string(), 8);
                        }
                        _ => {}
                    }
                }

                match method.as_str() {
                    "Connect" | "ConnectParallel" | "Once" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "callback".to_string(), 8);
                        }
                    }
                    "FindFirstChild" | "WaitForChild" | "FindFirstAncestor" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "name".to_string(), 5);
                        }
                    }
                    _ => {}
                }

                self.visit_expr(recv);
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::Call(callee, args) => {
                if let Expr::Var(callee_name) = callee.as_ref() {
                    if callee_name == "require" {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "module".to_string(), 8);
                        }
                    }
                }
                self.visit_expr(callee);
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::Index(base, key) => {
                self.visit_expr(base);
                self.visit_expr(key);
            }
            Expr::Unary(_, a) => self.visit_expr(a),
            Expr::Binary(op, a, b) => {
                if matches!(*op, "<" | "<=" | ">" | ">=" | "==" | "~=") {
                    if let Expr::Var(name) = a.as_ref() {
                        if let Expr::Var(limit_name) = b.as_ref() {
                            if limit_name.contains("limit") {
                                self.add_suggestion(name, "index".to_string(), 4);
                            }
                        }
                    }
                }
                self.visit_expr(a);
                self.visit_expr(b);
            }
            Expr::Table(fields) => {
                for f in fields {
                    match f {
                        TableField::Item(e) | TableField::Named(_, e) => self.visit_expr(e),
                        TableField::Keyed(k, v) => {
                            self.visit_expr(k);
                            self.visit_expr(v);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn select_name_base(
    var: &str,
    suggestions: &[(String, u32)],
    collector: &FactCollector,
    is_method: bool,
) -> Option<String> {
    if is_parameter(var)
        && collector.param_method_receiver.contains(var)
        && var == "p0"
        && is_method
    {
        return Some("self".to_string());
    }

    if suggestions.is_empty() {
        return None;
    }

    let mut scores: BTreeMap<String, u32> = BTreeMap::new();
    for (name, score) in suggestions {
        *scores.entry(name.clone()).or_default() += score;
    }

    let mut best_name: Option<String> = None;
    let mut max_score = 0;
    for (name, score) in scores {
        if score > max_score {
            max_score = score;
            best_name = Some(name);
        }
    }
    best_name
}

/// Compute a rename map for synthesized locals and parameters, keyed by their current name.
#[allow(dead_code)]
pub fn smart_rename(
    stmts: &[Stmt],
    hoist_names: &[String],
    is_method: bool,
) -> BTreeMap<String, String> {
    smart_rename_with_event(stmts, hoist_names, is_method, None)
}

fn is_candidate_loop_var(name: &str) -> bool {
    const LETTERS: &[&str] = &["i", "j", "k", "l", "m", "o", "p", "q", "r", "s"];
    LETTERS.contains(&name) || name.starts_with("idx")
}

pub fn smart_rename_with_event(
    stmts: &[Stmt],
    hoist_names: &[String],
    is_method: bool,
    event_name: Option<&str>,
) -> BTreeMap<String, String> {
    let mut candidates: BTreeSet<String> = hoist_names
        .iter()
        .filter(|n| is_synthetic(n))
        .cloned()
        .collect();

    let mut all_names = BTreeSet::new();
    collect_used_names(stmts, &mut all_names);
    for name in all_names {
        if is_parameter(&name) || is_synthetic(&name) || is_candidate_loop_var(&name) {
            candidates.insert(name);
        }
    }

    if candidates.is_empty() {
        return BTreeMap::new();
    }

    let mut raw_locked = BTreeSet::new();
    collect_raw_locked(stmts, &mut raw_locked);
    candidates.retain(|name| !raw_locked.contains(name));

    let mut defs: BTreeMap<String, Vec<Expr>> = BTreeMap::new();
    collect_all_defs(stmts, &candidates, &mut defs);

    let mut collector = FactCollector {
        suggestions: BTreeMap::new(),
        param_method_receiver: BTreeSet::new(),
    };
    collector.visit_stmts(stmts);

    let mut reserved: BTreeSet<String> = BTreeSet::new();
    collect_used_names(stmts, &mut reserved);
    for c in &candidates {
        reserved.remove(c);
    }
    reserved.extend(
        LUAU_KEYWORDS
            .iter()
            .filter(|&&k| k != "self")
            .map(|s| s.to_string()),
    );

    let mut base_map = BTreeMap::new();

    let mut captured_names = BTreeSet::new();
    collect_captured_names(stmts, &mut captured_names);

    let mut ordered: Vec<&String> = candidates.iter().collect();
    ordered.sort_by(|a, b| {
        let a_is_p = is_parameter(a);
        let b_is_p = is_parameter(b);
        if a_is_p != b_is_p {
            b_is_p.cmp(&a_is_p)
        } else {
            let a_is_c = captured_names.contains(*a);
            let b_is_c = captured_names.contains(*b);
            if a_is_c != b_is_c {
                b_is_c.cmp(&a_is_c)
            } else {
                let a_num: u32 = a[1..].parse().unwrap_or(0);
                let b_num: u32 = b[1..].parse().unwrap_or(0);
                a_num.cmp(&b_num)
            }
        }
    });

    // Pass 1: Derive base names from defs and suggestions
    for &orig in &ordered {
        let mut suggs = Vec::new();
        if let Some(list) = defs.get(orig) {
            let chosen = if list.len() == 1 {
                Some(&list[0])
            } else if list[1..].iter().all(|e| expr_references(e, orig)) {
                list.last()
            } else {
                None
            };
            if let Some(c) = chosen {
                if let Some(derived) = derive_name(c) {
                    suggs.push((derived, 15));
                }
                // Combined property field suggestions (e.g. input.Position -> inputPosition)
                if let Expr::Field(base, field) = c {
                    if let Expr::Var(base_name) = base.as_ref() {
                        let parent_name = base_map
                            .get(base_name)
                            .cloned()
                            .unwrap_or_else(|| base_name.clone());
                        if parent_name != "self"
                            && !is_synthetic(&parent_name)
                            && !is_parameter(&parent_name)
                        {
                            suggs.push((format!("{}{}", parent_name, upper_first(field)), 35));
                        }
                    }
                }
                if let Expr::Index(base, key) = c {
                    if let Expr::Var(base_name) = base.as_ref() {
                        if let Expr::Str(lit) = key.as_ref() {
                            let parent_name = base_map
                                .get(base_name)
                                .cloned()
                                .unwrap_or_else(|| base_name.clone());
                            if parent_name != "self"
                                && !is_synthetic(&parent_name)
                                && !is_parameter(&parent_name)
                            {
                                suggs.push((
                                    format!("{}{}", parent_name, upper_first(&strip_quotes(lit))),
                                    35,
                                ));
                            }
                        }
                    }
                }
            }
            if let Some(acc) = accumulator_name(orig, list) {
                suggs.push((acc, 20));
            }
        }

        if let Some(col_list) = collector.suggestions.get(orig) {
            suggs.extend(col_list.iter().cloned());
        }

        if let Some(event) = event_name {
            if is_parameter(orig) {
                let p_num: u32 = orig[1..].parse().unwrap_or(0);
                match event {
                    "InputBegan" | "InputChanged" | "InputEnded" => {
                        if p_num == 0 {
                            suggs.push(("input".to_string(), 25));
                        } else if p_num == 1 {
                            suggs.push(("gameProcessed".to_string(), 25));
                        }
                    }
                    "PlayerAdded" | "PlayerRemoving" | "OnServerEvent" if p_num == 0 => {
                        suggs.push(("player".to_string(), 25));
                    }
                    "ChildAdded" | "ChildRemoved" if p_num == 0 => {
                        suggs.push(("child".to_string(), 25));
                    }
                    "Touched" if p_num == 0 => {
                        suggs.push(("hit".to_string(), 25));
                    }
                    _ => {}
                }
            }
        }

        if let Some(base) = select_name_base(orig, &suggs, &collector, is_method) {
            base_map.insert(orig.clone(), base);
        }
    }

    // Pass 2: Let special naming helper passes suggest base names for remaining candidates
    apply_tuple_names(stmts, &candidates, &mut base_map);
    apply_field_sink_names(stmts, &candidates, &mut base_map);
    apply_returned_table_names(stmts, &defs, &candidates, &mut base_map);

    // Pass 3: Resolve final unique names in a stable order
    let mut map = BTreeMap::new();
    for &orig in &ordered {
        if let Some(base) = base_map.get(orig).and_then(|base| sanitize(base)) {
            let unique = unique_name(&base, &reserved);
            reserved.insert(unique.clone());
            map.insert(orig.clone(), unique);
        }
    }

    map
}

/// Conventional names for the destinations of a known multi-value call.
fn tuple_names_for(callee: &Expr, n: usize) -> Option<Vec<String>> {
    let name = match callee {
        Expr::Var(f) => last_segment(f)?,
        _ => return None,
    };
    let base: &[&str] = match name.as_str() {
        "pcall" | "xpcall" | "resume" => &["ok", "result"],
        "find" => &["startIndex", "endIndex"],
        "next" => &["key", "value"],
        "gsub" => &["replaced", "count"],
        _ => return None,
    };
    Some(
        (0..n)
            .map(|i| {
                base.get(i)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("result{}", i + 1))
            })
            .collect(),
    )
}

/// `local ok, result = pcall(f)` etc.: name the destinations of known tuple-returning calls.
fn apply_tuple_names(
    stmts: &[Stmt],
    candidates: &BTreeSet<String>,
    base_map: &mut BTreeMap<String, String>,
) {
    for s in stmts {
        if let Stmt::Assign { targets, values } = s {
            if values.len() == 1 && targets.len() >= 2 {
                if let Expr::Call(callee, _) = &values[0] {
                    if let Some(names) = tuple_names_for(callee, targets.len()) {
                        for (t, nm) in targets.iter().zip(names.iter()) {
                            if let Expr::Var(v) = t {
                                if candidates.contains(v) && !base_map.contains_key(v) {
                                    base_map.insert(v.clone(), nm.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
        for_each_child_block(s, |b| apply_tuple_names(b, candidates, base_map));
    }
}

/// A temporary later stored into a field/index gets named after that field
/// (`x = ...; obj.Health = x` => `health`).
fn apply_field_sink_names(
    stmts: &[Stmt],
    candidates: &BTreeSet<String>,
    base_map: &mut BTreeMap<String, String>,
) {
    for s in stmts {
        if let Stmt::Assign { targets, values } = s {
            if targets.len() == 1 && values.len() == 1 {
                if let Expr::Var(name) = &values[0] {
                    if candidates.contains(name) && !base_map.contains_key(name) {
                        let field = match &targets[0] {
                            Expr::Field(_, f) => Some(f.clone()),
                            Expr::Index(_, k) => match k.as_ref() {
                                Expr::Str(lit) => Some(strip_quotes(lit)),
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some(f) = field {
                            if f != "Parent" {
                                if let Some(base) = sanitize(&field_to_local_name(&f)) {
                                    base_map.insert(name.clone(), base);
                                }
                            }
                        }
                    }
                }
            }
        }
        for_each_child_block(s, |b| apply_field_sink_names(b, candidates, base_map));
    }
}

/// `local v0 = { ... }; return v0` is usually a module/export/result table. Give that
/// synthetic local a readable name when no definition-based heuristic found one.
fn apply_returned_table_names(
    stmts: &[Stmt],
    defs: &BTreeMap<String, Vec<Expr>>,
    candidates: &BTreeSet<String>,
    base_map: &mut BTreeMap<String, String>,
) {
    for s in stmts {
        if let Stmt::Return(values) = s {
            if let [Expr::Var(name)] = values.as_slice() {
                if candidates.contains(name) && !base_map.contains_key(name) {
                    if let Some([Expr::Table(fields)]) = defs.get(name).map(Vec::as_slice) {
                        let base = returned_table_name(fields);
                        base_map.insert(name.clone(), base.to_string());
                    }
                }
            }
        }
        for_each_child_block(s, |b| {
            apply_returned_table_names(b, defs, candidates, base_map)
        });
    }
}

fn returned_table_name(fields: &[TableField]) -> &'static str {
    if fields.iter().any(|field| match field {
        TableField::Named(name, value) => {
            matches!(value, Expr::Closure { .. }) || name.chars().any(|c| c.is_ascii_uppercase())
        }
        _ => false,
    }) {
        "module"
    } else {
        "result"
    }
}

fn accumulator_name(name: &str, defs: &[Expr]) -> Option<String> {
    if defs.len() < 2 {
        return None;
    }
    let Expr::Num(init) = &defs[0] else {
        return None;
    };

    let mut saw_add_sub = false;
    let mut saw_mul = false;
    for expr in &defs[1..] {
        match accumulator_step(name, expr)? {
            AccumulatorStep::AddSub => saw_add_sub = true,
            AccumulatorStep::Mul => saw_mul = true,
        }
    }

    if saw_add_sub && !saw_mul && num_literal_is(init, 0.0) {
        return Some("total".to_string());
    }
    if saw_mul && !saw_add_sub && num_literal_is(init, 1.0) {
        return Some("product".to_string());
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AccumulatorStep {
    AddSub,
    Mul,
}

fn accumulator_step(name: &str, expr: &Expr) -> Option<AccumulatorStep> {
    let Expr::Binary(op, a, b) = expr else {
        return None;
    };
    let other = match *op {
        "+" => {
            if is_var(a, name) {
                b.as_ref()
            } else if is_var(b, name) {
                a.as_ref()
            } else {
                return None;
            }
        }
        "-" => {
            if !is_var(a, name) {
                return None;
            }
            b.as_ref()
        }
        "*" => {
            if is_var(a, name) {
                b.as_ref()
            } else if is_var(b, name) {
                a.as_ref()
            } else {
                return None;
            }
        }
        _ => return None,
    };
    if expr_references(other, name) {
        return None;
    }
    Some(match *op {
        "+" | "-" => AccumulatorStep::AddSub,
        "*" => AccumulatorStep::Mul,
        _ => return None,
    })
}

fn num_literal_is(value: &str, expected: f64) -> bool {
    value
        .parse::<f64>()
        .map(|parsed| parsed == expected)
        .unwrap_or(false)
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
        | Expr::Closure { .. } => true,
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
        Stmt::Break | Stmt::Continue | Stmt::Label(_) | Stmt::Goto(_) | Stmt::Comment(_) => {}
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
        | Expr::Closure { .. }
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
            // Conventional names for well-known Roblox properties.
            if let Some(n) = roblox_field_name(field) {
                return Some(n.to_string());
            }
            // Otherwise the trailing field, read as an instance: player.Character -> character.
            sanitize(&field_to_local_name(field))
        }
        Expr::Index(base, key) => {
            if let Expr::Str(lit) = key.as_ref() {
                return sanitize(&strip_quotes(lit));
            }
            Some(index_value_name(base))
        }
        // #players -> playerCount ; #t -> count
        Expr::Unary(op, inner) if *op == "#" => Some(length_name(inner)),
        // Boolean-shaped expressions stored in a local: nil checks, emptiness checks.
        Expr::Binary(op, a, b) => derive_bool_name(op, a, b),
        _ => None,
    }
}

/// Conventional variable name for a well-known Roblox property field.
fn roblox_field_name(field: &str) -> Option<&'static str> {
    Some(match field {
        "LocalPlayer" => "localPlayer",
        "HumanoidRootPart" => "rootPart",
        "PrimaryPart" => "primaryPart",
        "CurrentCamera" => "camera",
        "CFrame" => "cframe",
        "Position" => "position",
        "Velocity" | "AssemblyLinearVelocity" => "velocity",
        "Parent" => "parent",
        _ => return None,
    })
}

/// Name a boolean-valued local after the shape of its condition.
fn derive_bool_name(op: &str, a: &Expr, b: &Expr) -> Option<String> {
    let noun = |e: &Expr| name_from_value(e).map(|n| upper_first(&n));
    match (op, b) {
        // x ~= nil -> hasX ; x == nil -> missingX
        ("~=", Expr::Nil) => noun(a).map(|n| format!("has{n}")),
        ("==", Expr::Nil) => noun(a).map(|n| format!("missing{n}")),
        // #t == 0 -> isEmpty ; #t > 0 -> hasItems
        ("==", Expr::Num(z)) if z == "0" && matches!(a, Expr::Unary("#", _)) => {
            Some("isEmpty".to_string())
        }
        (">", Expr::Num(z)) if z == "0" && matches!(a, Expr::Unary("#", _)) => {
            Some("hasItems".to_string())
        }
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
            "tick" => return Some("now".to_string()),
            "newproxy" => return Some("proxy".to_string()),
            "select" => return Some("selected".to_string()),
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
        // Standard-library results worth naming.
        match (owner.as_str(), member.as_str()) {
            ("table", "remove") => return Some("removed".to_string()),
            ("table", "find") => return Some("index".to_string()),
            ("table", "pack") => return Some("args".to_string()),
            ("table", "concat") => return Some("joined".to_string()),
            ("table", "create") => return Some("list".to_string()),
            ("table", "clone") => return Some("copy".to_string()),
            ("math", "random") => return Some("random".to_string()),
            ("math", "floor") | ("math", "ceil") | ("math", "round") => {
                return Some("rounded".to_string())
            }
            ("math", "sqrt") => return Some("root".to_string()),
            ("os", "time") | ("os", "clock") => return Some("now".to_string()),
            ("os", "date") => return Some("date".to_string()),
            ("task", "wait") => return Some("dt".to_string()),
            ("string", "format") => return Some("formatted".to_string()),
            ("string", "gsub") => return Some("replaced".to_string()),
            ("string", "split") => return Some("parts".to_string()),
            ("string", "rep") => return Some("repeated".to_string()),
            ("string", "sub") => return Some("substring".to_string()),
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
        // :IsA("BasePart") -> isBasePart (boolean named after the class).
        "IsA" => match args.first() {
            Some(Expr::Str(lit)) => sanitize(&format!("is{}", upper_first(&strip_quotes(lit)))),
            _ => method_to_noun(method),
        },
        // :GetAttribute("Speed") -> speed ; :GetPropertyChangedSignal("Health") -> healthChangedSignal.
        "GetAttribute" => match args.first() {
            Some(Expr::Str(lit)) => sanitize(&lower_first(&strip_quotes(lit))),
            _ => None,
        },
        "GetPropertyChangedSignal" | "GetAttributeChangedSignal" => match args.first() {
            Some(Expr::Str(lit)) => {
                sanitize(&format!("{}ChangedSignal", lower_first(&strip_quotes(lit))))
            }
            _ => Some("changedSignal".to_string()),
        },
        // Spatial queries.
        "Raycast" | "Blockcast" | "Shapecast" | "Spherecast" => Some("raycastResult".to_string()),
        "Dot" => Some("dotProduct".to_string()),
        "Cross" => Some("crossProduct".to_string()),
        "Lerp" => Some("lerped".to_string()),
        "GetMouseLocation" => Some("mouseLocation".to_string()),
        "GetMouseDelta" => Some("mouseDelta".to_string()),
        "UserOwnsGamePassAsync" => Some("ownsGamePass".to_string()),
        "GetUserIdFromNameAsync" => Some("userId".to_string()),
        // Common Roblox/HTTP/DataStore/stdlib result nouns.
        "Clone" => Some("clone".to_string()),
        "GetPivot" => Some("pivot".to_string()),
        "JSONDecode" => Some("decoded".to_string()),
        "JSONEncode" => Some("json".to_string()),
        "GetAsync" => Some("data".to_string()),
        "SetAsync" | "UpdateAsync" => Some("setResult".to_string()),
        "GetDataStore" | "GetOrderedDataStore" => Some("store".to_string()),
        "SubscribeAsync" => Some("subscription".to_string()),
        "GenerateGUID" => Some("guid".to_string()),
        "format" => Some("formatted".to_string()),
        "gsub" => Some("replaced".to_string()),
        "split" => Some("parts".to_string()),
        "sub" => Some("substring".to_string()),
        // GetChildren -> children, GetPlayers -> players, Clone -> clone, etc.
        _ => method_to_noun(method),
    }
}

fn upper_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => c.to_ascii_uppercase().to_string() + chars.as_str(),
        None => String::new(),
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

/// #players -> playerCount, #workspace:GetChildren() -> childCount, #t -> count.
fn length_name(inner: &Expr) -> String {
    if let Some(base) = collection_name(inner) {
        if base == "children" {
            return "childCount".to_string();
        }
        if base.len() > 1 && base.ends_with('s') && !base.ends_with("ss") {
            return format!("{}Count", singular(&base));
        }
    }
    "count".to_string()
}

fn index_value_name(base: &Expr) -> String {
    if let Some(base) = collection_name(base) {
        if base == "children" {
            return "child".to_string();
        }
        if base.len() > 1 && base.ends_with('s') && !base.ends_with("ss") {
            return singular(&base);
        }
    }
    "value".to_string()
}

fn collection_name(e: &Expr) -> Option<String> {
    if let Some(name) = name_from_value(e) {
        return Some(name);
    }
    match e {
        Expr::Call(callee, args) => derive_from_call(callee, args),
        Expr::MethodCall(recv, method, args) => derive_from_method(recv, method, args),
        _ => None,
    }
}

fn loop_item_suggestion(coll_expr: &Expr) -> Option<String> {
    if let Expr::MethodCall(recv, method, _) = coll_expr {
        let m = method.as_str();
        if m == "GetChildren" || m == "GetDescendants" || m == "GetPlayers" {
            if let Some(recv_name) = name_from_value(recv) {
                let s_name = recv_name.to_lowercase();
                if s_name != "workspace" && s_name != "game" {
                    return Some(singular(&recv_name));
                }
            }
            if m == "GetChildren" {
                return Some("child".to_string());
            } else if m == "GetDescendants" {
                return Some("descendant".to_string());
            } else if m == "GetPlayers" {
                return Some("player".to_string());
            }
        }
    }
    collection_name(coll_expr).map(|c| singular(&c))
}

fn singular(s: &str) -> String {
    if s == "children" {
        return "child".to_string();
    }
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
pub(crate) fn last_segment(s: &str) -> Option<String> {
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

/// Turn a field name into a local name: ALL-CAPS constants become fully lowercase
/// (`REWARDS` -> `rewards`), otherwise just lowercase the first letter (`MaxHealth` ->
/// `maxHealth`).
fn field_to_local_name(f: &str) -> String {
    if f.chars().any(|c| c.is_ascii_lowercase()) {
        lower_first(f)
    } else {
        f.to_ascii_lowercase()
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
    let base = if base != "self" && LUAU_KEYWORDS.contains(&base) {
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

        let child_count = Expr::Unary("#", Box::new(get_children));
        assert_eq!(derive_name(&child_count).as_deref(), Some("childCount"));

        let item = Expr::Index(
            Box::new(Expr::Var("items".into())),
            Box::new(Expr::Var("i".into())),
        );
        assert_eq!(derive_name(&item).as_deref(), Some("item"));

        let value = Expr::Index(
            Box::new(Expr::Var("p0".into())),
            Box::new(Expr::Var("i".into())),
        );
        assert_eq!(derive_name(&value).as_deref(), Some("value"));
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
    fn derives_more_nouns() {
        let isa = Expr::MethodCall(
            Box::new(Expr::Var("part".into())),
            "IsA".into(),
            vec![s("BasePart")],
        );
        assert_eq!(derive_name(&isa).as_deref(), Some("isBasePart"));

        let clone = Expr::MethodCall(Box::new(Expr::Var("model".into())), "Clone".into(), vec![]);
        assert_eq!(derive_name(&clone).as_deref(), Some("clone"));

        let attr = Expr::MethodCall(
            Box::new(Expr::Var("p".into())),
            "GetAttribute".into(),
            vec![s("Speed")],
        );
        assert_eq!(derive_name(&attr).as_deref(), Some("speed"));

        let raycast = Expr::MethodCall(
            Box::new(Expr::Var("workspace".into())),
            "Raycast".into(),
            vec![],
        );
        assert_eq!(derive_name(&raycast).as_deref(), Some("raycastResult"));

        // x ~= nil -> hasX
        let has = Expr::Binary(
            "~=",
            Box::new(Expr::MethodCall(
                Box::new(Expr::Var("m".into())),
                "FindFirstChild".into(),
                vec![s("Seat")],
            )),
            Box::new(Expr::Nil),
        );
        assert_eq!(derive_name(&has).as_deref(), Some("hasSeat"));

        // string.format(...) -> formatted (dotted-import callee)
        let fmt = call("string.format", vec![s("%d")]);
        assert_eq!(derive_name(&fmt).as_deref(), Some("formatted"));

        // os.time() -> now
        let now = call("os.time", vec![]);
        assert_eq!(derive_name(&now).as_deref(), Some("now"));
    }

    #[test]
    fn keeps_copies_and_literals_unnamed() {
        assert_eq!(derive_name(&Expr::Var("x".into())), None);
        assert_eq!(derive_name(&Expr::Num("3".into())), None);
        assert_eq!(derive_name(&Expr::Nil), None);
    }

    #[test]
    fn names_returned_module_tables() {
        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("v0".into())],
                values: vec![Expr::Table(vec![TableField::Named(
                    "MAX_REWARD".into(),
                    Expr::Num("250".into()),
                )])],
            },
            Stmt::Return(vec![Expr::Var("v0".into())]),
        ];
        let map = smart_rename(&stmts, &[String::from("v0")], false);
        assert_eq!(map.get("v0").map(String::as_str), Some("module"));
    }

    #[test]
    fn names_numeric_accumulators() {
        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("v1".into())],
                values: vec![Expr::Num("0".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v1".into())],
                values: vec![Expr::Binary(
                    "+",
                    Box::new(Expr::Var("v1".into())),
                    Box::new(Expr::Var("p0".into())),
                )],
            },
        ];
        let map = smart_rename(&stmts, &[String::from("v1")], false);
        assert_eq!(map.get("v1").map(String::as_str), Some("total"));

        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("v2".into())],
                values: vec![Expr::Num("1".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v2".into())],
                values: vec![Expr::Binary(
                    "*",
                    Box::new(Expr::Var("v2".into())),
                    Box::new(Expr::Var("p0".into())),
                )],
            },
        ];
        let map = smart_rename(&stmts, &[String::from("v2")], false);
        assert_eq!(map.get("v2").map(String::as_str), Some("product"));
    }

    #[test]
    fn raw_lock_prevents_renaming_v3() {
        let stmts = vec![Stmt::Assign {
            targets: vec![Expr::Var("v3".into())],
            values: vec![Expr::Raw("some text with v3 inside".into())],
        }];
        let map = smart_rename(&stmts, &[String::from("v3")], false);
        assert!(!map.contains_key("v3"));
    }

    #[test]
    fn raw_lock_prevents_renaming_p0() {
        let stmts = vec![Stmt::Assign {
            targets: vec![Expr::Var("p0".into())],
            values: vec![Expr::Raw("some text with p0 inside".into())],
        }];
        let map = smart_rename(&stmts, &[String::from("p0")], false);
        assert!(!map.contains_key("p0"));
    }

    #[test]
    fn plain_helper_p0_does_not_become_self() {
        let stmts = vec![Stmt::Return(vec![Expr::Field(
            Box::new(Expr::Var("p0".into())),
            "Name".into(),
        )])];
        let map = smart_rename(&stmts, &[String::from("p0")], false);
        assert_ne!(map.get("p0").map(String::as_str), Some("self"));
    }

    #[test]
    fn method_assignment_uses_self_safely() {
        let stmts = vec![Stmt::Call(Expr::MethodCall(
            Box::new(Expr::Var("p0".into())),
            "DoSomething".into(),
            vec![],
        ))];
        let map = smart_rename(&stmts, &[String::from("p0")], true);
        assert_eq!(map.get("p0").map(String::as_str), Some("self"));
    }

    #[test]
    fn deterministic_unique_suffixes() {
        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("v0".into())],
                values: vec![Expr::MethodCall(
                    Box::new(Expr::Var("p0".into())),
                    "FindFirstChild".into(),
                    vec![Expr::Str("\"child\"".into())],
                )],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v1".into())],
                values: vec![Expr::MethodCall(
                    Box::new(Expr::Var("p0".into())),
                    "FindFirstChild".into(),
                    vec![Expr::Str("\"child\"".into())],
                )],
            },
        ];
        let map = smart_rename(&stmts, &[String::from("v0"), String::from("v1")], false);
        assert_eq!(map.get("v0").map(String::as_str), Some("child"));
        assert_eq!(map.get("v1").map(String::as_str), Some("child2"));
    }

    #[test]
    fn keyword_candidates_are_sanitized() {
        let stmts = vec![Stmt::Assign {
            targets: vec![Expr::Var("v0".into())],
            values: vec![Expr::MethodCall(
                Box::new(Expr::Var("p0".into())),
                "FindFirstChild".into(),
                vec![Expr::Str("\"end\"".into())],
            )],
        }];
        let map = smart_rename(&stmts, &[String::from("v0")], false);
        assert_eq!(map.get("v0").map(String::as_str), Some("end_"));
    }

    #[test]
    fn unsafe_string_key_candidates_are_sanitized() {
        let stmts = vec![Stmt::Assign {
            targets: vec![Expr::Index(
                Box::new(Expr::Var("tables".into())),
                Box::new(Expr::Str("\"\\0\\0\\0\"".into())),
            )],
            values: vec![Expr::Var("p1".into())],
        }];

        let map = smart_rename(&stmts, &[], false);

        assert_eq!(map.get("p1").map(String::as_str), Some("_000"));
    }

    #[test]
    fn property_field_combined_naming() {
        let stmts = vec![
            Stmt::Local {
                names: vec!["input".into()],
                values: vec![Expr::Var("p0".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v0".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("input".into())),
                    "Position".into(),
                )],
            },
        ];
        let map = smart_rename_with_event(&stmts, &[String::from("v0")], false, None);
        assert_eq!(map.get("v0").map(String::as_str), Some("inputPosition"));
    }

    #[test]
    fn event_callback_parameter_naming() {
        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("p0".into())],
                values: vec![Expr::Num("1".into())],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("p1".into())],
                values: vec![Expr::Bool(true)],
            },
        ];
        let map = smart_rename_with_event(&stmts, &[], false, Some("InputBegan"));
        assert_eq!(map.get("p0").map(String::as_str), Some("input"));
        assert_eq!(map.get("p1").map(String::as_str), Some("gameProcessed"));
    }

    #[test]
    fn loop_collections_naming() {
        let stmts = vec![Stmt::GenericFor {
            vars: vec!["_".into(), "v0".into()],
            exprs: vec![Expr::MethodCall(
                Box::new(Expr::Var("buttons".into())),
                "GetChildren".into(),
                vec![],
            )],
            body: vec![],
        }];
        let map = smart_rename_with_event(&stmts, &[], false, None);
        assert_eq!(map.get("v0").map(String::as_str), Some("button"));
    }
}

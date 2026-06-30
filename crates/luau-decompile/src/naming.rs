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
                                let name = param_name_from_field_key(field)
                                    .unwrap_or_else(|| lower_first(field));
                                self.add_suggestion(x_name, name, 8);
                            }
                        }

                        if let Expr::Index(_, key) = target {
                            if let Expr::Str(lit) = key.as_ref() {
                                if let Expr::Var(x_name) = value {
                                    let key = strip_quotes(lit);
                                    let name = param_name_from_field_key(&key)
                                        .unwrap_or_else(|| lower_first(&key));
                                    self.add_suggestion(x_name, name, 8);
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
                        "UserId" | "DisplayName" | "PlayerGui" | "Backpack" | "Team"
                        | "AccountAge" | "MembershipType" | "Neutral" => {
                            self.add_suggestion(base_name, "player".to_string(), 8)
                        }
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
                        "PrimaryPart" => self.add_suggestion(base_name, "model".to_string(), 8),
                        "Health" | "MaxHealth" | "WalkSpeed" | "JumpPower" | "JumpHeight"
                        | "MoveDirection" | "FloorMaterial" | "Sit" | "RigType" | "Animator" => {
                            self.add_suggestion(base_name, "humanoid".to_string(), 8);
                        }
                        "Position"
                        | "CFrame"
                        | "Size"
                        | "Material"
                        | "Transparency"
                        | "Anchored"
                        | "CanCollide"
                        | "CanTouch"
                        | "CanQuery"
                        | "Massless"
                        | "AssemblyLinearVelocity"
                        | "AssemblyAngularVelocity" => {
                            self.add_suggestion(base_name, "part".to_string(), 5);
                            self.add_suggestion(base_name, "attachment".to_string(), 5);
                        }
                        "Text" | "TextColor3" | "TextSize" | "Font" | "RichText" => {
                            self.add_suggestion(base_name, "label".to_string(), 7);
                            self.add_suggestion(base_name, "guiObject".to_string(), 5);
                        }
                        "Visible"
                        | "AbsoluteSize"
                        | "AbsolutePosition"
                        | "AnchorPoint"
                        | "LayoutOrder"
                        | "ZIndex"
                        | "BackgroundColor3"
                        | "BackgroundTransparency" => {
                            self.add_suggestion(base_name, "guiObject".to_string(), 7);
                        }
                        "MouseButton1Click" | "MouseButton1Down" | "MouseButton1Up"
                        | "MouseButton2Click" | "MouseButton2Down" | "MouseButton2Up"
                        | "Activated" => {
                            self.add_suggestion(base_name, "button".to_string(), 8);
                        }
                        "SoundId" | "Volume" | "PlaybackSpeed" | "TimePosition" | "IsPlaying"
                        | "Looped" => {
                            self.add_suggestion(base_name, "sound".to_string(), 8);
                        }
                        "FieldOfView" | "CameraType" | "CameraSubject" | "Focus" => {
                            self.add_suggestion(base_name, "camera".to_string(), 8);
                        }
                        "Brightness" | "Range" => {
                            self.add_suggestion(base_name, "light".to_string(), 8);
                        }
                        "Part0" | "Part1" | "C0" | "C1" => {
                            self.add_suggestion(base_name, "weld".to_string(), 8);
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
                            if let Some(Expr::Str(class)) = args.first() {
                                if let Some(name) = class_name_hint(&strip_quotes(class)) {
                                    self.add_suggestion(recv_name, name, 9);
                                }
                            }
                        }
                        "FindFirstChild"
                        | "WaitForChild"
                        | "FindFirstChildOfClass"
                        | "FindFirstChildWhichIsA"
                        | "FindFirstAncestor"
                        | "FindFirstAncestorOfClass"
                        | "FindFirstAncestorWhichIsA"
                        | "IsDescendantOf"
                        | "Destroy"
                        | "Clone"
                        | "GetFullName" => {
                            self.add_suggestion(recv_name, "instance".to_string(), 8);
                        }
                        "GetChildren" | "GetDescendants" => {
                            self.add_suggestion(recv_name, "instance".to_string(), 8);
                        }
                        "LoadAnimation" => {
                            self.add_suggestion(recv_name, "animator".to_string(), 9);
                        }
                        "Connect" | "ConnectParallel" | "Once" => {
                            self.add_suggestion(recv_name, "event".to_string(), 8);
                        }
                        "Disconnect" => {
                            self.add_suggestion(recv_name, "connection".to_string(), 9);
                        }
                        "Fire" => {
                            self.add_suggestion(recv_name, "event".to_string(), 8);
                        }
                        "FireServer" | "FireClient" | "FireAllClients" => {
                            self.add_suggestion(recv_name, "remoteEvent".to_string(), 8);
                        }
                        "InvokeServer" | "InvokeClient" => {
                            self.add_suggestion(recv_name, "remoteFunction".to_string(), 8);
                        }
                        "GetPivot" | "PivotTo" | "GetBoundingBox" => {
                            self.add_suggestion(recv_name, "model".to_string(), 7);
                        }
                        "GetAttribute" | "SetAttribute" | "GetAttributeChangedSignal" => {
                            self.add_suggestion(recv_name, "instance".to_string(), 7);
                        }
                        "Kick" | "LoadCharacter" | "GetMouse" | "GetRankInGroup"
                        | "GetRoleInGroup" | "IsInGroup" => {
                            self.add_suggestion(recv_name, "player".to_string(), 8);
                        }
                        "TakeDamage"
                        | "ChangeState"
                        | "GetState"
                        | "MoveTo"
                        | "GetPlayingAnimationTracks"
                        | "UnequipTools"
                        | "EquipTool"
                        | "ApplyDescription"
                        | "GetAppliedDescription" => {
                            self.add_suggestion(recv_name, "humanoid".to_string(), 8);
                        }
                        "GetTouchingParts"
                        | "GetMass"
                        | "ApplyImpulse"
                        | "ApplyAngularImpulse"
                        | "SetNetworkOwner"
                        | "GetNetworkOwner" => {
                            self.add_suggestion(recv_name, "part".to_string(), 8);
                        }
                        "TweenPosition" | "TweenSize" | "TweenSizeAndPosition" => {
                            self.add_suggestion(recv_name, "guiObject".to_string(), 8);
                        }
                        "JSONDecode" | "JSONEncode" => {
                            self.add_suggestion(recv_name, "httpService".to_string(), 8);
                        }
                        "AddTag" | "RemoveTag" | "HasTag" | "GetTagged" => {
                            self.add_suggestion(recv_name, "collectionService".to_string(), 8);
                        }
                        "GetAsync" | "SetAsync" | "UpdateAsync" | "IncrementAsync"
                        | "RemoveAsync" => {
                            self.add_suggestion(recv_name, "dataStore".to_string(), 8);
                        }
                        "PublishAsync" | "SubscribeAsync" => {
                            self.add_suggestion(recv_name, "messagingService".to_string(), 8);
                        }
                        "CreatePath" => {
                            self.add_suggestion(recv_name, "pathfindingService".to_string(), 8);
                        }
                        "BindToRenderStep" | "UnbindFromRenderStep" => {
                            self.add_suggestion(recv_name, "runService".to_string(), 8);
                        }
                        "BindAction" | "BindActionAtPriority" | "UnbindAction" => {
                            self.add_suggestion(recv_name, "contextActionService".to_string(), 8);
                        }
                        "GetInstanceAddedSignal" | "GetInstanceRemovedSignal" => {
                            self.add_suggestion(recv_name, "collectionService".to_string(), 8);
                        }
                        "Create" if args.len() >= 3 => {
                            self.add_suggestion(recv_name, "tweenService".to_string(), 8);
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
                            self.add_suggestion(arg_name, "childName".to_string(), 7);
                            self.add_suggestion(arg_name, "name".to_string(), 5);
                        }
                    }
                    "IsA" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "className".to_string(), 8);
                        }
                    }
                    "GetAttribute" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "attributeName".to_string(), 7);
                        }
                    }
                    "SetAttribute" => {
                        if let (Some(Expr::Str(key)), Some(Expr::Var(arg_name))) =
                            (args.first(), args.get(1))
                        {
                            if let Some(name) = param_name_from_field_key(&strip_quotes(key)) {
                                self.add_suggestion(arg_name, name, 9);
                            }
                        }
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "attributeName".to_string(), 7);
                        }
                    }
                    "GetPropertyChangedSignal" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "propertyName".to_string(), 8);
                        }
                    }
                    "LoadAnimation" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "animation".to_string(), 8);
                        }
                    }
                    "AddTag" | "RemoveTag" | "HasTag" | "GetTagged" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "tagName".to_string(), 8);
                        }
                    }
                    "GetRankInGroup" | "GetRoleInGroup" | "IsInGroup" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "groupId".to_string(), 8);
                        }
                    }
                    "SetNetworkOwner" | "FireClient" | "InvokeClient" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "player".to_string(), 8);
                        }
                    }
                    "Create" if args.len() >= 3 => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "object".to_string(), 6);
                        }
                        if let Some(Expr::Var(arg_name)) = args.get(1) {
                            self.add_suggestion(arg_name, "tweenInfo".to_string(), 8);
                        }
                        if let Some(Expr::Var(arg_name)) = args.get(2) {
                            self.add_suggestion(arg_name, "properties".to_string(), 8);
                        }
                    }
                    "BindToRenderStep" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "renderStepName".to_string(), 8);
                        }
                        if let Some(Expr::Var(arg_name)) = args.get(2) {
                            self.add_suggestion(arg_name, "callback".to_string(), 8);
                        }
                    }
                    "BindAction" | "BindActionAtPriority" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "actionName".to_string(), 8);
                        }
                        if let Some(Expr::Var(arg_name)) = args.get(1) {
                            self.add_suggestion(arg_name, "callback".to_string(), 8);
                        }
                    }
                    "GetInstanceAddedSignal" | "GetInstanceRemovedSignal" => {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "tagName".to_string(), 8);
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
                if let Some(index) = callback_arg_index(callee) {
                    if let Some(Expr::Var(arg_name)) = args.get(index) {
                        self.add_suggestion(arg_name, "callback".to_string(), 8);
                    }
                }
                if let Expr::Var(callee_name) = callee.as_ref() {
                    if callee_name == "require" {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "module".to_string(), 8);
                        }
                    }
                    if matches!(callee_name.as_str(), "pcall" | "xpcall") {
                        if let Some(Expr::Var(arg_name)) = args.first() {
                            self.add_suggestion(arg_name, "callback".to_string(), 8);
                        }
                    }
                    if let Some(Expr::Var(arg_name)) = args.first() {
                        if callee_name.ends_with("Connect")
                            || callee_name.ends_with("ConnectParallel")
                            || callee_name.ends_with("Once")
                        {
                            self.add_suggestion(arg_name, "callback".to_string(), 7);
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
                if matches!(*op, "==" | "~=") {
                    if let Some((name, type_name)) = type_guard_name(a, b) {
                        if let Some(base) = type_name_hint(type_name) {
                            self.add_suggestion(name, base.to_string(), 7);
                        }
                    }
                }
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
                        TableField::Item(e) => self.visit_expr(e),
                        TableField::Named(name, e) => {
                            if let Expr::Var(var) = e {
                                if let Some(callback_name) = callback_field_name(name) {
                                    self.add_suggestion(var, callback_name, 9);
                                }
                            }
                            self.visit_expr(e);
                        }
                        TableField::Keyed(k, v) => {
                            if let (Expr::Str(lit), Expr::Var(var)) = (k, v) {
                                if let Some(callback_name) = callback_field_name(&strip_quotes(lit))
                                {
                                    self.add_suggestion(var, callback_name, 9);
                                }
                            }
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

fn event_param_name(event: &str, index: u32) -> Option<&'static str> {
    match event {
        "InputBegan" | "InputChanged" | "InputEnded" => match index {
            0 => Some("input"),
            1 => Some("gameProcessed"),
            _ => None,
        },
        "Heartbeat" | "RenderStepped" | "PreSimulation" | "PostSimulation" | "PreRender"
        | "PreAnimation" => match index {
            0 => Some("deltaTime"),
            _ => None,
        },
        "Stepped" => match index {
            0 => Some("time"),
            1 => Some("deltaTime"),
            _ => None,
        },
        "PlayerAdded" | "PlayerRemoving" | "OnServerEvent" => match index {
            0 => Some("player"),
            _ => None,
        },
        "OnServerInvoke" => match index {
            0 => Some("player"),
            _ => None,
        },
        "OnClientEvent" | "OnClientInvoke" => match index {
            0 => Some("payload"),
            _ => None,
        },
        "CharacterAdded" | "CharacterRemoving" | "CharacterAppearanceLoaded" => match index {
            0 => Some("character"),
            _ => None,
        },
        "ChildAdded" | "ChildRemoved" => match index {
            0 => Some("child"),
            _ => None,
        },
        "DescendantAdded" | "DescendantRemoving" => match index {
            0 => Some("descendant"),
            _ => None,
        },
        "AncestryChanged" => match index {
            0 => Some("child"),
            1 => Some("parent"),
            _ => None,
        },
        "Changed" => match index {
            0 => Some("property"),
            _ => None,
        },
        "Touched" => match index {
            0 => Some("hit"),
            _ => None,
        },
        "TouchEnded" => match index {
            0 => Some("otherPart"),
            _ => None,
        },
        "Triggered"
        | "TriggerEnded"
        | "PromptTriggered"
        | "PromptButtonHoldBegan"
        | "PromptButtonHoldEnded" => match index {
            0 => Some("player"),
            _ => None,
        },
        "Activated" => match index {
            0 => Some("input"),
            1 => Some("clickCount"),
            _ => None,
        },
        "FocusLost" => match index {
            0 => Some("enterPressed"),
            1 => Some("input"),
            _ => None,
        },
        "Equipped" => match index {
            0 => Some("mouse"),
            _ => None,
        },
        "HealthChanged" => match index {
            0 => Some("health"),
            _ => None,
        },
        "StateChanged" => match index {
            0 => Some("oldState"),
            1 => Some("newState"),
            _ => None,
        },
        "Running" | "Climbing" | "Swimming" => match index {
            0 => Some("speed"),
            _ => None,
        },
        "Jumping" | "FreeFalling" => match index {
            0 => Some("active"),
            _ => None,
        },
        "Seated" => match index {
            0 => Some("active"),
            1 => Some("seatPart"),
            _ => None,
        },
        "AnimationPlayed" => match index {
            0 => Some("track"),
            _ => None,
        },
        "KeyframeReached" => match index {
            0 => Some("keyframeName"),
            _ => None,
        },
        _ => None,
    }
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

    let conflicting_defs: BTreeSet<String> = defs
        .iter()
        .filter(|(_, values)| definitions_have_conflicting_names(values))
        .map(|(name, _)| name.clone())
        .collect();
    let stable_candidates: BTreeSet<String> = candidates
        .iter()
        .filter(|name| !conflicting_defs.contains(*name))
        .cloned()
        .collect();

    // Pass 1: Derive base names from defs and suggestions
    for &orig in &ordered {
        let mut suggs = Vec::new();
        let defs_conflict = conflicting_defs.contains(orig);
        if let Some(list) = defs.get(orig).filter(|_| !defs_conflict) {
            let chosen = if list.len() == 1 {
                Some(&list[0])
            } else if list[1..].iter().all(|e| expr_references(e, orig)) {
                list.last()
            } else {
                // Multi-definition but non-conflicting (the definitions don't vote for differing
                // names): a register reused for the same kind of value — e.g. `Instance.new("X")`
                // in several branches, or the same field/child lookup — should still be named.
                // Pick the first definition that yields a name; since they don't conflict, any
                // named one is representative of the whole lifetime.
                list.iter().find(|e| derive_name(e).is_some())
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

        if !defs_conflict {
            if let Some(col_list) = collector.suggestions.get(orig) {
                suggs.extend(col_list.iter().cloned());
            }
        } else if let Some(name) = defs.get(orig).and_then(|list| lifetime_name(list)) {
            // The definitions disagree on a single specific name, but share a class family
            // (Motor6D + Weld -> "joint") or form a divergent part role (PrimaryPart +
            // FindFirstChild("Middle") -> "mainPart"). Name it from the whole lifetime instead
            // of leaving it as a synthetic vN. (Non-conflicting variables are untouched.)
            suggs.push((name, 40));
        }

        if let Some(event) = event_name {
            if is_parameter(orig) {
                let p_num: u32 = orig[1..].parse().unwrap_or(0);
                if let Some(name) = event_param_name(event, p_num) {
                    suggs.push((name.to_string(), 25));
                }
            }
        }

        if let Some(base) = select_name_base(orig, &suggs, &collector, is_method) {
            base_map.insert(orig.clone(), base);
        }
    }

    // Pass 2: Let special naming helper passes suggest base names for remaining candidates
    apply_tuple_names(stmts, &stable_candidates, &mut base_map);
    apply_field_sink_names(stmts, &stable_candidates, &mut base_map);
    apply_returned_table_names(stmts, &defs, &stable_candidates, &mut base_map);

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

fn definitions_have_conflicting_names(values: &[Expr]) -> bool {
    let mut names = BTreeSet::new();
    for value in values {
        if let Some(name) = definition_name_vote(value) {
            names.insert(name);
            if names.len() > 1 {
                return true;
            }
        }
    }
    false
}

fn definition_name_vote(value: &Expr) -> Option<String> {
    match value {
        Expr::Nil | Expr::Bool(_) | Expr::Num(_) | Expr::Str(_) | Expr::Vector(_) => None,
        Expr::Var(name) if is_synthetic(name) || is_parameter(name) => None,
        _ => derive_name(value).or_else(|| name_from_value(value)),
    }
}

/// Conventional names for the destinations of a known multi-value call.
fn tuple_names_for(callee: &Expr, n: usize) -> Option<Vec<String>> {
    let name = match callee {
        Expr::Var(f) => last_segment(f)?,
        _ => call_owner_member(callee).map(|(_, member)| member)?,
    };
    tuple_names_for_name(&name, n)
}

fn tuple_names_for_value(value: &Expr, n: usize) -> Option<Vec<String>> {
    let name = match value {
        Expr::Call(callee, _) => return tuple_names_for(callee, n),
        Expr::MethodCall(_, method, _) => method.clone(),
        _ => return None,
    };
    tuple_names_for_name(&name, n)
}

fn tuple_names_for_name(name: &str, n: usize) -> Option<Vec<String>> {
    let base: &[&str] = match name {
        "pcall" | "xpcall" | "resume" => &["ok", "result"],
        "find" => &["startIndex", "endIndex"],
        "next" => &["key", "value"],
        "gsub" => &["replaced", "count"],
        "GetBoundingBox" => &["cframe", "size"],
        "WorldToScreenPoint" | "WorldToViewportPoint" => &["screenPoint", "onScreen"],
        "ViewportPointToRay" | "ScreenPointToRay" => &["ray"],
        "ToOrientation" | "ToEulerAnglesXYZ" | "ToEulerAnglesYXZ" => &["x", "y", "z"],
        "ToAxisAngle" => &["axis", "angle"],
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
        match s {
            Stmt::Local { names, values } if values.len() == 1 && names.len() >= 2 => {
                if let Some(tuple_names) = tuple_names_for_value(&values[0], names.len()) {
                    for (name, tuple_name) in names.iter().zip(tuple_names.iter()) {
                        if candidates.contains(name) {
                            base_map.insert(name.clone(), tuple_name.clone());
                        }
                    }
                }
            }
            Stmt::Assign { targets, values } if values.len() == 1 && targets.len() >= 2 => {
                if let Some(names) = tuple_names_for_value(&values[0], targets.len()) {
                    for (t, nm) in targets.iter().zip(names.iter()) {
                        if let Expr::Var(v) = t {
                            if candidates.contains(v) {
                                base_map.insert(v.clone(), nm.clone());
                            }
                        }
                    }
                }
            }
            _ => {}
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
                                if let Some(base) = param_name_from_field_key(&f)
                                    .or_else(|| sanitize(&field_to_local_name(&f)))
                                {
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
    let exported_tables = exported_table_candidates(stmts);
    for s in stmts {
        if let Stmt::Return(values) = s {
            if let [Expr::Var(name)] = values.as_slice() {
                if candidates.contains(name) && !base_map.contains_key(name) {
                    if exported_tables.contains(name) {
                        base_map.insert(name.clone(), "module".to_string());
                    } else if let Some([Expr::Table(fields)]) = defs.get(name).map(Vec::as_slice) {
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

fn exported_table_candidates(stmts: &[Stmt]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for stmt in stmts {
        if let Stmt::Assign { targets, values } = stmt {
            if targets.len() == 1 && values.len() == 1 && is_export_value(&values[0]) {
                match &targets[0] {
                    Expr::Field(base, field)
                        if is_module_export_field(field)
                            && matches!(base.as_ref(), Expr::Var(_)) =>
                    {
                        if let Expr::Var(name) = base.as_ref() {
                            names.insert(name.clone());
                        }
                    }
                    Expr::Index(base, key)
                        if matches!(base.as_ref(), Expr::Var(_))
                            && matches!(key.as_ref(), Expr::Str(_)) =>
                    {
                        if let (Expr::Var(name), Expr::Str(lit)) = (base.as_ref(), key.as_ref()) {
                            if is_module_export_field(&strip_quotes(lit)) {
                                names.insert(name.clone());
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        for_each_child_block(stmt, |body| names.extend(exported_table_candidates(body)));
    }
    names
}

fn is_export_value(value: &Expr) -> bool {
    matches!(value, Expr::Closure { .. } | Expr::Table(_))
        || derive_name(value).is_some()
        || name_from_value(value).is_some()
}

fn is_module_export_field(field: &str) -> bool {
    field.chars().any(|c| c.is_ascii_uppercase())
        || matches!(
            field,
            "new" | "init" | "start" | "stop" | "destroy" | "connect" | "disconnect"
        )
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
        Expr::Call(callee, args) => args.iter().all(is_pure) && is_pure_builtin_call(callee),
        Expr::MethodCall(..) | Expr::Raw(_) => false,
    }
}

fn is_pure_builtin_call(callee: &Expr) -> bool {
    let Some((owner, member)) = call_owner_member(callee) else {
        return false;
    };

    match owner.as_str() {
        "Vector2"
        | "Vector3"
        | "CFrame"
        | "Color3"
        | "UDim"
        | "UDim2"
        | "BrickColor"
        | "Ray"
        | "Region3"
        | "Rect"
        | "NumberRange"
        | "NumberSequence"
        | "ColorSequence"
        | "NumberSequenceKeypoint"
        | "ColorSequenceKeypoint"
        | "TweenInfo"
        | "PhysicalProperties"
        | "Axes"
        | "Faces"
        | "CatalogSearchParams"
        | "FloatCurveKey"
        | "RotationCurveKey" => matches!(
            member.as_str(),
            "new"
                | "fromRGB"
                | "fromHSV"
                | "fromHex"
                | "fromScale"
                | "fromOffset"
                | "Angles"
                | "fromAxisAngle"
                | "fromEulerAnglesXYZ"
                | "fromEulerAnglesYXZ"
                | "lookAt"
                | "fromMatrix"
                | "identity"
        ),
        "math" => matches!(
            member.as_str(),
            "abs"
                | "acos"
                | "asin"
                | "atan"
                | "atan2"
                | "ceil"
                | "clamp"
                | "cos"
                | "cosh"
                | "deg"
                | "exp"
                | "floor"
                | "fmod"
                | "frexp"
                | "ldexp"
                | "log"
                | "log10"
                | "max"
                | "min"
                | "modf"
                | "noise"
                | "pow"
                | "rad"
                | "round"
                | "sign"
                | "sin"
                | "sinh"
                | "sqrt"
                | "tan"
                | "tanh"
        ),
        _ => false,
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
            var,
            start,
            limit,
            step,
            body,
        } => {
            if let Some(new) = map.get(var) {
                *var = new.clone();
            }
            rename_expr(start, map);
            rename_expr(limit, map);
            if let Some(s) = step {
                rename_expr(s, map);
            }
            apply_rename(body, map);
        }
        Stmt::GenericFor { vars, exprs, body } => {
            for var in vars.iter_mut() {
                if let Some(new) = map.get(var) {
                    *var = new.clone();
                }
            }
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
        match s {
            Stmt::Local { names, values } => {
                for (name, value) in names.iter().zip(values.iter()) {
                    if candidates.contains(name) {
                        out.entry(name.clone()).or_default().push(value.clone());
                    }
                }
            }
            Stmt::Assign { targets, values } => {
                if let (Some(Expr::Var(name)), Some(value)) = (targets.first(), values.first()) {
                    if targets.len() == 1 && candidates.contains(name) {
                        out.entry(name.clone()).or_default().push(value.clone());
                    }
                }
            }
            _ => {}
        }
        // Definitions only appear at top level in the current emitter, but recurse so this
        // keeps working once control flow is structured.
        for_each_child_block(s, |body| collect_all_defs(body, candidates, out));
    }
}

/// Whether `e` reads the variable `name` anywhere.
fn expr_references(e: &Expr, name: &str) -> bool {
    let mut set = BTreeSet::new();
    collect_used_in_expr(e, &mut set);
    set.contains(name)
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
/// Classification of a single definition expression, for naming a variable from its WHOLE
/// lifetime (every value ever assigned to it) instead of one definition. See [`lifetime_name`].
#[derive(Debug, Clone, PartialEq, Eq)]
enum TypeTag {
    /// A constructor/lookup that yields a known Roblox class: `Instance.new("Weld")`,
    /// `FindFirstChildOfClass("Humanoid")`. Carries the class name.
    Class(String),
    /// A part-typed source whose identity differs by site — a part property (`PrimaryPart`,
    /// `from_property = true`) or a child lookup (`FindFirstChild("Middle")`,
    /// `from_property = false`). Carries the field/literal so divergence can be detected.
    PartRole { name: String, from_property: bool },
    /// Some other derivable value; its presence means the lifetime is not purely class- or
    /// part-typed, so no family/role name is produced (the variable stays generic).
    Other,
    /// Literals, `nil`, and self/synthetic re-aliases: ignored — they never block agreement
    /// between the real definitions, nor invent a name on their own.
    Ignore,
}

/// The class string of an `Instance.new("Class")` call, if that is what `callee`/`args` are.
fn instance_new_class(callee: &Expr, args: &[Expr]) -> Option<String> {
    let (owner, member) = call_owner_member(callee)?;
    if owner == "Instance" && member == "new" {
        if let Some(Expr::Str(lit)) = args.first() {
            return Some(strip_quotes(lit));
        }
    }
    None
}

/// The class string of a class-filtered child/ancestor lookup, if `method` is one.
fn find_by_class_name(method: &str, args: &[Expr]) -> Option<String> {
    if matches!(
        method,
        "FindFirstChildOfClass"
            | "FindFirstChildWhichIsA"
            | "FindFirstAncestorOfClass"
            | "FindFirstAncestorWhichIsA"
    ) {
        if let Some(Expr::Str(lit)) = args.first() {
            return Some(strip_quotes(lit));
        }
    }
    None
}

/// Instance properties that read a BasePart, so a variable fed by several of them (or by one of
/// them plus a child lookup) is recognised as "the main part" rather than any single property.
fn is_part_field(field: &str) -> bool {
    matches!(
        field,
        "PrimaryPart"
            | "HumanoidRootPart"
            | "RootPart"
            | "Head"
            | "Torso"
            | "UpperTorso"
            | "LowerTorso"
            | "Handle"
            | "Hitbox"
    )
}

/// Child names that denote a part, so `FindFirstChild("Middle")` anchors a variable as part-typed
/// even with no sibling part property.
fn is_part_ish_name(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "middle"
            | "handle"
            | "root"
            | "rootpart"
            | "humanoidrootpart"
            | "torso"
            | "head"
            | "hitbox"
            | "base"
            | "body"
            | "center"
            | "trunk"
            | "core"
            | "primarypart"
            | "mainpart"
    )
}

/// The generic local name shared by a family of related Roblox classes — used when one variable
/// holds MORE THAN ONE class of the family over its lifetime (a `Motor6D` in one branch and a
/// `Weld` in another are both "joint"). `None` for classes with no good shared name, so such a
/// variable keeps its specific name (single class) or stays generic rather than gaining a vague
/// one. Kept deliberately separate from [`class_name_hint`], which gives the single-class name.
fn class_family(class: &str) -> Option<&'static str> {
    Some(match class {
        "Weld" | "WeldConstraint" | "ManualWeld" | "Motor6D" | "Motor" | "Snap" | "Glue" => "joint",
        "HingeConstraint" | "BallSocketConstraint" | "PrismaticConstraint"
        | "CylindricalConstraint" | "SpringConstraint" | "RodConstraint" | "RopeConstraint"
        | "UniversalConstraint" | "NoCollisionConstraint" | "Torque" | "AlignPosition"
        | "AlignOrientation" | "LinearVelocity" | "AngularVelocity" | "VectorForce"
        | "LineForce" | "Plane" => "constraint",
        "BodyVelocity" | "BodyForce" | "BodyGyro" | "BodyPosition" | "BodyThrust"
        | "BodyAngularVelocity" | "RocketPropulsion" => "mover",
        "Part" | "BasePart" | "MeshPart" | "UnionOperation" | "NegateOperation" | "WedgePart"
        | "CornerWedgePart" | "TrussPart" | "SpawnLocation" | "Seat" | "VehicleSeat"
        | "SkateboardPlatform" => "part",
        "SpecialMesh" | "BlockMesh" | "CylinderMesh" | "FileMesh" | "CharacterMesh" => "mesh",
        "StringValue" | "IntValue" | "NumberValue" | "BoolValue" | "ObjectValue" | "CFrameValue"
        | "Vector3Value" | "Color3Value" | "BrickColorValue" | "RayValue" => "value",
        "Frame" | "ScrollingFrame" | "ViewportFrame" | "CanvasGroup" => "frame",
        "TextLabel" | "ImageLabel" => "label",
        "TextButton" | "ImageButton" => "button",
        "ScreenGui" | "SurfaceGui" | "BillboardGui" => "gui",
        "UIListLayout" | "UIGridLayout" | "UITableLayout" | "UIPageLayout" | "UIPadding"
        | "UICorner" | "UIStroke" | "UIScale" | "UIGradient" | "UIAspectRatioConstraint"
        | "UISizeConstraint" | "UITextSizeConstraint" => "uiElement",
        "RemoteEvent" | "RemoteFunction" | "UnreliableRemoteEvent" => "remote",
        "BindableEvent" | "BindableFunction" => "bindable",
        "ParticleEmitter" | "Beam" | "Trail" | "Smoke" | "Fire" | "Sparkles" | "Explosion" => {
            "effect"
        }
        "PointLight" | "SpotLight" | "SurfaceLight" => "light",
        "ColorCorrectionEffect" | "BloomEffect" | "BlurEffect" | "SunRaysEffect"
        | "DepthOfFieldEffect" => "postEffect",
        "Sound" | "SoundGroup" => "sound",
        "EqualizerSoundEffect" | "EchoSoundEffect" | "ReverbSoundEffect" | "DistortionSoundEffect"
        | "PitchShiftSoundEffect" | "ChorusSoundEffect" | "CompressorSoundEffect"
        | "FlangeSoundEffect" | "TremoloSoundEffect" => "soundEffect",
        "Animation" | "AnimationTrack" | "Animator" | "AnimationController" => "animation",
        "Script" | "LocalScript" | "ModuleScript" | "BaseScript" => "script",
        "Decal" | "Texture" | "SurfaceAppearance" => "texture",
        "Attachment" | "Bone" => "attachment",
        "Accessory" | "Accoutrement" | "Shirt" | "Pants" | "ShirtGraphic" | "Hat" => "accessory",
        "ProximityPrompt" | "ClickDetector" | "DragDetector" => "interaction",
        "Model" | "WorldModel" | "Actor" => "model",
        _ => return None,
    })
}

/// Classify one definition expression for lifetime-aware naming.
fn def_type_tag(e: &Expr) -> TypeTag {
    match e {
        Expr::Nil | Expr::Bool(_) | Expr::Num(_) | Expr::Str(_) | Expr::Vector(_) => TypeTag::Ignore,
        Expr::Var(name) if is_synthetic(name) || is_parameter(name) => TypeTag::Ignore,
        Expr::Call(callee, args) => match instance_new_class(callee, args) {
            Some(class) => TypeTag::Class(class),
            None => TypeTag::Other,
        },
        Expr::MethodCall(_, method, args) => {
            if let Some(class) = find_by_class_name(method, args) {
                TypeTag::Class(class)
            } else if matches!(method.as_str(), "FindFirstChild" | "WaitForChild") {
                match args.first() {
                    Some(Expr::Str(lit)) => TypeTag::PartRole {
                        name: strip_quotes(lit),
                        from_property: false,
                    },
                    _ => TypeTag::Other,
                }
            } else {
                TypeTag::Other
            }
        }
        Expr::Field(_, field) if is_part_field(field) => TypeTag::PartRole {
            name: field.clone(),
            from_property: true,
        },
        _ => TypeTag::Other,
    }
}

/// Derive ONE name for a variable from its WHOLE lifetime (`defs` — every value ever assigned to
/// it), for variables whose definitions disagree on a single specific name but still share a
/// coherent type:
/// - all definitions construct the SAME class -> that class's specific name;
/// - definitions construct DIFFERENT classes of one family -> the family name
///   (`Motor6D` + `Weld` -> `"joint"`);
/// - the variable is part-typed but reached different ways -> `"mainPart"`
///   (`instance.PrimaryPart` in one branch, `instance:FindFirstChild("Middle")` in another).
///
/// Returns `None` when the definitions don't cohere, leaving the variable generic. Renaming a
/// local is always semantics-preserving here, so a family/role name is safe even when imperfect.
fn lifetime_name(defs: &[Expr]) -> Option<String> {
    let tags: Vec<TypeTag> = defs
        .iter()
        .map(def_type_tag)
        .filter(|t| *t != TypeTag::Ignore)
        .collect();
    if tags.is_empty() {
        return None;
    }

    let classes: BTreeSet<&str> = tags
        .iter()
        .filter_map(|t| match t {
            TypeTag::Class(c) => Some(c.as_str()),
            _ => None,
        })
        .collect();
    // A genuinely unrecognised value (a call/field that isn't an instance source) means the
    // register's lifetime is incoherent; stay conservative and leave it generic.
    let has_other = tags.iter().any(|t| matches!(t, TypeTag::Other));

    // Some definition constructs/looks up an instance of a known class. Child lookups
    // (`FindFirstChild`/`WaitForChild`) and part properties are instance-producing and compatible
    // with a constructor, so they don't block class naming — this is exactly the ubiquitous
    // `parent:FindFirstChild("X") or Instance.new("Y")` get-or-create idiom: the variable holds an
    // instance of the constructed class either way. Same class -> specific name; one family ->
    // family name (`Motor6D` + `Weld` -> "joint").
    if !classes.is_empty() && !has_other {
        if classes.len() == 1 {
            return class_name_hint(classes.iter().copied().next().unwrap());
        }
        let families: Option<BTreeSet<&str>> = classes.iter().copied().map(class_family).collect();
        return match families {
            Some(fams) if fams.len() == 1 => Some(fams.into_iter().next().unwrap().to_string()),
            _ => None,
        };
    }

    // No class constructor: a part-typed variable located in divergent ways -> "mainPart" (neither
    // "primaryPart", which is only the first assignment, nor "middle", only the second). Requires
    // at least one unambiguous part anchor, then two or more distinct sources.
    let part_roles: Vec<(&str, bool)> = tags
        .iter()
        .filter_map(|t| match t {
            TypeTag::PartRole { name, from_property } => Some((name.as_str(), *from_property)),
            _ => None,
        })
        .collect();
    if classes.is_empty() && !has_other && !part_roles.is_empty() {
        let has_anchor = part_roles
            .iter()
            .any(|(name, from_property)| *from_property || is_part_ish_name(name));
        let sources: BTreeSet<&str> = part_roles.iter().map(|(name, _)| *name).collect();
        if has_anchor && sources.len() >= 2 {
            return Some("mainPart".to_string());
        }
    }

    None
}

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
            // game.ReplicatedStorage/game.Players are service aliases and read best as services.
            if is_var(base, "game") && roblox_service_name(field) {
                return sanitize(field);
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
        Expr::Table(fields) => table_collection_name(fields),
        // Boolean-shaped expressions stored in a local: nil checks, emptiness checks.
        Expr::Binary("and", a, b) => derive_short_circuit_name("and", a, b),
        Expr::Binary("or", a, b) => derive_short_circuit_name("or", a, b),
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
        "Size" => "size",
        "Color" => "color",
        "Health" => "health",
        "MaxHealth" => "maxHealth",
        "WalkSpeed" => "walkSpeed",
        "JumpPower" => "jumpPower",
        "JumpHeight" => "jumpHeight",
        "MoveDirection" => "moveDirection",
        "Transparency" => "transparency",
        "Brightness" => "brightness",
        "Volume" => "volume",
        "Text" => "text",
        "Value" => "value",
        "Velocity" | "AssemblyLinearVelocity" => "velocity",
        "Parent" => "parent",
        _ => return None,
    })
}

fn roblox_service_name(field: &str) -> bool {
    matches!(
        field,
        "Players"
            | "ReplicatedStorage"
            | "ServerStorage"
            | "ServerScriptService"
            | "StarterGui"
            | "StarterPack"
            | "StarterPlayer"
            | "RunService"
            | "TweenService"
            | "Debris"
            | "Lighting"
            | "Workspace"
            | "CollectionService"
            | "UserInputService"
            | "ContextActionService"
            | "HttpService"
            | "TeleportService"
            | "MarketplaceService"
            | "DataStoreService"
            | "MemoryStoreService"
            | "MessagingService"
            | "BadgeService"
            | "PhysicsService"
            | "PathfindingService"
            | "GuiService"
            | "InsertService"
            | "LogService"
            | "PolicyService"
            | "ProximityPromptService"
            | "AnalyticsService"
            | "ReplicatedFirst"
            | "Teams"
            | "VoiceChatService"
            | "LocalizationService"
            | "TextService"
            | "TestService"
            | "TextChatService"
            | "SoundService"
            | "Chat"
    )
}

/// Name a boolean-valued local after the shape of its condition.
fn derive_bool_name(op: &str, a: &Expr, b: &Expr) -> Option<String> {
    if let Some(name) = positive_bool_compare_name(op, a, b) {
        return Some(name);
    }

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

fn derive_short_circuit_name(op: &str, a: &Expr, b: &Expr) -> Option<String> {
    let yielded = match op {
        "and" => b,
        "or" => a,
        _ => return None,
    };
    derive_name(yielded).or_else(|| name_from_value(yielded))
}

fn positive_bool_compare_name(op: &str, a: &Expr, b: &Expr) -> Option<String> {
    let (subject, literal) = match (bool_lit(a), bool_lit(b)) {
        (None, Some(value)) => (a, value),
        (Some(value), None) => (b, value),
        _ => return None,
    };
    let positive = match op {
        "==" => true,
        "~=" => false,
        _ => return None,
    };
    if positive != literal {
        return None;
    }
    boolean_subject_name(subject)
}

fn bool_lit(expr: &Expr) -> Option<bool> {
    match expr {
        Expr::Bool(value) => Some(*value),
        _ => None,
    }
}

fn boolean_subject_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Field(_, field) => sanitize(&field_to_local_name(field.trim_start_matches('_'))),
        Expr::Index(_, key) => match key.as_ref() {
            Expr::Str(lit) => sanitize(&field_to_local_name(&strip_quotes(lit))),
            _ => None,
        },
        Expr::MethodCall(_, method, args) if method == "GetAttribute" => match args.first() {
            Some(Expr::Str(lit)) => sanitize(&field_to_local_name(&strip_quotes(lit))),
            _ => None,
        },
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
            "pairs" => return Some("iterator".to_string()),
            "ipairs" => return Some("iterator".to_string()),
            _ => {}
        }
    }

    // owner.member style calls (field access or dotted import).
    if let Some((owner, member)) = call_owner_member(callee) {
        // Instance.new("Class") -> lowercased class name.
        if owner == "Instance" && member == "new" {
            if let Some(Expr::Str(lit)) = args.first() {
                let class_name = strip_quotes(lit);
                return class_name_hint(&class_name)
                    .or_else(|| sanitize(&lower_first(&class_name)));
            }
        }
        if member == "GetService" {
            return service_name_arg(args);
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
            ("math", "clamp") => return Some("clamped".to_string()),
            ("math", "min") => return Some("min".to_string()),
            ("math", "max") => return Some("max".to_string()),
            ("math", "floor") | ("math", "ceil") | ("math", "round") => {
                return Some("rounded".to_string())
            }
            ("math", "sqrt") => return Some("root".to_string()),
            ("math", "abs") => return Some("absolute".to_string()),
            ("math", "sin") | ("math", "cos") | ("math", "tan") => {
                return Some("angleValue".to_string())
            }
            ("debug", "traceback") => return Some("traceback".to_string()),
            ("os", "time") | ("os", "clock") => return Some("now".to_string()),
            ("os", "date") => return Some("date".to_string()),
            ("task", "wait") => return Some("dt".to_string()),
            ("task", "spawn") | ("task", "defer") | ("task", "delay") => {
                return Some("thread".to_string())
            }
            ("DateTime", "now")
            | ("DateTime", "fromUnixTimestamp")
            | ("DateTime", "fromUnixTimestampMillis")
            | ("DateTime", "fromUniversalTime")
            | ("DateTime", "fromLocalTime")
            | ("DateTime", "fromIsoDate") => return Some("dateTime".to_string()),
            ("Random", "new") => return Some("random".to_string()),
            ("RaycastParams", "new") => return Some("raycastParams".to_string()),
            ("OverlapParams", "new") => return Some("overlapParams".to_string()),
            ("NumberSequenceKeypoint", "new") => return Some("keypoint".to_string()),
            ("ColorSequenceKeypoint", "new") => return Some("keypoint".to_string()),
            ("coroutine", "create") => return Some("thread".to_string()),
            ("coroutine", "wrap") => return Some("wrapped".to_string()),
            ("buffer", "create") | ("buffer", "fromstring") => return Some("buffer".to_string()),
            ("string", "format") => return Some("formatted".to_string()),
            ("string", "gsub") => return Some("replaced".to_string()),
            ("string", "split") => return Some("parts".to_string()),
            ("string", "rep") => return Some("repeated".to_string()),
            ("string", "sub") => return Some("substring".to_string()),
            ("utf8", "len") => return Some("length".to_string()),
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
    if method == "Create" && receiver_mentions(recv, "tween") {
        return Some("tween".to_string());
    }

    match method {
        "GetService" => service_name_arg(args),
        // Child lookups by literal name: keep the child name verbatim (PascalCase reads well).
        "FindFirstChild" | "WaitForChild" | "FindFirstAncestor" => {
            args.first().and_then(name_from_value)
        }
        // Child lookups by class: name after the class, as an instance.
        "FindFirstChildOfClass"
        | "FindFirstChildWhichIsA"
        | "FindFirstAncestorOfClass"
        | "FindFirstAncestorWhichIsA" => match args.first() {
            Some(Expr::Str(lit)) => {
                let class_name = strip_quotes(lit);
                class_name_hint(&class_name).or_else(|| sanitize(&lower_first(&class_name)))
            }
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
        "LoadAnimation" => Some("track".to_string()),
        "GetMouse" => Some("mouse".to_string()),
        "GetMouseLocation" => Some("mouseLocation".to_string()),
        "GetMouseDelta" => Some("mouseDelta".to_string()),
        "GetFullName" => Some("fullName".to_string()),
        "GetDebugId" => Some("debugId".to_string()),
        "GetBoundingBox" => Some("boundingBox".to_string()),
        "GetTouchingParts" | "GetPartsInPart" | "GetPartBoundsInBox" | "GetPartBoundsInRadius" => {
            Some("parts".to_string())
        }
        "UserOwnsGamePassAsync" => Some("ownsGamePass".to_string()),
        "GetUserIdFromNameAsync" => Some("userId".to_string()),
        "GetNameFromUserIdAsync" => Some("username".to_string()),
        "GetRankInGroup" => Some("rank".to_string()),
        "GetRoleInGroup" => Some("role".to_string()),
        "IsInGroup" => Some("inGroup".to_string()),
        "GetProductInfo" => Some("productInfo".to_string()),
        "GetFriendsAsync" => Some("friendsPages".to_string()),
        "GetServerTimeNow" => Some("serverTime".to_string()),
        "CreatePath" => Some("path".to_string()),
        "GetWaypoints" => Some("waypoints".to_string()),
        "GetTagged" => Some("tagged".to_string()),
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

fn receiver_mentions(recv: &Expr, needle: &str) -> bool {
    trailing_noun(recv)
        .map(|name| name.to_ascii_lowercase().contains(needle))
        .unwrap_or(false)
}

fn service_name_arg(args: &[Expr]) -> Option<String> {
    let arg = if matches!(args.first(), Some(Expr::Var(name)) if name == "game") {
        args.get(1)
    } else {
        args.first()
    };
    arg.and_then(name_from_value)
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
    if let Expr::MethodCall(_, method, args) = coll_expr {
        if method == "GetTagged" {
            if let Some(Expr::Str(lit)) = args.first() {
                return sanitize(&singular(&field_to_local_name(&strip_quotes(lit))));
            }
            return Some("tagged".to_string());
        }
    }
    collection_name(coll_expr).map(|c| singular(&c))
}

fn singular(s: &str) -> String {
    singularize(s).unwrap_or_else(|| s.to_string())
}

fn singularize(name: &str) -> Option<String> {
    if name == "children" {
        return Some("child".to_string());
    }
    if !name.is_ascii() {
        return None;
    }

    let lower = name.to_ascii_lowercase();
    const NON_PLURAL: &[&str] = &[
        "status", "data", "address", "class", "process", "bonus", "physics", "analysis", "axis",
        "props", "series", "species", "news", "progress", "pass", "mass", "boss", "loss", "glass",
        "lens", "gas", "basis", "access", "success", "focus", "bias", "canvas", "radius", "virus",
        "index",
    ];
    if NON_PLURAL.contains(&lower.as_str()) {
        return None;
    }

    let singular = if let Some(stem) = name.strip_suffix("ies") {
        let prev = stem.chars().last()?;
        if stem.len() < 3 || "aeiouAEIOU".contains(prev) {
            return None;
        }
        format!("{stem}y")
    } else if lower.ends_with("ses")
        || lower.ends_with("xes")
        || lower.ends_with("zes")
        || lower.ends_with("ches")
        || lower.ends_with("shes")
    {
        name[..name.len() - 2].to_string()
    } else if lower.ends_with("oes") {
        return None;
    } else if let Some(stem) = name.strip_suffix('s') {
        let bytes = name.as_bytes();
        if name.len() < 2 {
            return None;
        }
        let prev = bytes[name.len() - 2].to_ascii_lowercase();
        if matches!(prev, b's' | b'i' | b'u') {
            return None;
        }
        stem.to_string()
    } else {
        return None;
    };

    if singular.eq_ignore_ascii_case(name) || singular.len() < 2 {
        return None;
    }
    sanitize(&singular)
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
        "NumberRange" => "numberRange",
        "NumberSequence" => "numberSequence",
        "ColorSequence" => "colorSequence",
        "NumberSequenceKeypoint" | "ColorSequenceKeypoint" => "keypoint",
        "PathWaypoint" => "waypoint",
        "PhysicalProperties" => "physicalProperties",
        "Axes" => "axes",
        "Faces" => "faces",
        "CatalogSearchParams" => "catalogSearchParams",
        "FloatCurveKey" => "key",
        "RotationCurveKey" => "key",
        "Secret" => "secret",
        _ => return None,
    };
    Some(name.to_string())
}

fn class_name_hint(class_name: &str) -> Option<String> {
    Some(
        match class_name {
            "BasePart" | "Part" | "MeshPart" | "UnionOperation" => "part",
            "Script" | "LocalScript" | "ModuleScript" | "BaseScript" => "script",
            "Model" | "WorldModel" => "model",
            "Folder" => "folder",
            "Attachment" => "attachment",
            "GuiButton" | "TextButton" | "ImageButton" => "button",
            "GuiObject" => "guiObject",
            "Frame" | "ScrollingFrame" | "ViewportFrame" => "frame",
            "TextLabel" => "label",
            "TextBox" => "textBox",
            "ImageLabel" => "image",
            "ScreenGui" => "screenGui",
            "SurfaceGui" => "surfaceGui",
            "BillboardGui" => "billboardGui",
            "UIListLayout" => "listLayout",
            "UIGridLayout" => "gridLayout",
            "UITableLayout" => "tableLayout",
            "UIPadding" => "padding",
            "UIStroke" => "stroke",
            "UICorner" => "corner",
            "UIScale" => "scale",
            "UIGradient" => "gradient",
            "ParticleEmitter" => "emitter",
            "Beam" => "beam",
            "Trail" => "trail",
            "PointLight" | "SpotLight" | "SurfaceLight" => "light",
            "RemoteEvent" => "remoteEvent",
            "RemoteFunction" => "remoteFunction",
            "BindableEvent" => "bindableEvent",
            "BindableFunction" => "bindableFunction",
            "Humanoid" => "humanoid",
            "Animator" => "animator",
            "Animation" => "animation",
            "AnimationController" => "animationController",
            "AnimationTrack" => "track",
            "Sound" => "sound",
            "SoundGroup" => "soundGroup",
            "Tool" => "tool",
            "Backpack" => "backpack",
            "Camera" => "camera",
            "Weld" | "WeldConstraint" | "ManualWeld" => "weld",
            "Motor6D" => "motor",
            "ProximityPrompt" => "prompt",
            "ClickDetector" => "clickDetector",
            "Decal" | "Texture" => "texture",
            "SurfaceAppearance" => "surfaceAppearance",
            "BodyVelocity" | "LinearVelocity" => "velocity",
            "BodyGyro" | "AlignOrientation" => "alignOrientation",
            "BodyPosition" | "AlignPosition" => "alignPosition",
            "VectorForce" => "force",
            "ObjectValue" => "objectValue",
            "StringValue" => "stringValue",
            "NumberValue" | "IntValue" => "numberValue",
            "BoolValue" => "boolValue",
            "RaycastParams" => "raycastParams",
            "OverlapParams" => "overlapParams",
            other => return sanitize(&lower_first(other)),
        }
        .to_string(),
    )
}

fn table_collection_name(fields: &[TableField]) -> Option<String> {
    let names = fields
        .iter()
        .filter_map(|field| match field {
            TableField::Item(value) => name_from_value(value),
            _ => None,
        })
        .collect::<Vec<_>>();
    if names.len() < 2 {
        return None;
    }

    let known_target_folders = names
        .iter()
        .filter(|name| {
            matches!(
                name.to_ascii_lowercase().as_str(),
                "npcs"
                    | "debris"
                    | "animals"
                    | "characters"
                    | "farm"
                    | "farms"
                    | "plots"
                    | "plants"
                    | "clouds"
                    | "folders"
            )
        })
        .count();
    if known_target_folders >= 2 {
        return Some("targetFolders".to_string());
    }
    if names
        .iter()
        .any(|name| name.to_ascii_lowercase().contains("folder"))
    {
        return Some("folders".to_string());
    }
    None
}

fn param_name_from_field_key(key: &str) -> Option<String> {
    const GENERIC_FIELD_KEYS: &[&str] = &[
        "value", "val", "v", "data", "item", "key", "index", "self", "type", "result", "arg", "n",
    ];
    let sanitized = sanitize(&field_to_local_name(key.trim_start_matches('_')))?;
    let trimmed = sanitized.trim_end_matches(|c: char| c.is_ascii_digit());
    let name = if trimmed.len() >= 2 {
        trimmed.to_string()
    } else {
        sanitized
    };
    if name.len() < 2 || GENERIC_FIELD_KEYS.contains(&name.as_str()) {
        return None;
    }
    Some(name)
}

fn callback_field_name(key: &str) -> Option<String> {
    let sanitized = sanitize(&field_to_local_name(key.trim_start_matches('_')))?;
    if sanitized == "callback" || sanitized == "handler" {
        return Some(sanitized);
    }
    if sanitized.starts_with("on")
        && sanitized
            .chars()
            .nth(2)
            .is_some_and(|c| c.is_ascii_uppercase())
    {
        return Some(sanitized);
    }
    if sanitized.starts_with("set")
        && sanitized
            .chars()
            .nth(3)
            .is_some_and(|c| c.is_ascii_uppercase())
    {
        return Some(sanitized);
    }
    None
}

fn callback_arg_index(callee: &Expr) -> Option<usize> {
    if let Some((owner, member)) = call_owner_member(callee) {
        match (owner.as_str(), member.as_str()) {
            ("task", "spawn" | "defer") | ("coroutine", "wrap" | "create") => Some(0),
            ("task", "delay") => Some(1),
            ("Promise", "new" | "try" | "defer") => Some(0),
            _ => None,
        }
    } else {
        None
    }
}

fn type_guard_name<'a>(a: &'a Expr, b: &'a Expr) -> Option<(&'a str, &'a str)> {
    if let (Some(name), Some(type_name)) = (typeof_call_var(a), string_literal_value(b)) {
        return Some((name, type_name));
    }
    if let (Some(name), Some(type_name)) = (typeof_call_var(b), string_literal_value(a)) {
        return Some((name, type_name));
    }
    None
}

fn typeof_call_var(expr: &Expr) -> Option<&str> {
    let Expr::Call(callee, args) = expr else {
        return None;
    };
    let Expr::Var(name) = callee.as_ref() else {
        return None;
    };
    if name != "typeof" && name != "type" || args.len() != 1 {
        return None;
    }
    match args.first() {
        Some(Expr::Var(var)) => Some(var),
        _ => None,
    }
}

fn string_literal_value(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Str(lit) => Some(lit.trim_matches('"').trim_matches('\'')),
        _ => None,
    }
}

fn type_name_hint(type_name: &str) -> Option<&'static str> {
    match type_name {
        "string" => Some("text"),
        "number" => Some("amount"),
        "boolean" => Some("enabled"),
        "Instance" => Some("instance"),
        "Vector3" | "Vector2" => Some("vector"),
        "CFrame" => Some("cframe"),
        "function" => Some("callback"),
        "table" => Some("data"),
        _ => None,
    }
}

/// A noun extracted from a value used as a path/key (require arg, service name, child name).
fn name_from_value(e: &Expr) -> Option<String> {
    match e {
        Expr::Str(lit) => last_segment(&strip_quotes(lit)).and_then(|s| sanitize(&s)),
        Expr::Var(path) => {
            let segment = last_segment(path)?;
            if is_synthetic(&segment) || is_parameter(&segment) {
                None
            } else {
                sanitize(&segment)
            }
        }
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
    if let Some(rest) = strip_verb_prefix(f) {
        return sanitize(&lower_first(rest));
    }
    sanitize(&lower_first(f))
}

fn strip_verb_prefix(name: &str) -> Option<&str> {
    fn noun_like(rest: &str) -> Option<&str> {
        if rest.chars().next().is_some_and(|c| c.is_ascii_uppercase())
            && !starts_with_connective(rest)
        {
            Some(rest)
        } else {
            None
        }
    }

    const COMPOUND: &[&str] = &["getOr", "findOr", "getAnd", "findAnd"];
    const SECOND_VERBS: &[&str] = &["Create", "Make", "Build", "Get", "Find", "Spawn"];
    for compound in COMPOUND {
        if let Some(rest) = name.strip_prefix(compound) {
            if !rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                continue;
            }
            for verb in SECOND_VERBS {
                if let Some(tail) = rest.strip_prefix(verb) {
                    return noun_like(tail);
                }
            }
            return noun_like(rest);
        }
    }

    const VERBS: &[&str] = &[
        "Get",
        "get",
        "Find",
        "find",
        "Create",
        "create",
        "Make",
        "make",
        "New",
        "Build",
        "build",
        "Compute",
        "compute",
        "Load",
        "load",
        "Fetch",
        "fetch",
        "Ensure",
        "ensure",
        "Resolve",
        "resolve",
        "Clone",
        "clone",
        "Normalize",
        "normalize",
        "Spawn",
        "spawn",
    ];
    for verb in VERBS {
        if let Some(rest) = name.strip_prefix(verb) {
            if rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                return noun_like(rest);
            }
        }
    }
    None
}

fn starts_with_connective(rest: &str) -> bool {
    const CONNECTIVES: &[&str] = &[
        "and", "or", "from", "to", "with", "by", "of", "in", "for", "on", "into", "out", "off",
        "via", "at", "as", "the", "a",
    ];
    let mut chars = rest.chars();
    let mut word = String::new();
    if let Some(first) = chars.next() {
        word.push(first.to_ascii_lowercase());
    }
    for c in chars {
        if c.is_ascii_uppercase() {
            break;
        }
        word.push(c.to_ascii_lowercase());
    }
    CONNECTIVES.contains(&word.as_str())
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
            // Non-printable / non-ASCII: emit a numeric escape, zero-padded to 3 digits. Luau
            // reads up to 3 digits for `\ddd`, so an unpadded short escape (`\26`) followed by a
            // literal digit (`0`) would be misread as one escape (`\260`) — which exceeds 255 and
            // is rejected as a malformed escape sequence. `\026` is always exactly 3 digits.
            _ => out.push_str(&format!("\\{b:03}")),
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
    fn pure_builtin_constructors_can_be_inlined_safely() {
        let color = Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Var("Color3".into())),
                "fromRGB".into(),
            )),
            vec![
                Expr::Num("1".into()),
                Expr::Num("2".into()),
                Expr::Num("3".into()),
            ],
        );
        assert!(is_pure(&color));

        let instance = Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Var("Instance".into())),
                "new".into(),
            )),
            vec![s("Part")],
        );
        assert!(!is_pure(&instance));
    }

    #[test]
    fn conflicting_reused_register_defs_do_not_get_one_misleading_name() {
        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("v0".into())],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("Reference".into())),
                    "addToReplicatedStorage".into(),
                )],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v0".into())],
                values: vec![call("require", vec![Expr::Var("goodSignal".into())])],
            },
            Stmt::Call(Expr::Call(Box::new(Expr::Var("v0".into())), Vec::new())),
        ];

        let map = smart_rename(&stmts, &[String::from("v0")], false);
        assert!(!map.contains_key("v0"), "{map:?}");
    }

    #[test]
    fn derives_tovek_style_value_names() {
        let guarded_lookup = Expr::Binary(
            "and",
            Box::new(Expr::Var("folder".into())),
            Box::new(Expr::MethodCall(
                Box::new(Expr::Var("folder".into())),
                "FindFirstChild".into(),
                vec![s("Client")],
            )),
        );
        assert_eq!(derive_name(&guarded_lookup).as_deref(), Some("Client"));

        let fallback = Expr::Binary(
            "or",
            Box::new(Expr::Field(
                Box::new(Expr::Var("player".into())),
                "Character".into(),
            )),
            Box::new(Expr::MethodCall(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("player".into())),
                    "CharacterAdded".into(),
                )),
                "Wait".into(),
                vec![],
            )),
        );
        assert_eq!(derive_name(&fallback).as_deref(), Some("character"));

        let enabled = Expr::Binary(
            "==",
            Box::new(Expr::Field(
                Box::new(Expr::Var("config".into())),
                "Enabled".into(),
            )),
            Box::new(Expr::Bool(true)),
        );
        assert_eq!(derive_name(&enabled).as_deref(), Some("enabled"));

        let planted = Expr::Binary(
            "~=",
            Box::new(Expr::MethodCall(
                Box::new(Expr::Var("plot".into())),
                "GetAttribute".into(),
                vec![s("IsPlanted")],
            )),
            Box::new(Expr::Bool(false)),
        );
        assert_eq!(derive_name(&planted).as_deref(), Some("isPlanted"));

        let not_favorite = Expr::Binary(
            "==",
            Box::new(Expr::Field(
                Box::new(Expr::Var("item".into())),
                "Favorite".into(),
            )),
            Box::new(Expr::Bool(false)),
        );
        assert_eq!(derive_name(&not_favorite), None);
    }

    #[test]
    fn derives_class_and_collection_names() {
        let text_button = Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Var("Instance".into())),
                "new".into(),
            )),
            vec![s("TextButton")],
        );
        assert_eq!(derive_name(&text_button).as_deref(), Some("button"));

        let base_part = Expr::MethodCall(
            Box::new(Expr::Var("model".into())),
            "FindFirstChildWhichIsA".into(),
            vec![s("BasePart")],
        );
        assert_eq!(derive_name(&base_part).as_deref(), Some("part"));

        let target_folders = Expr::Table(vec![
            TableField::Item(Expr::Field(
                Box::new(Expr::Var("workspace".into())),
                "NPCs".into(),
            )),
            TableField::Item(Expr::Field(
                Box::new(Expr::Var("workspace".into())),
                "Debris".into(),
            )),
        ]);
        assert_eq!(
            derive_name(&target_folders).as_deref(),
            Some("targetFolders")
        );
    }

    #[test]
    fn strips_more_factory_verbs_and_keeps_plural_words_safe() {
        assert_eq!(
            derive_name(&call("getOrCreateButton", vec![])).as_deref(),
            Some("button")
        );
        assert_eq!(
            derive_name(&call("ensureFolder", vec![])).as_deref(),
            Some("folder")
        );
        assert_eq!(
            derive_name(&call("cloneFromNode", vec![])).as_deref(),
            Some("cloneFromNode")
        );
        assert_eq!(singular("buttons"), "button");
        assert_eq!(singular("entries"), "entry");
        assert_eq!(singular("status"), "status");
        assert_eq!(singular("classes"), "class");
    }

    #[test]
    fn field_sink_and_type_guard_hints_name_parameters() {
        let stmts = vec![Stmt::Assign {
            targets: vec![Expr::Field(
                Box::new(Expr::Var("weld".into())),
                "Part0".into(),
            )],
            values: vec![Expr::Var("p0".into())],
        }];
        let map = smart_rename(&stmts, &[], false);
        assert_eq!(map.get("p0").map(String::as_str), Some("part"));

        let stmts = vec![Stmt::If {
            cond: Expr::Binary(
                "==",
                Box::new(call("typeof", vec![Expr::Var("p1".into())])),
                Box::new(s("string")),
            ),
            then_body: vec![Stmt::Return(vec![Expr::Var("p1".into())])],
            else_body: Vec::new(),
        }];
        let map = smart_rename(&stmts, &[], false);
        assert_eq!(map.get("p1").map(String::as_str), Some("text"));
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

    #[test]
    fn apply_rename_updates_loop_headers() {
        let mut stmts = vec![
            Stmt::NumericFor {
                var: "i".into(),
                start: Expr::Num("1".into()),
                limit: Expr::Var("limit".into()),
                step: None,
                body: vec![Stmt::Call(call("print", vec![Expr::Var("i".into())]))],
            },
            Stmt::GenericFor {
                vars: vec!["_".into(), "v0".into()],
                exprs: vec![Expr::Var("players".into())],
                body: vec![Stmt::Call(call("print", vec![Expr::Var("v0".into())]))],
            },
        ];
        let map = BTreeMap::from([
            ("i".to_string(), "index".to_string()),
            ("v0".to_string(), "player".to_string()),
        ]);

        apply_rename(&mut stmts, &map);

        match &stmts[0] {
            Stmt::NumericFor { var, body, .. } => {
                assert_eq!(var, "index");
                assert!(matches!(
                    &body[0],
                    Stmt::Call(Expr::Call(_, args)) if args == &[Expr::Var("index".into())]
                ));
            }
            _ => panic!("expected numeric for"),
        }
        match &stmts[1] {
            Stmt::GenericFor { vars, body, .. } => {
                assert_eq!(vars, &["_", "player"]);
                assert!(matches!(
                    &body[0],
                    Stmt::Call(Expr::Call(_, args)) if args == &[Expr::Var("player".into())]
                ));
            }
            _ => panic!("expected generic for"),
        }
    }

    #[test]
    fn local_defs_and_tuple_locals_get_named() {
        let stmts = vec![
            Stmt::Local {
                names: vec!["input".into()],
                values: vec![Expr::Var("p0".into())],
            },
            Stmt::Local {
                names: vec!["v0".into()],
                values: vec![Expr::Field(
                    Box::new(Expr::Var("input".into())),
                    "Position".into(),
                )],
            },
            Stmt::Local {
                names: vec!["v1".into(), "v2".into()],
                values: vec![call("pcall", vec![Expr::Var("callback".into())])],
            },
        ];

        let map = smart_rename(&stmts, &["v0".into(), "v1".into(), "v2".into()], false);

        assert_eq!(map.get("v0").map(String::as_str), Some("inputPosition"));
        assert_eq!(map.get("v1").map(String::as_str), Some("ok"));
        assert_eq!(map.get("v2").map(String::as_str), Some("result"));
    }

    #[test]
    fn expanded_event_callback_parameter_naming() {
        let stmts = vec![Stmt::Return(vec![
            Expr::Var("p0".into()),
            Expr::Var("p1".into()),
        ])];

        let map = smart_rename_with_event(&stmts, &[], false, Some("Heartbeat"));
        assert_eq!(map.get("p0").map(String::as_str), Some("deltaTime"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("Stepped"));
        assert_eq!(map.get("p0").map(String::as_str), Some("time"));
        assert_eq!(map.get("p1").map(String::as_str), Some("deltaTime"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("CharacterAdded"));
        assert_eq!(map.get("p0").map(String::as_str), Some("character"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("DescendantAdded"));
        assert_eq!(map.get("p0").map(String::as_str), Some("descendant"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("AncestryChanged"));
        assert_eq!(map.get("p0").map(String::as_str), Some("child"));
        assert_eq!(map.get("p1").map(String::as_str), Some("parent"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("TouchEnded"));
        assert_eq!(map.get("p0").map(String::as_str), Some("otherPart"));
    }

    #[test]
    fn api_slot_receiver_and_callback_names() {
        let stmts = vec![
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p0".into())),
                "IsA".into(),
                vec![Expr::Var("p1".into())],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p2".into())),
                "SetAttribute".into(),
                vec![Expr::Var("p3".into()), Expr::Var("p4".into())],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p5".into())),
                "GetPropertyChangedSignal".into(),
                vec![Expr::Var("p6".into())],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p7".into())),
                "Disconnect".into(),
                vec![],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p8".into())),
                "LoadAnimation".into(),
                vec![Expr::Var("p9".into())],
            )),
            Stmt::Call(call(
                "pcall",
                vec![Expr::Var("p10".into()), Expr::Var("payload".into())],
            )),
            Stmt::Call(Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("task".into())),
                    "delay".into(),
                )),
                vec![Expr::Num("1".into()), Expr::Var("p11".into())],
            )),
        ];

        let map = smart_rename(&stmts, &[], false);

        assert_eq!(map.get("p1").map(String::as_str), Some("className"));
        assert_eq!(map.get("p3").map(String::as_str), Some("attributeName"));
        assert_eq!(map.get("p6").map(String::as_str), Some("propertyName"));
        assert_eq!(map.get("p7").map(String::as_str), Some("connection"));
        assert_eq!(map.get("p8").map(String::as_str), Some("animator"));
        assert_eq!(map.get("p9").map(String::as_str), Some("animation"));
        assert_eq!(map.get("p10").map(String::as_str), Some("callback"));
        assert_eq!(map.get("p11").map(String::as_str), Some("callback2"));
    }

    #[test]
    fn table_callback_fields_and_export_tables_are_named() {
        let stmts = vec![
            Stmt::Local {
                names: vec!["v0".into()],
                values: vec![Expr::Table(vec![
                    TableField::Named("onClose".into(), Expr::Var("p0".into())),
                    TableField::Keyed(Expr::Str("\"setVisible\"".into()), Expr::Var("p1".into())),
                ])],
            },
            Stmt::Local {
                names: vec!["v1".into()],
                values: vec![Expr::Table(vec![])],
            },
            Stmt::Assign {
                targets: vec![Expr::Field(
                    Box::new(Expr::Var("v1".into())),
                    "DoThing".into(),
                )],
                values: vec![Expr::Closure {
                    text: "function()\nend".into(),
                    captures: vec![],
                }],
            },
            Stmt::Return(vec![Expr::Var("v1".into())]),
        ];

        let map = smart_rename(&stmts, &["v0".into(), "v1".into()], false);

        assert_eq!(map.get("p0").map(String::as_str), Some("onClose"));
        assert_eq!(map.get("p1").map(String::as_str), Some("setVisible"));
        assert_eq!(map.get("v1").map(String::as_str), Some("module"));
    }

    #[test]
    fn service_aliases_and_more_call_results_are_named() {
        let dotted_service = Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Var("game".into())),
                "GetService".into(),
            )),
            vec![Expr::Var("game".into()), s("Players")],
        );
        assert_eq!(derive_name(&dotted_service).as_deref(), Some("Players"));

        let require_synthetic = call("require", vec![Expr::Var("v0".into())]);
        assert_eq!(derive_name(&require_synthetic), None);

        assert_eq!(
            derive_name(&Expr::Field(
                Box::new(Expr::Var("game".into())),
                "ReplicatedStorage".into()
            ))
            .as_deref(),
            Some("ReplicatedStorage")
        );
        assert_eq!(
            derive_name(&Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("RaycastParams".into())),
                    "new".into(),
                )),
                vec![],
            ))
            .as_deref(),
            Some("raycastParams")
        );
        assert_eq!(
            derive_name(&Expr::MethodCall(
                Box::new(Expr::Var("animator".into())),
                "LoadAnimation".into(),
                vec![Expr::Var("animation".into())],
            ))
            .as_deref(),
            Some("track")
        );
    }

    #[test]
    fn much_more_event_callback_parameter_naming() {
        let stmts = vec![Stmt::Return(vec![
            Expr::Var("p0".into()),
            Expr::Var("p1".into()),
        ])];

        let map = smart_rename_with_event(&stmts, &[], false, Some("OnClientEvent"));
        assert_eq!(map.get("p0").map(String::as_str), Some("payload"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("OnServerInvoke"));
        assert_eq!(map.get("p0").map(String::as_str), Some("player"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("Activated"));
        assert_eq!(map.get("p0").map(String::as_str), Some("input"));
        assert_eq!(map.get("p1").map(String::as_str), Some("clickCount"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("FocusLost"));
        assert_eq!(map.get("p0").map(String::as_str), Some("enterPressed"));
        assert_eq!(map.get("p1").map(String::as_str), Some("input"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("Equipped"));
        assert_eq!(map.get("p0").map(String::as_str), Some("mouse"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("StateChanged"));
        assert_eq!(map.get("p0").map(String::as_str), Some("oldState"));
        assert_eq!(map.get("p1").map(String::as_str), Some("newState"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("Seated"));
        assert_eq!(map.get("p0").map(String::as_str), Some("active"));
        assert_eq!(map.get("p1").map(String::as_str), Some("seatPart"));

        let map = smart_rename_with_event(&stmts, &[], false, Some("KeyframeReached"));
        assert_eq!(map.get("p0").map(String::as_str), Some("keyframeName"));
    }

    #[test]
    fn roblox_usage_hints_name_many_receivers_and_arguments() {
        let stmts = vec![
            Stmt::Return(vec![
                Expr::Field(Box::new(Expr::Var("p0".into())), "Health".into()),
                Expr::Field(Box::new(Expr::Var("p1".into())), "MouseButton1Click".into()),
                Expr::Field(Box::new(Expr::Var("p2".into())), "Text".into()),
                Expr::Field(Box::new(Expr::Var("p3".into())), "SoundId".into()),
                Expr::Field(Box::new(Expr::Var("p4".into())), "FieldOfView".into()),
                Expr::Field(Box::new(Expr::Var("p5".into())), "Part0".into()),
            ]),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p6".into())),
                "Kick".into(),
                vec![],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p7".into())),
                "TakeDamage".into(),
                vec![Expr::Num("10".into())],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p8".into())),
                "GetTouchingParts".into(),
                vec![],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p9".into())),
                "JSONDecode".into(),
                vec![Expr::Var("json".into())],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p10".into())),
                "BindAction".into(),
                vec![
                    Expr::Var("p11".into()),
                    Expr::Var("p12".into()),
                    Expr::Bool(false),
                ],
            )),
            Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Var("p13".into())),
                "SetNetworkOwner".into(),
                vec![Expr::Var("p14".into())],
            )),
        ];

        let map = smart_rename(&stmts, &[], false);

        assert_eq!(map.get("p0").map(String::as_str), Some("humanoid"));
        assert_eq!(map.get("p1").map(String::as_str), Some("button"));
        assert_eq!(map.get("p2").map(String::as_str), Some("label"));
        assert_eq!(map.get("p3").map(String::as_str), Some("sound"));
        assert_eq!(map.get("p4").map(String::as_str), Some("camera"));
        assert_eq!(map.get("p5").map(String::as_str), Some("weld"));
        assert_eq!(map.get("p6").map(String::as_str), Some("player"));
        assert_eq!(map.get("p7").map(String::as_str), Some("humanoid2"));
        assert_eq!(map.get("p8").map(String::as_str), Some("part"));
        assert_eq!(map.get("p9").map(String::as_str), Some("httpService"));
        assert_eq!(
            map.get("p10").map(String::as_str),
            Some("contextActionService")
        );
        assert_eq!(map.get("p11").map(String::as_str), Some("actionName"));
        assert_eq!(map.get("p12").map(String::as_str), Some("callback"));
        assert_eq!(map.get("p13").map(String::as_str), Some("part2"));
        assert_eq!(map.get("p14").map(String::as_str), Some("player2"));
    }

    #[test]
    fn tuple_method_results_and_framework_calls_are_named() {
        let stmts = vec![
            Stmt::Local {
                names: vec!["v0".into(), "v1".into()],
                values: vec![Expr::MethodCall(
                    Box::new(Expr::Var("model".into())),
                    "GetBoundingBox".into(),
                    vec![],
                )],
            },
            Stmt::Local {
                names: vec!["v2".into(), "v3".into()],
                values: vec![Expr::MethodCall(
                    Box::new(Expr::Var("camera".into())),
                    "WorldToViewportPoint".into(),
                    vec![Expr::Var("worldPosition".into())],
                )],
            },
            Stmt::Local {
                names: vec!["v4".into(), "v5".into(), "v6".into()],
                values: vec![Expr::MethodCall(
                    Box::new(Expr::Var("transform".into())),
                    "ToOrientation".into(),
                    vec![],
                )],
            },
        ];

        let map = smart_rename(
            &stmts,
            &[
                "v0".into(),
                "v1".into(),
                "v2".into(),
                "v3".into(),
                "v4".into(),
                "v5".into(),
                "v6".into(),
            ],
            false,
        );

        assert_eq!(map.get("v0").map(String::as_str), Some("cframe"));
        assert_eq!(map.get("v1").map(String::as_str), Some("size"));
        assert_eq!(map.get("v2").map(String::as_str), Some("screenPoint"));
        assert_eq!(map.get("v3").map(String::as_str), Some("onScreen"));
        assert_eq!(map.get("v4").map(String::as_str), Some("x"));
        assert_eq!(map.get("v5").map(String::as_str), Some("y"));
        assert_eq!(map.get("v6").map(String::as_str), Some("z"));

        assert_eq!(
            derive_name(&Expr::MethodCall(
                Box::new(Expr::Var("tweenService".into())),
                "Create".into(),
                vec![
                    Expr::Var("object".into()),
                    Expr::Var("info".into()),
                    Expr::Var("goals".into()),
                ],
            ))
            .as_deref(),
            Some("tween")
        );
        assert_eq!(
            derive_name(&Expr::MethodCall(
                Box::new(Expr::Var("pathfindingService".into())),
                "CreatePath".into(),
                vec![],
            ))
            .as_deref(),
            Some("path")
        );
        assert_eq!(
            derive_name(&Expr::MethodCall(
                Box::new(Expr::Var("collectionService".into())),
                "GetTagged".into(),
                vec![s("Enemy")],
            ))
            .as_deref(),
            Some("tagged")
        );

        let loop_stmts = vec![Stmt::GenericFor {
            vars: vec!["_".into(), "v0".into()],
            exprs: vec![Expr::MethodCall(
                Box::new(Expr::Var("collectionService".into())),
                "GetTagged".into(),
                vec![s("Enemies")],
            )],
            body: vec![],
        }];
        let map = smart_rename(&loop_stmts, &[], false);
        assert_eq!(map.get("v0").map(String::as_str), Some("enemy"));
    }

    #[test]
    fn expanded_class_constructor_hints() {
        let cases = [
            ("Folder", "folder"),
            ("Model", "model"),
            ("Attachment", "attachment"),
            ("TextBox", "textBox"),
            ("ScreenGui", "screenGui"),
            ("WeldConstraint", "weld"),
            ("Motor6D", "motor"),
            ("ProximityPrompt", "prompt"),
            ("ClickDetector", "clickDetector"),
            ("RaycastParams", "raycastParams"),
        ];

        for (class_name, expected) in cases {
            let expr = Expr::Call(
                Box::new(Expr::Field(
                    Box::new(Expr::Var("Instance".into())),
                    "new".into(),
                )),
                vec![s(class_name)],
            );
            assert_eq!(derive_name(&expr).as_deref(), Some(expected));
        }
    }

    fn instance_new(class: &str) -> Expr {
        Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Var("Instance".into())),
                "new".into(),
            )),
            vec![s(class)],
        )
    }

    #[test]
    fn lifetime_name_groups_class_families() {
        // Different classes of one family -> the family name.
        assert_eq!(
            lifetime_name(&[instance_new("Motor6D"), instance_new("Weld")]).as_deref(),
            Some("joint")
        );
        assert_eq!(
            lifetime_name(&[instance_new("Part"), instance_new("WedgePart")]).as_deref(),
            Some("part")
        );
        assert_eq!(
            lifetime_name(&[instance_new("StringValue"), instance_new("NumberValue")]).as_deref(),
            Some("value")
        );
        // Same class throughout -> the specific name, not the family name.
        assert_eq!(
            lifetime_name(&[instance_new("Motor6D"), instance_new("Motor6D")]).as_deref(),
            Some("motor")
        );
        // Unrelated families -> no opinion (variable stays generic).
        assert_eq!(lifetime_name(&[instance_new("Sound"), instance_new("Part")]), None);
    }

    #[test]
    fn lifetime_name_handles_get_or_create() {
        let find = |name: &str| {
            Expr::MethodCall(
                Box::new(Expr::Var("parent".into())),
                "FindFirstChild".into(),
                vec![s(name)],
            )
        };
        // `parent:FindFirstChild("CCE") or Instance.new("ColorCorrectionEffect")` — the variable
        // holds a ColorCorrectionEffect either way, so it is named after the constructed class.
        assert_eq!(
            lifetime_name(&[find("CursorFreeCC"), instance_new("ColorCorrectionEffect")]).as_deref(),
            Some("colorCorrectionEffect")
        );
        // A child lookup mixed with a joint-family constructor still resolves to the family.
        assert_eq!(
            lifetime_name(&[find("Joint"), instance_new("Motor6D"), instance_new("Weld")]).as_deref(),
            Some("joint")
        );
        // A genuinely unrelated value (a plain call) mixed in stays conservative.
        let other_call = Expr::Call(Box::new(Expr::Var("compute".into())), vec![]);
        assert_eq!(lifetime_name(&[other_call, instance_new("Part")]), None);
    }

    #[test]
    fn lifetime_name_handles_divergent_part_roles() {
        let field = |f: &str| Expr::Field(Box::new(Expr::Var("instance".into())), f.into());
        let find = |name: &str| {
            Expr::MethodCall(
                Box::new(Expr::Var("instance".into())),
                "FindFirstChild".into(),
                vec![s(name)],
            )
        };
        // .PrimaryPart in one branch, :FindFirstChild("Middle") in another -> "mainPart".
        assert_eq!(
            lifetime_name(&[field("PrimaryPart"), find("Middle")]).as_deref(),
            Some("mainPart")
        );
        // A single uniform part source is not divergent -> defer to the normal naming path.
        assert_eq!(lifetime_name(&[field("PrimaryPart")]), None);
        // Non-part child lookups with no part anchor -> no "mainPart" claim.
        assert_eq!(lifetime_name(&[find("Config"), find("Settings")]), None);
        // nil resets between class assignments are ignored, not treated as a conflict.
        assert_eq!(
            lifetime_name(&[instance_new("Weld"), Expr::Nil, instance_new("Motor6D")]).as_deref(),
            Some("joint")
        );
    }

    #[test]
    fn divergent_definitions_get_lifetime_names_end_to_end() {
        // v5 holds a Motor6D in one branch and a Weld in another: both joints -> "joint".
        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("v5".into())],
                values: vec![instance_new("Motor6D")],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v5".into())],
                values: vec![instance_new("Weld")],
            },
        ];
        let map = smart_rename(&stmts, &["v5".to_string()], false);
        assert_eq!(map.get("v5").map(String::as_str), Some("joint"));

        // v4 is the model's main part, reached two different ways -> "mainPart".
        let field = |f: &str| Expr::Field(Box::new(Expr::Var("instance".into())), f.into());
        let find = Expr::MethodCall(
            Box::new(Expr::Var("instance".into())),
            "FindFirstChild".into(),
            vec![s("Middle")],
        );
        let stmts = vec![
            Stmt::Assign {
                targets: vec![Expr::Var("v4".into())],
                values: vec![field("PrimaryPart")],
            },
            Stmt::Assign {
                targets: vec![Expr::Var("v4".into())],
                values: vec![find],
            },
        ];
        let map = smart_rename(&stmts, &["v4".to_string()], false);
        assert_eq!(map.get("v4").map(String::as_str), Some("mainPart"));
    }

    #[test]
    fn framework_callback_slots_name_arguments() {
        let bind_render = vec![Stmt::Call(Expr::MethodCall(
            Box::new(Expr::Var("p0".into())),
            "BindToRenderStep".into(),
            vec![
                Expr::Var("p1".into()),
                Expr::Num("100".into()),
                Expr::Var("p2".into()),
            ],
        ))];
        let map = smart_rename(&bind_render, &[], false);
        assert_eq!(map.get("p0").map(String::as_str), Some("runService"));
        assert_eq!(map.get("p1").map(String::as_str), Some("renderStepName"));
        assert_eq!(map.get("p2").map(String::as_str), Some("callback"));

        let promise = vec![Stmt::Call(Expr::Call(
            Box::new(Expr::Field(
                Box::new(Expr::Var("Promise".into())),
                "new".into(),
            )),
            vec![Expr::Var("p0".into())],
        ))];
        let map = smart_rename(&promise, &[], false);
        assert_eq!(map.get("p0").map(String::as_str), Some("callback"));
    }
}

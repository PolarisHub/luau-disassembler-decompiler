//! Loop / control-flow structuring: the decompiler must never leave `goto`/`::label::` in
//! its output (this Luau dialect has no goto grammar, so any survivor is a syntax error), and
//! every reconstruction must recompile. Each case is a control-flow shape the compiler lowers
//! through forward/backward jumps — `break`, `continue`, nested loops, `while true`, early
//! returns — that the recovery passes must fold back into structured Luau.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use luau_bytecode::parse_and_validate;
use luau_decompile::decompile;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

/// Compile a snippet with the vendored oracle. Returns None if the oracle is unavailable so
/// the test degrades to a skip on machines without `tools/luau-compile.exe`.
fn compile(tag: &str, source: &str) -> Option<Vec<u8>> {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        return None;
    }
    let path = std::env::temp_dir().join(format!("luau_loopstruct_{tag}.luau"));
    fs::write(&path, source).unwrap();
    let output = Command::new(&luau)
        .arg("--binary")
        .arg("-O1")
        .arg("-g2")
        .arg("--fflags=LuauEmitCallFeedback=false,LuauCompileUdataDirect=false,LuauIntegerType2=false")
        .arg(&path)
        .output()
        .expect("run luau-compile");
    let ok = output.status.success()
        && output
            .stdout
            .first()
            .map(|&b| (3..=11).contains(&b))
            .unwrap_or(false);
    ok.then_some(output.stdout)
}

const CASES: &[(&str, &str)] = &[
    (
        "if_elseif_else",
        r#"local function f(x)
            if x == 1 then return "a"
            elseif x == 2 then return "b"
            elseif x == 3 then return "c"
            else return "d" end
        end
        return f"#,
    ),
    (
        "while_break_continue",
        r#"local function f(t)
            local s = 0
            local i = 1
            while i <= #t do
                if t[i] < 0 then i = i + 1; continue end
                if t[i] > 100 then break end
                s = s + t[i]
                i = i + 1
            end
            return s
        end
        return f"#,
    ),
    (
        "while_mid_continue",
        r#"local function f(t)
            local s = 0
            local i = 0
            while i < #t do
                i = i + 1
                if t[i] % 2 == 0 then continue end
                s = s + t[i]
            end
            return s
        end
        return f"#,
    ),
    (
        "while_break_and_continue_both",
        r#"local function f(t, limit)
            local s = 0
            local i = 0
            while true do
                i = i + 1
                if i > #t then break end
                if t[i] < 0 then continue end
                s = s + t[i]
                if s > limit then break end
            end
            return s
        end
        return f"#,
    ),
    (
        "nested_while_inner_break",
        r#"local function f(rows)
            local found = 0
            local i = 1
            while i <= #rows do
                local j = 1
                while j <= #rows[i] do
                    if rows[i][j] == "x" then
                        found = found + 1
                        break
                    end
                    j = j + 1
                end
                i = i + 1
            end
            return found
        end
        return f"#,
    ),
    (
        "numeric_for_continue",
        r#"local function f(n)
            local s = 0
            for i = 1, n do
                if i % 3 == 0 then continue end
                s = s + i
            end
            return s
        end
        return f"#,
    ),
    (
        "while_multi_break",
        r#"local function f(t)
            local i = 1
            while i <= #t do
                if t[i] == "stop" then break end
                if t[i] == "halt" then break end
                i = i + 1
            end
            return i
        end
        return f"#,
    ),
    (
        "nested_loops_return",
        r#"local function f(grid)
            for i = 1, #grid do
                for j = 1, #grid[i] do
                    if grid[i][j] == 0 then return i, j end
                end
            end
            return nil
        end
        return f"#,
    ),
    (
        "while_true_body_returns",
        r#"local function f(queue)
            while true do
                local item = queue:pop()
                if item == nil then return nil end
                if item.done then return item end
            end
        end
        return f"#,
    ),
    (
        "guard_continue_loop",
        r#"local function f(items)
            local out = {}
            for _, v in ipairs(items) do
                if not v.active then continue end
                if v.value == nil then continue end
                table.insert(out, v.value)
            end
            return out
        end
        return f"#,
    ),
];

#[test]
fn loops_structure_without_goto_and_recompile() {
    if compile("probe", "return 1").is_none() {
        eprintln!("luau-compile.exe unavailable; skipping loop-structuring test");
        return;
    }
    for (tag, src) in CASES {
        let bytes = compile(tag, src).unwrap_or_else(|| panic!("[{tag}] oracle compile failed"));
        let module =
            parse_and_validate(&bytes).unwrap_or_else(|e| panic!("[{tag}] parse failed: {e:?}"));
        let out = decompile(&module);

        assert!(
            !out.source.contains("goto ") && !out.source.contains("::"),
            "[{tag}] goto/label survived structuring:\n{}",
            out.source
        );
        assert!(
            compile(&format!("{tag}_rt"), &out.source).is_some(),
            "[{tag}] reconstruction did not recompile:\n{}",
            out.source
        );
    }
}

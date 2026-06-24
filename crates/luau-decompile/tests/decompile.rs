//! Decompiler tests: never panics on the corpus, straight-line functions reconstruct
//! cleanly, and their output is valid Luau that the real compiler accepts (round-trip).

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

fn read(name: &str) -> Vec<u8> {
    fs::read(root().join("corpus").join("bytecode").join(name)).unwrap()
}

fn compile_source(name: &str) -> Option<Vec<u8>> {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        return None;
    }
    let source = root().join("corpus").join("src").join(name);
    let output = Command::new(&luau)
        .arg("--binary")
        .arg(&source)
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

fn all_files() -> Vec<PathBuf> {
    let dir = root().join("corpus").join("bytecode");
    let mut v: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "luauc").unwrap_or(false))
        .collect();
    v.sort();
    v
}

fn compact_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn decompiles_whole_corpus_without_panic() {
    for path in all_files() {
        let bytes = fs::read(&path).unwrap();
        let module = parse_and_validate(&bytes).unwrap();
        let out = decompile(&module);
        assert!(!out.source.is_empty(), "{}: empty output", path.display());
    }
}

#[test]
fn straight_line_functions_are_not_partial() {
    for name in ["02_arith", "09_method_call", "14_string_ops"] {
        let module = parse_and_validate(&read(&format!("{name}.luauc"))).unwrap();
        let out = decompile(&module);
        assert!(
            !out.partial,
            "{name}: expected fully structured (no goto), notes={:?}",
            out.per_proto
        );
    }
}

#[test]
fn table_literals_reconstructed() {
    // NEWTABLE + SETLIST/SETTABLEKS fills should fold back into table literals.
    let arr = decompile(&parse_and_validate(&read("01_literals.luauc")).unwrap()).source;
    let arr_compact = compact_ws(&arr);
    assert!(
        arr_compact.contains("{1, 2, 3}"),
        "array literal not rebuilt:\n{arr}"
    );

    let mixed = decompile(&parse_and_validate(&read("10_tables.luauc")).unwrap()).source;
    let mixed_compact = compact_ws(&mixed);
    assert!(
        mixed_compact.contains("{ 10, 20, 30, 40, }") || mixed_compact.contains("{10, 20, 30, 40}"),
        "array not rebuilt:\n{mixed}"
    );
    assert!(
        mixed.contains("name = \"luau\""),
        "hash literal not rebuilt:\n{mixed}"
    );
}

#[test]
fn sibling_closures_resolve_distinct_protos() {
    // NEWCLOSURE's D operand indexes the parent's child-proto list, not the flat table.
    // Two siblings capturing the same upvalue must render their OWN (distinct) bodies, the
    // captured local must be materialized, and an upvalue write must not be folded away.
    let out = decompile(&parse_and_validate(&read("18_sibling_closures.luauc")).unwrap()).source;
    assert!(out.contains("hits = hits + 1"), "bump body wrong:\n{out}");
    assert!(
        out.contains("hits = 0"),
        "captured local/reset lost:\n{out}"
    );
    // `reset` writes the shared upvalue then returns it — must not collapse to `return 0`.
    assert!(
        out.contains("return hits"),
        "upvalue write was folded away:\n{out}"
    );
    // The chained capture (inner closure reads the outer closure's upvalues) resolves names.
    assert!(
        out.contains("name .. \": \") .. hits") || out.contains("(name .. \": \") .. hits"),
        "chained upvalue names not resolved:\n{out}"
    );
}

#[test]
fn multret_call_args_reconstructed() {
    // A multret producer (C=0) feeding a "to top" consumer (B=0) must keep the call as an
    // expanding expression, not a `--[[...]]` marker or a single-value truncation.
    let out = decompile(&parse_and_validate(&read("19_multret.luauc")).unwrap()).source;
    assert!(!out.contains("--[[...]]"), "multret marker left in:\n{out}");
    assert!(
        out.contains("math.max(triple())"),
        "f(g()) not rebuilt:\n{out}"
    );
    assert!(
        out.contains("{triple()}"),
        "open table {{g()}} not rebuilt:\n{out}"
    );
    assert!(
        out.contains("print(triple())"),
        "print(g()) not rebuilt:\n{out}"
    );
    assert!(
        out.contains("return triple()"),
        "multret return not rebuilt:\n{out}"
    );
    assert!(
        recompiles(&out, "multret"),
        "multret output must recompile:\n{out}"
    );
}

#[test]
fn loop_break_and_continue_recovered() {
    // Conditional jumps to a loop's exit / continue point must lower to native `break` /
    // `continue` keywords (this Luau dialect has no goto), and the result must recompile.
    let out = decompile(&parse_and_validate(&read("20_loop_control.luauc")).unwrap()).source;
    assert!(!out.contains("goto"), "goto left in loop output:\n{out}");
    assert!(out.contains("break"), "break not recovered:\n{out}");
    assert!(out.contains("continue"), "continue not recovered:\n{out}");
    assert!(
        recompiles(&out, "loopctl"),
        "loop-control output must recompile:\n{out}"
    );
}

#[test]
fn guard_chains_recovered() {
    // `if not (a and b ...) then return/break end` compiles to a run of conditional jumps
    // converging on a terminator block; the structurer must rebuild the combined condition
    // (no goto), and recompiling must preserve the control-flow shape.
    let out = decompile(&parse_and_validate(&read("21_guards.luauc")).unwrap()).source;
    assert!(!out.contains("goto"), "goto left in guard output:\n{out}");
    assert!(
        out.contains("if not (a and b) then"),
        "two-condition guard not rebuilt:\n{out}"
    );
    assert!(
        out.contains("if not (a and b and c) then"),
        "three-condition guard not flattened:\n{out}"
    );
    assert!(
        recompiles(&out, "guards"),
        "guard output must recompile:\n{out}"
    );
}

#[test]
fn short_circuit_return_recovered_without_goto() {
    let Some(bytes) = compile_source("22_short_circuit_return.luau") else {
        eprintln!("skipping: compiler not present");
        return;
    };
    let module = parse_and_validate(&bytes).unwrap();
    let out = decompile(&module);
    assert!(
        !out.partial,
        "short-circuit return stayed partial:\n{}",
        out.source
    );
    assert!(
        !out.source.contains("goto"),
        "goto left in output:\n{}",
        out.source
    );
    assert!(
        out.source.contains("return (v1 and v1.icon) or"),
        "and/or return not rebuilt cleanly:\n{}",
        out.source
    );
    assert!(
        recompiles(&out.source, "short_circuit_return"),
        "short-circuit output must recompile:\n{}",
        out.source
    );
}

#[test]
fn method_calls_reconstructed() {
    let module = parse_and_validate(&read("09_method_call.luauc")).unwrap();
    let out = decompile(&module);
    assert!(out.source.contains(":upper()"), "{}", out.source);
    assert!(out.source.contains(":rep(2)"), "{}", out.source);
}

/// Round-trip validity: the decompiled output of straight-line functions must be Luau the
/// real compiler accepts. Skipped automatically when the vendored compiler is absent.
#[test]
fn straight_line_output_recompiles() {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        eprintln!("skipping: {} not present", luau.display());
        return;
    }

    for name in ["02_arith", "09_method_call", "14_string_ops"] {
        let module = parse_and_validate(&read(&format!("{name}.luauc"))).unwrap();
        let src = decompile(&module).source;

        let tmp = std::env::temp_dir().join(format!("luau_rt_{name}.luau"));
        fs::write(&tmp, &src).unwrap();

        let output = Command::new(&luau)
            .arg("--binary")
            .arg(&tmp)
            .output()
            .expect("run luau-compile");

        // luau-compile emits a version-0 error blob on failure; success starts with a
        // valid version byte in [3, 11].
        let ok = output.status.success()
            && output
                .stdout
                .first()
                .map(|&b| (3..=11).contains(&b))
                .unwrap_or(false);
        assert!(
            ok,
            "{name}: decompiled output did not recompile.\n--- source ---\n{src}\n--- stderr ---\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn read_stripped(name: &str) -> Vec<u8> {
    fs::read(root().join("corpus").join("bytecode-stripped").join(name)).unwrap()
}

/// Returns true if `src` compiles cleanly with the vendored compiler, or true (skip) when
/// the compiler is absent.
fn recompiles(src: &str, tag: &str) -> bool {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        return true;
    }
    let tmp = std::env::temp_dir().join(format!("luau_rt_{tag}.luau"));
    fs::write(&tmp, src).unwrap();
    let output = Command::new(&luau)
        .arg("--binary")
        .arg(&tmp)
        .output()
        .expect("run luau-compile");
    output.status.success()
        && output
            .stdout
            .first()
            .map(|&b| (3..=11).contains(&b))
            .unwrap_or(false)
}

#[test]
fn roblox_idioms_get_smart_names() {
    // Stripped (no debug names) so the name-derivation heuristics must do the work.
    let module = parse_and_validate(&read_stripped("16_roblox.luauc")).unwrap();
    let out = decompile(&module);
    for needle in [
        "Players = game:GetService(\"Players\")",
        "MyModule = require(",
        "MyModule_doThing = require(game.ReplicatedStorage.MyModule).doThing",
        "part = Instance.new(\"Part\")",
        "Players.LocalPlayer.Character",
        "#workspace:GetChildren()",
    ] {
        assert!(
            out.source.contains(needle),
            "missing {needle:?} in:\n{}",
            out.source
        );
    }
    assert!(
        recompiles(&out.source, "roblox"),
        "smart-named output must recompile:\n{}",
        out.source
    );
}

/// Recompile `src`, returning the resulting bytecode, or `None` when the compiler is absent.
fn recompile_bytes(src: &str, tag: &str) -> Option<Vec<u8>> {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        return None;
    }
    let tmp = std::env::temp_dir().join(format!("luau_sig_{tag}.luau"));
    fs::write(&tmp, src).unwrap();
    let out = Command::new(&luau)
        .arg("--binary")
        .arg("-O1")
        .arg(&tmp)
        .output()
        .expect("run luau-compile");
    if out.status.success()
        && out
            .stdout
            .first()
            .map(|&b| (3..=11).contains(&b))
            .unwrap_or(false)
    {
        Some(out.stdout)
    } else {
        None
    }
}

/// Count opcodes by category across a module:
/// [numeric-for, generic-for, while/repeat back-edges, conditional branches, global access].
/// The global count guards against a decompiler bug turning a local into an implicit global
/// (e.g. an undeclared tuple-assignment target) — that still compiles, so only the opcode
/// profile reveals it.
fn cf_signature(m: &luau_bytecode::Module) -> [usize; 5] {
    use luau_bytecode::opcode::{insn_op, Opcode};
    let mut sig = [0usize; 5];
    for p in &m.protos {
        let mut pc = 0;
        while pc < p.code.len() {
            if let Some(op) = Opcode::from_u8(insn_op(p.code[pc])) {
                use Opcode::*;
                match op {
                    FORNPREP => sig[0] += 1,
                    FORGPREP | FORGPREP_INEXT | FORGPREP_NEXT => sig[1] += 1,
                    JUMPBACK => sig[2] += 1,
                    JUMPIF | JUMPIFNOT | JUMPIFEQ | JUMPIFLE | JUMPIFLT | JUMPIFNOTEQ
                    | JUMPIFNOTLE | JUMPIFNOTLT | JUMPXEQKNIL | JUMPXEQKB | JUMPXEQKN
                    | JUMPXEQKS => sig[3] += 1,
                    GETGLOBAL | SETGLOBAL => sig[4] += 1,
                    _ => {}
                }
                pc += op.length().max(1);
            } else {
                pc += 1;
            }
        }
    }
    sig
}

/// The structural round-trip: every fully-structured (non-partial) decompilation must
/// recompile to bytecode with the SAME control-flow shape (same count of for/while/if
/// constructs) as the original. This proves the structurer recovered the real control flow,
/// not just something that happens to compile.
#[test]
fn structured_corpus_round_trips() {
    if !root().join("tools").join("luau-compile.exe").exists() {
        eprintln!("skipping: compiler not present");
        return;
    }
    for path in all_files() {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let original = parse_and_validate(&fs::read(&path).unwrap()).unwrap();
        let out = decompile(&original);
        if out.partial {
            continue;
        }
        let bytes = recompile_bytes(&out.source, &name).unwrap_or_else(|| {
            panic!(
                "{name}: non-partial output failed to recompile:\n{}",
                out.source
            )
        });
        let recompiled = parse_and_validate(&bytes).unwrap();
        assert_eq!(
            cf_signature(&original),
            cf_signature(&recompiled),
            "{name}: control-flow shape changed.\n{}",
            out.source
        );
    }
}

#[test]
fn stripped_corpus_recompiles() {
    // Synthesized + smart-named output for the whole STRIPPED corpus (no debug names) must
    // still be valid Luau the real compiler accepts.
    let dir = root().join("corpus").join("bytecode-stripped");
    if !dir.exists() {
        return;
    }
    let mut files: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "luauc").unwrap_or(false))
        .collect();
    files.sort();
    for path in files {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let module = parse_and_validate(&fs::read(&path).unwrap()).unwrap();
        let out = decompile(&module);
        if out.partial {
            continue; // goto fallback isn't valid Luau by design; skip
        }
        assert!(
            recompiles(&out.source, &format!("strip_{name}")),
            "{name} (stripped) did not recompile:\n{}",
            out.source
        );
    }
}

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
        "children = workspace:GetChildren()",
        "count = #children",
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

#[test]
fn stripped_straight_line_recompiles() {
    // Synthesized + smart-named output for stripped bytecode is still valid Luau.
    for name in ["02_arith", "09_method_call", "14_string_ops", "16_roblox"] {
        let module = parse_and_validate(&read_stripped(&format!("{name}.luauc"))).unwrap();
        let out = decompile(&module);
        if out.partial {
            continue; // control-flow regions fall back to goto; skip those here
        }
        assert!(
            recompiles(&out.source, &format!("strip_{name}")),
            "{name} (stripped) did not recompile:\n{}",
            out.source
        );
    }
}

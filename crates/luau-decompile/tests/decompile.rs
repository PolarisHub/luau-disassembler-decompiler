//! Decompiler tests: never panics on the corpus, straight-line functions reconstruct
//! cleanly, and their output is valid Luau that the real compiler accepts (round-trip).

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use luau_bytecode::opcode::Opcode;
use luau_bytecode::{parse_and_validate, parse_normalized};
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

fn compile_inline_source(tag: &str, source: &str) -> Option<Vec<u8>> {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        return None;
    }
    let path = std::env::temp_dir().join(format!("luau_gen_{tag}.luau"));
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

fn push_varint(out: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        out.push(((value as u8) & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

fn push_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn abc(op: Opcode, a: u8, b: u8, c: u8) -> u32 {
    (op as u32) | ((a as u32) << 8) | ((b as u32) << 16) | ((c as u32) << 24)
}

fn ad(op: Opcode, a: u8, d: i16) -> u32 {
    (op as u32) | ((a as u32) << 8) | (((d as u16) as u32) << 16)
}

fn push_string_table(out: &mut Vec<u8>, strings: &[&str]) {
    push_varint(out, strings.len() as u64);
    for string in strings {
        push_varint(out, string.len() as u64);
        out.extend_from_slice(string.as_bytes());
    }
}

fn push_minimal_proto(
    out: &mut Vec<u8>,
    max_stack: u8,
    code: &[u32],
    constants: impl FnOnce(&mut Vec<u8>),
) {
    out.push(max_stack);
    out.push(0); // num params
    out.push(0); // num upvalues
    out.push(0); // is vararg
    out.push(0); // flags
    push_varint(out, 0); // type-info size

    push_varint(out, code.len() as u64);
    for &word in code {
        push_u32(out, word);
    }

    constants(out);

    push_varint(out, 0); // child protos
    push_varint(out, 0); // line defined
    push_varint(out, 0); // debug name
    out.push(0); // no line info
    out.push(0); // no debug info
}

fn push_minimal_proto_v11(
    out: &mut Vec<u8>,
    max_stack: u8,
    code: &[u32],
    constants: impl FnOnce(&mut Vec<u8>),
    feedback: &[u32],
) {
    push_minimal_proto(out, max_stack, code, constants);
    push_varint(out, feedback.len() as u64);
    for &pc in feedback {
        out.push(0); // LFT_CALLTARGET
        push_varint(out, pc as u64);
    }
}

fn version8_integer_blob() -> Vec<u8> {
    let mut out = vec![8, 1];
    push_string_table(&mut out, &[]);
    push_varint(&mut out, 1);
    push_minimal_proto(
        &mut out,
        1,
        &[ad(Opcode::LOADK, 0, 0), abc(Opcode::RETURN, 0, 2, 0)],
        |out| {
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::INTEGER);
            out.push(0);
            push_varint(out, 42);
        },
    );
    push_varint(&mut out, 0);
    out
}

fn version9_udata_blob() -> Vec<u8> {
    let mut out = vec![9, 1];
    push_string_table(&mut out, &["object", "Foo"]);
    push_varint(&mut out, 1);
    push_minimal_proto(
        &mut out,
        1,
        &[
            abc(Opcode::GETGLOBAL, 0, 0, 0),
            0,
            abc(Opcode::GETUDATAKS, 0, 0, 0),
            0x1234_0001,
            abc(Opcode::RETURN, 0, 2, 0),
        ],
        |out| {
            push_varint(out, 2);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 2);
        },
    );
    push_varint(&mut out, 0);
    out
}

fn version9_udata_namecall_blob() -> Vec<u8> {
    let mut out = vec![9, 1];
    push_string_table(&mut out, &["object", "Foo"]);
    push_varint(&mut out, 1);
    push_minimal_proto(
        &mut out,
        2,
        &[
            abc(Opcode::GETGLOBAL, 1, 0, 0),
            0,
            abc(Opcode::NAMECALLUDATA, 0, 1, 0),
            0xCAFE_0001,
            abc(Opcode::CALL, 0, 2, 2),
            abc(Opcode::RETURN, 0, 2, 0),
        ],
        |out| {
            push_varint(out, 2);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 2);
        },
    );
    push_varint(&mut out, 0);
    out
}

fn version9_udata_set_blob() -> Vec<u8> {
    let mut out = vec![9, 1];
    push_string_table(&mut out, &["object", "Foo"]);
    push_varint(&mut out, 1);
    push_minimal_proto(
        &mut out,
        2,
        &[
            abc(Opcode::GETGLOBAL, 0, 0, 0),
            0,
            abc(Opcode::LOADN, 1, 5, 0),
            abc(Opcode::SETUDATAKS, 1, 0, 0),
            0xBEEF_0001,
            abc(Opcode::RETURN, 0, 1, 0),
        ],
        |out| {
            push_varint(out, 2);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 2);
        },
    );
    push_varint(&mut out, 0);
    out
}

fn version10_newclassmember_blob() -> Vec<u8> {
    let mut out = vec![10, 1];
    push_string_table(&mut out, &["Class", "Foo"]);
    push_varint(&mut out, 1);
    push_minimal_proto(
        &mut out,
        2,
        &[
            abc(Opcode::GETGLOBAL, 0, 0, 0),
            0,
            ad(Opcode::LOADK, 1, 2),
            abc(Opcode::NEWCLASSMEMBER, 0, 0, 1),
            1,
            abc(Opcode::RETURN, 0, 1, 0),
        ],
        |out| {
            push_varint(out, 3);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 2);
            out.push(luau_bytecode::constant_tag::INTEGER);
            out.push(0);
            push_varint(out, 123);
        },
    );
    push_varint(&mut out, 0);
    out
}

fn version11_callfb_blob() -> Vec<u8> {
    let mut out = vec![11, 1];
    push_string_table(&mut out, &["callback"]);
    push_varint(&mut out, 1);
    push_minimal_proto_v11(
        &mut out,
        1,
        &[
            abc(Opcode::GETGLOBAL, 0, 0, 0),
            0,
            abc(Opcode::CALLFB, 0, 1, 1),
            0,
            abc(Opcode::RETURN, 0, 1, 0),
        ],
        |out| {
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 1);
        },
        &[2],
    );
    push_varint(&mut out, 0);
    out
}

fn version11_cmpproto_blob() -> Vec<u8> {
    let mut out = vec![11, 1];
    push_string_table(&mut out, &["callback"]);
    push_varint(&mut out, 1);
    push_minimal_proto_v11(
        &mut out,
        1,
        &[
            abc(Opcode::GETGLOBAL, 0, 0, 0),
            0,
            ad(Opcode::CMPPROTO, 0, 1),
            7,
            abc(Opcode::RETURN, 0, 1, 0),
        ],
        |out| {
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 1);
        },
        &[],
    );
    push_varint(&mut out, 0);
    out
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

const IN_GAME_DEFAULT_MAX_BYTES: u64 = 512 * 1024;

fn in_game_bytecode_files() -> Vec<PathBuf> {
    in_game_bytecode_files_by_size(|len| len <= IN_GAME_DEFAULT_MAX_BYTES)
}

fn in_game_large_bytecode_files() -> Vec<PathBuf> {
    in_game_bytecode_files_by_size(|len| len > IN_GAME_DEFAULT_MAX_BYTES)
}

fn in_game_bytecode_files_by_size(keep_size: impl Fn(u64) -> bool) -> Vec<PathBuf> {
    let dir = root().join("roblox-studio-cases").join("in_game");
    if !dir.exists() {
        return Vec::new();
    }
    let mut v: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| {
            let Some(name) = p.file_name().and_then(|name| name.to_str()) else {
                return false;
            };
            let is_bytecode_luau = name.ends_with(".luau") && name.contains("Bytecode");
            let size_ok = p
                .metadata()
                .map(|metadata| keep_size(metadata.len()))
                .unwrap_or(false);
            is_bytecode_luau && size_ok
        })
        .collect();
    v.sort();
    v
}

fn in_game_all_bytecode_files() -> Vec<PathBuf> {
    let dir = root().join("roblox-studio-cases").join("in_game");
    if !dir.exists() {
        return Vec::new();
    }
    let mut v: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| {
            p.file_name()
                .and_then(|name| name.to_str())
                .map(|name| name.ends_with(".luau") && name.contains("Bytecode"))
                .unwrap_or(false)
        })
        .collect();
    v.sort();
    v
}

fn compact_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn duplicate_not_operand_in_while(source: &str) -> Option<String> {
    for line in source.lines() {
        let trimmed = line.trim();
        let Some(cond) = trimmed
            .strip_prefix("while ")
            .and_then(|text| text.strip_suffix(" do"))
        else {
            continue;
        };
        let mut seen = Vec::new();
        for operand in cond.split(" and ").map(str::trim) {
            if !operand.starts_with("not ") {
                continue;
            }
            if seen.iter().any(|seen_operand| seen_operand == operand) {
                return Some(trimmed.to_string());
            }
            seen.push(operand.to_string());
        }
    }
    None
}

fn generated_stress_sources() -> Vec<(String, String)> {
    let mut cases = Vec::new();
    for i in 1..=20 {
        cases.push((
            format!("while_loop_{i}"),
            format!(
                "local function run(limit, magnitude)\n\tlocal total = 0\n\twhile limit < magnitude and total <= limit do\n\t\ttotal += {}\n\tend\n\treturn total\nend\nreturn run({}, {})\n",
                (i % 3) + 1,
                i + 4,
                i + 20
            ),
        ));
        cases.push((
            format!("table_{i}"),
            format!(
                "local config = {{}}\nconfig.id = \"case_{i}\"\nconfig.enabled = {}\nconfig.values = {{{}, {}, {}}}\nconfig.meta = {{rank = {}, label = \"L{}\"}}\nreturn config\n",
                if i % 2 == 0 { "true" } else { "false" },
                i,
                i + 1,
                i + 2,
                i % 7,
                i
            ),
        ));
        cases.push((
            format!("branch_{i}"),
            format!(
                "local function choose(n)\n\tif n % 3 == 0 then\n\t\treturn n * {}\n\telse\n\t\treturn n + {}\n\tend\nend\nreturn choose({})\n",
                (i % 4) + 2,
                i + 3,
                i * 3
            ),
        ));
        cases.push((
            format!("numeric_loop_{i}"),
            format!(
                "local total = 0\nfor n = 1, {} do\n\tif n % 2 == 0 then\n\t\ttotal += n\n\telse\n\t\ttotal -= {}\n\tend\nend\nreturn total\n",
                i + 3,
                (i % 3) + 1
            ),
        ));
        cases.push((
            format!("generic_loop_{i}"),
            format!(
                "local items = {{{}, {}, {}}}\nlocal total = 0\nfor _, item in ipairs(items) do\n\ttotal += item\nend\nreturn total\n",
                i,
                i + 10,
                i + 20
            ),
        ));
    }
    cases
}

fn assert_readable_nonpartial_output(name: &str, source: &str) {
    assert!(
        !source.contains("goto "),
        "{name}: generated case should not need goto:\n{source}"
    );
    assert!(
        !source.contains("::L"),
        "{name}: generated case should not leave labels:\n{source}"
    );
    assert!(
        !source.contains("-- Some regions use goto/labels"),
        "{name}: non-partial header should not mention goto:\n{source}"
    );
    assert!(
        !source
            .lines()
            .any(|line| line.ends_with(' ') || line.ends_with('\t')),
        "{name}: trailing whitespace in output:\n{source}"
    );
    assert!(
        !source.contains("\n\t\n") && !source.contains("\n    \n"),
        "{name}: blank lines should be empty, not indented:\n{source}"
    );
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
fn decompiles_bytecode_version_8_integer_constants() {
    let module = parse_and_validate(&version8_integer_blob()).unwrap();
    assert_eq!(module.version, 8);

    let out = decompile(&module);
    assert!(
        !out.partial,
        "v8 integer sample should be complete: {out:?}"
    );
    assert!(
        out.source.contains("return 42"),
        "v8 integer constant should decompile as a number:\n{}",
        out.source
    );
}

#[test]
fn decompiles_bytecode_version_9_udata_field_access() {
    let module = parse_and_validate(&version9_udata_blob()).unwrap();
    assert_eq!(module.version, 9);

    let out = decompile(&module);
    assert!(!out.partial, "v9 udata sample should be complete: {out:?}");
    assert!(
        !out.source.contains("unhandled op GETUDATAKS"),
        "v9 userdata field opcode must not be emitted as unhandled:\n{}",
        out.source
    );
    assert!(
        out.source.contains("return object.Foo"),
        "v9 userdata field access should use the low 16-bit key from AUX:\n{}",
        out.source
    );

    let module = parse_and_validate(&version9_udata_namecall_blob()).unwrap();
    let out = decompile(&module);
    assert!(
        !out.partial,
        "v9 udata namecall should be complete: {out:?}"
    );
    assert!(
        !out.source.contains("unhandled op NAMECALLUDATA"),
        "v9 userdata namecall opcode must not be emitted as unhandled:\n{}",
        out.source
    );
    assert!(
        out.source.contains("return object:Foo()"),
        "v9 userdata namecall should use the low 16-bit key from AUX:\n{}",
        out.source
    );

    let module = parse_and_validate(&version9_udata_set_blob()).unwrap();
    let out = decompile(&module);
    assert!(!out.partial, "v9 udata set should be complete: {out:?}");
    assert!(
        !out.source.contains("unhandled op SETUDATAKS"),
        "v9 userdata set opcode must not be emitted as unhandled:\n{}",
        out.source
    );
    assert!(
        out.source.contains("object.Foo = 5"),
        "v9 userdata set should use the low 16-bit key from AUX:\n{}",
        out.source
    );
}

#[test]
fn decompiles_bytecode_version_10_class_member_registration() {
    let module = parse_and_validate(&version10_newclassmember_blob()).unwrap();
    assert_eq!(module.version, 10);

    let out = decompile(&module);
    assert!(
        !out.partial,
        "v10 NEWCLASSMEMBER sample should be complete: {out:?}"
    );
    assert!(
        !out.source.contains("unhandled op NEWCLASSMEMBER"),
        "v10 class-member opcode must not be emitted as unhandled:\n{}",
        out.source
    );
    assert!(
        out.source.contains("Class.Foo = 123"),
        "v10 class-member registration should print as a field assignment:\n{}",
        out.source
    );
}

#[test]
fn decompiles_bytecode_version_11_cmpproto_feedback_guard() {
    let module = parse_and_validate(&version11_callfb_blob()).unwrap();
    assert_eq!(module.version, 11);

    let out = decompile(&module);
    assert!(
        !out.partial,
        "v11 CALLFB sample should be complete: {out:?}"
    );
    assert!(
        !out.source.contains("unhandled op CALLFB"),
        "v11 CALLFB opcode must not be emitted as unhandled:\n{}",
        out.source
    );
    assert!(
        out.source.contains("callback()"),
        "v11 CALLFB should decompile as a normal call:\n{}",
        out.source
    );

    let module = parse_and_validate(&version11_cmpproto_blob()).unwrap();
    assert_eq!(module.version, 11);

    let out = decompile(&module);
    assert!(
        !out.source.contains("unhandled op CMPPROTO"),
        "v11 CMPPROTO opcode must not be emitted as unhandled:\n{}",
        out.source
    );
    assert!(
        out.per_proto.iter().any(|report| report
            .notes
            .iter()
            .any(|note| note == "CMPPROTO feedback guard approximated")),
        "v11 CMPPROTO should be recorded as an explicit feedback-guard approximation: {out:?}"
    );
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
    assert!(out.contains("hits += 1"), "bump body wrong:\n{out}");
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
fn multret_method_arg_is_not_duplicated() {
    let Some(bytes) = compile_source("23_multret_method_arg.luau") else {
        eprintln!("skipping: compiler not present");
        return;
    };
    let module = parse_and_validate(&bytes).unwrap();
    let out = decompile(&module).source;

    assert!(
        out.contains("table.insert(result, self:GetPoint(i))"),
        "method call argument not rebuilt:\n{out}"
    );
    assert_eq!(
        out.matches("self:GetPoint(i)").count(),
        1,
        "method call argument was duplicated:\n{out}"
    );
    assert!(
        recompiles(&out, "multret_method_arg"),
        "method arg output must recompile:\n{out}"
    );
}

#[test]
fn captured_service_locals_survive_smart_rename() {
    let Some(bytes) = compile_source("24_captured_services.luau") else {
        eprintln!("skipping: compiler not present");
        return;
    };
    let module = parse_and_validate(&bytes).unwrap();
    let out = decompile(&module).source;

    assert!(
        out.contains("local Debris = game:GetService(\"Debris\")"),
        "captured Debris service assignment was dropped:\n{out}"
    );
    assert!(
        out.contains("local TweenService = game:GetService(\"TweenService\")"),
        "captured TweenService assignment was dropped:\n{out}"
    );
    assert!(
        !out.contains("unhandled op CALLFB"),
        "CALLFB should decompile as a normal call:\n{out}"
    );
    assert!(
        out.contains("Debris:AddItem"),
        "upvalue use missing:\n{out}"
    );
    assert!(
        recompiles(&out, "captured_services"),
        "captured service output must recompile:\n{out}"
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
fn literal_left_comparisons_render_naturally() {
    let out = decompile(&parse_and_validate(&read("03_if_else.luauc")).unwrap()).source;
    assert!(
        out.contains("if n > 0 then"),
        "constant-left comparison should be flipped for readability:\n{out}"
    );
    assert!(
        !out.contains("if 0 < n then"),
        "backwards comparison survived:\n{out}"
    );
    assert!(
        recompiles(&out, "if_else_cmp"),
        "comparison-normalized output must recompile:\n{out}"
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
        out.contains("local total = 0"),
        "first assignment should be promoted into a local initializer:\n{out}"
    );
    assert!(
        !out.contains("local amount, total"),
        "promoted locals must not also appear in the hoist declaration:\n{out}"
    );
    assert!(
        out.contains("for _, it in ipairs(items) do"),
        "single-use loop aliases should be inlined:\n{out}"
    );
    assert!(
        out.contains("panel:FindFirstChild(name)"),
        "single-use call argument aliases should be inlined:\n{out}"
    );
    assert!(
        !out.contains("local v3 = items") && !out.contains("local v4 = name"),
        "trivial parameter aliases should not survive cleanup:\n{out}"
    );
    assert!(
        recompiles(&out, "guards"),
        "guard output must recompile:\n{out}"
    );
}

#[test]
fn generated_stress_suite_recompiles_and_stays_readable() {
    let cases = generated_stress_sources();
    assert_eq!(cases.len(), 100);
    if !root().join("tools").join("luau-compile.exe").exists() {
        eprintln!("skipping: compiler not present");
        return;
    }

    for (name, source) in cases {
        let bytes = compile_inline_source(&name, &source).unwrap_or_else(|| {
            panic!("{name}: generated source did not compile:\n{source}");
        });
        let module = parse_and_validate(&bytes).unwrap();
        let out = decompile(&module);
        assert!(
            !out.partial,
            "{name}: generated case should be fully structured, notes={:?}\n{}",
            out.per_proto, out.source
        );
        assert_readable_nonpartial_output(&name, &out.source);
        assert!(
            recompiles(&out.source, &format!("generated_{name}")),
            "{name}: decompiled generated output must recompile:\n{}",
            out.source
        );
    }
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
        out.source.contains("return (value and value.icon) or"),
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
        "childCount = #workspace:GetChildren()",
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

#[test]
fn stripped_accumulators_get_readable_names() {
    let out =
        decompile(&parse_and_validate(&read_stripped("06_numeric_for.luauc")).unwrap()).source;
    assert!(
        out.contains("local total = 0"),
        "numeric sum accumulator should be named total:\n{out}"
    );
    assert!(
        !out.contains("local v1 = 0"),
        "synthetic accumulator name survived:\n{out}"
    );
    assert!(
        recompiles(&out, "stripped_accumulator_total"),
        "renamed accumulator output must recompile:\n{out}"
    );

    let out = decompile(&parse_and_validate(&read_stripped("05_repeat.luauc")).unwrap()).source;
    assert!(
        out.contains("local product = 1"),
        "multiplicative accumulator should be named product:\n{out}"
    );
    assert!(
        recompiles(&out, "stripped_accumulator_product"),
        "renamed product output must recompile:\n{out}"
    );
}

#[test]
fn stripped_index_reads_get_readable_names() {
    let out =
        decompile(&parse_and_validate(&read_stripped("20_loop_control.luauc")).unwrap()).source;
    assert!(
        out.contains("local value"),
        "dynamic index result should get a readable fallback name:\n{out}"
    );
    assert!(
        out.contains("value = p0[i]"),
        "indexed loop value should be renamed consistently:\n{out}"
    );
    assert!(
        !out.contains("v6 = p0[i]"),
        "synthetic index-read name survived:\n{out}"
    );
    assert!(
        recompiles(&out, "stripped_index_value"),
        "renamed index-read output must recompile:\n{out}"
    );
}

#[test]
fn overwritten_pure_temp_stores_are_removed() {
    let out = decompile(&parse_and_validate(&read("14_string_ops.luauc")).unwrap()).source;
    assert!(
        !out.contains("local floor = 1"),
        "dead register initializer survived before overwrite:\n{out}"
    );
    assert!(
        out.contains("return string.sub(s, 1, n), len, math.floor(n), math.max(n, len)"),
        "real assignment should be removed or inlined after dead-store removal:\n{out}"
    );
    assert!(
        recompiles(&out, "overwritten_debug_store"),
        "cleaned debug output must recompile:\n{out}"
    );

    let out = decompile(&parse_and_validate(&read_stripped("14_string_ops.luauc")).unwrap()).source;
    assert!(
        !out.contains("local v4 = 1"),
        "dead stripped register initializer survived before overwrite:\n{out}"
    );
    assert!(
        out.contains("return string.sub(p0, 1, p1), len, math.floor(p1), math.max(p1, len)"),
        "stripped math.floor result should be removed or inlined after dead-store removal:\n{out}"
    );
    assert!(
        recompiles(&out, "overwritten_stripped_store"),
        "cleaned stripped output must recompile:\n{out}"
    );
}

#[test]
fn overwritten_copy_stores_that_feed_calls_are_kept() {
    let out = decompile(&parse_and_validate(&read_stripped("13_multiret.luauc")).unwrap()).source;
    // With register splitting, the local register is split to v0_2, so we don't need a self-copy.
    // Instead, verify that v0(1, 2) is called correctly and assigned to a split version.
    assert!(
        out.contains("v0(1, 2)"),
        "outer function v0 must be called with args:\n{out}"
    );
    assert!(
        out.contains("local v0_2, v1"),
        "split locals should be declared for multi-return:\n{out}"
    );
    assert!(
        recompiles(&out, "overwritten_copy_store"),
        "copy-preserving output must recompile:\n{out}"
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

fn compile_stripped_inline_source(tag: &str, source: &str) -> Option<Vec<u8>> {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        return None;
    }
    let path = std::env::temp_dir().join(format!("luau_gen_strip_{tag}.luau"));
    fs::write(&path, source).unwrap();
    let output = Command::new(&luau)
        .arg("--binary")
        .arg("-O1")
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

#[test]
fn integration_naming_features() {
    let Some(_) = compile_inline_source("check", "return 1") else {
        eprintln!("skipping: compiler not present");
        return;
    };

    // 1. Strict self rules and plain helper receiver checks:
    let src = r#"
        local t = {}
        t.foo = function(self)
            return self:bar()
        end
        t.bar = function(p0)
            return p0.Name
        end
        return t
    "#;
    let bytes = compile_inline_source("strict_self", src).unwrap();
    let out = decompile(&parse_and_validate(&bytes).unwrap()).source;
    assert!(
        out.contains("function(self)"),
        "t.foo should use self:\n{out}"
    );
    assert!(
        out.contains("function(instance)"),
        "t.bar should keep instance (not self):\n{out}"
    );
    assert!(recompiles(&out, "strict_self"));

    // 2. Captured service local remains named correctly inside nested closure:
    let src_captured = r#"
        local Debris = game:GetService("Debris")
        local function outer()
            return function()
                Debris:AddItem(nil, 0)
            end
        end
        return outer
    "#;
    let bytes_captured = compile_inline_source("captured_service", src_captured).unwrap();
    let out_captured = decompile(&parse_and_validate(&bytes_captured).unwrap()).source;
    assert!(
        out_captured.contains("Debris:AddItem"),
        "nested closure should use Debris:\n{out_captured}"
    );
    assert!(recompiles(&out_captured, "captured_service"));

    // 3. Two vars both wanting 'child' become 'child', 'child2' (stripped)
    let src_child = r#"
        return function(p0)
            local v0 = p0:FindFirstChild("child")
            local v1 = p0:FindFirstChild("child")
            print(v0, v1)
            print(v0, v1)
            return v0, v1
        end
    "#;
    let bytes_child = compile_stripped_inline_source("child_dedup", src_child).unwrap();
    let out_child = decompile(&parse_and_validate(&bytes_child).unwrap()).source;
    assert!(
        out_child.contains("local child ="),
        "first child not renamed to child:\n{out_child}"
    );
    assert!(
        out_child.contains("local child2 ="),
        "second child not renamed to child2:\n{out_child}"
    );
    assert!(recompiles(&out_child, "child_dedup"));

    // 4. Loop variable names do not collide with locals/params
    let src_loop = r#"
        return function(i)
            local total = 0
            for j = 1, 10 do
                total = total + i + j
            end
            return total
        end
    "#;
    let bytes_loop = compile_inline_source("loop_collision", src_loop).unwrap();
    let out_loop = decompile(&parse_and_validate(&bytes_loop).unwrap()).source;
    assert!(recompiles(&out_loop, "loop_collision"));
}

#[test]
fn warning_header_conditional_on_remaining_gotos() {
    let src = "return function(x) return x + 1 end";
    let bytes = compile_inline_source("header_test", src).unwrap();
    let out = decompile(&parse_and_validate(&bytes).unwrap());
    assert!(
        !out.source.contains("Some regions use goto/labels"),
        "Warning header emitted for structured output:\n{}",
        out.source
    );
}

#[test]
fn rtween_bytecode_structures_without_gotos() {
    let path = root()
        .join("roblox-studio-cases")
        .join("in_game")
        .join("RTween_ModuleScript_Bytecode.luau");
    let bytes = fs::read(&path).unwrap();
    let (module, multiplier) = parse_normalized(&bytes).unwrap();
    assert_ne!(
        multiplier, 1,
        "RTween fixture should exercise Roblox opcode decoding"
    );
    let decompiled = decompile(&module);
    assert!(
        !decompiled.partial,
        "RTween bytecode should fully structure, reports={:?}\n{}",
        decompiled.per_proto, decompiled.source
    );
    assert!(
        !decompiled
            .source
            .contains("-- Some regions use goto/labels"),
        "RTween should not emit the goto warning:\n{}",
        decompiled.source
    );
    assert!(
        !decompiled.source.contains("goto ") && !decompiled.source.contains("::L"),
        "RTween output should not contain raw goto/labels:\n{}",
        decompiled.source
    );
    assert!(
        recompiles(&decompiled.source, "rtween"),
        "RTween output must recompile:\n{}",
        decompiled.source
    );
}

#[test]
fn elevators_capture_names_do_not_collapse_into_duplicate_conditions() {
    let path = root()
        .join("roblox-studio-cases")
        .join("in_game")
        .join("Elevators_ModuleScript_Bytecode.luau");
    let bytes = fs::read(&path).unwrap();
    let (module, _multiplier) = parse_normalized(&bytes).unwrap();
    let decompiled = decompile(&module);

    assert!(
        !decompiled.partial,
        "Elevators bytecode should fully structure, reports={:?}\n{}",
        decompiled.per_proto, decompiled.source
    );
    assert!(
        !decompiled.source.contains("goto ") && !decompiled.source.contains("::L"),
        "Elevators output should not contain raw goto/labels:\n{}",
        decompiled.source
    );
    assert!(
        duplicate_not_operand_in_while(&decompiled.source).is_none(),
        "captured upvalues must not collapse into duplicate while operands:\n{}",
        decompiled.source
    );
}

#[test]
fn in_game_bytecode_fixtures_decompile_without_panic() {
    let files = in_game_bytecode_files();
    assert!(
        !files.is_empty(),
        "expected in-game Roblox bytecode fixtures under roblox-studio-cases/in_game"
    );

    for path in files {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("in_game_fixture");
        let bytes = fs::read(&path).unwrap();
        let (module, _multiplier) = parse_normalized(&bytes).unwrap();
        let decompiled = decompile(&module);
        assert!(
            !decompiled.source.trim().is_empty(),
            "{name}: empty decompile output"
        );
    }
}

#[test]
#[ignore = "large Roblox bytecode fixtures are intentionally excluded from the default suite"]
fn in_game_large_bytecode_fixtures_decompile_without_panic() {
    let files = in_game_large_bytecode_files();
    assert!(
        !files.is_empty(),
        "expected large in-game Roblox bytecode fixtures under roblox-studio-cases/in_game"
    );

    for path in files {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("in_game_large_fixture");
        let bytes = fs::read(&path).unwrap();
        let (module, _multiplier) = parse_normalized(&bytes).unwrap();
        let decompiled = decompile(&module);
        assert!(
            !decompiled.source.trim().is_empty(),
            "{name}: empty decompile output"
        );
    }
}

#[test]
fn in_game_clean_bytecode_fixtures_stay_structured() {
    let files = in_game_bytecode_files();
    assert!(
        !files.is_empty(),
        "expected in-game Roblox bytecode fixtures under roblox-studio-cases/in_game"
    );

    for path in files {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("in_game_fixture");
        let bytes = fs::read(&path).unwrap();
        let (module, _multiplier) = parse_normalized(&bytes).unwrap();
        let decompiled = decompile(&module);
        assert!(
            !decompiled.partial,
            "{name}: expected fully structured output, reports={:?}\n{}",
            decompiled.per_proto, decompiled.source
        );
        assert!(
            !decompiled
                .source
                .contains("-- Some regions use goto/labels")
                && !decompiled.source.contains("goto ")
                && !decompiled.source.contains("::L"),
            "{name}: structured in-game fixture should not contain goto/labels:\n{}",
            decompiled.source
        );
        assert!(
            recompiles(&decompiled.source, name),
            "{name}: decompiled output must recompile:\n{}",
            decompiled.source
        );
    }
}

#[test]
fn in_game_fixture_discovery_includes_copied_bytecode_names() {
    let files = in_game_all_bytecode_files();
    if files.iter().any(|path| {
        path.file_name().and_then(|name| name.to_str())
            == Some("SharedData_ModuleScript_Bytecode copy.luau")
    }) {
        assert!(
            in_game_bytecode_files().iter().any(|path| {
                path.file_name().and_then(|name| name.to_str())
                    == Some("SharedData_ModuleScript_Bytecode copy.luau")
            }),
            "copied bytecode fixture names should be included in the default in-game fixture set"
        );
    }
}

#[test]
fn studio_25_quality_checks() {
    let luau = root().join("tools").join("luau-compile.exe");
    if !luau.exists() {
        return; // Skip if compiler is missing
    }

    let source_path = root()
        .join("roblox-studio-cases")
        .join("studio_25_cases.luau");
    let output = Command::new(&luau)
        .arg("--binary")
        .arg("-O1")
        .arg("-g2")
        .arg(&source_path)
        .output()
        .expect("run luau-compile");
    assert!(
        output.status.success(),
        "Failed to compile studio_25_cases.luau: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let decompiled = decompile(&parse_and_validate(&output.stdout).unwrap());

    // Assert: Studio 25 should be expected to fully structure
    if decompiled.partial {
        println!("Decompilation is partial! Printing proto reports:");
        for report in &decompiled.per_proto {
            println!(
                "Proto #{}: {:?} - partial={}, has_unstructured={}",
                report.index, report.name, report.partial, report.has_unstructured
            );
            for note in &report.notes {
                println!("  Note: {note}");
            }
        }
        panic!("studio_25_cases.luau should be fully structured, but decompile result is partial.");
    }

    let out = decompiled.source;

    // 1. Output compiles successfully
    assert!(
        recompiles(&out, "studio_25_cases"),
        "Decompiled studio_25_cases must recompile cleanly"
    );

    // 2. No warning header is emitted (since it structured fully)
    assert!(
        !out.contains("-- Some regions use goto/labels"),
        "Warning header should not be emitted when fully structured"
    );
    assert!(
        !out.contains("goto ") && !out.contains("::L"),
        "Studio 25 output should not contain raw goto/label fallback:\n{out}"
    );

    // 3. buttonLoopCapture preserves the captured button variable inside the closure
    assert!(
        out.contains("button.Name"),
        "buttonLoopCapture must preserve the captured button name:\n{out}"
    );

    // 4. evidenceConfig folds the Evidence table
    assert!(
        out.contains("Evidence = {"),
        "evidenceConfig must fold the Evidence table:\n{out}"
    );
    assert!(
        out.contains("evidenceTypes.GhostOrb"),
        "evidenceConfig must contain GhostOrb field reference:\n{out}"
    );

    // 5. signatureInput uses callback names like input
    assert!(
        out.contains("Connect(function(input)"),
        "signatureInput must use callback parameter input:\n{out}"
    );
    assert!(
        out.contains("addStroke(input)"),
        "signatureInput must keep the accepted mouse-move body:\n{out}"
    );
    assert!(
        out.contains("return Config.forCharacter(player.Character, root)"),
        "servicesAndRequires must keep the success-path return:\n{out}"
    );

    // 6. callbackChain keeps the loop-carried state update before the nil guard
    assert!(
        out.contains("current = callback(current)"),
        "callbackChain must preserve loop-carried callback state:\n{out}"
    );
    assert!(
        !out.contains("if callback(current) ~= nil then"),
        "callbackChain must not inline away the state update:\n{out}"
    );

    // 7. dataStoreRetry keeps the repeat condition instead of leaking temp comparisons
    assert!(
        compact_ws(&out).contains("until saved or tries >= 3"),
        "dataStoreRetry must recover the repeat-until condition:\n{out}"
    );
    assert!(
        !out.contains("v8 = 3"),
        "dataStoreRetry must not keep the temporary repeat-limit assignment:\n{out}"
    );
    assert!(
        out.contains("saved = ok"),
        "dataStoreRetry must preserve the pcall success assignment:\n{out}"
    );

    // 8. bodyPartCloneWeld/motorOrWeld do not keep dead class-string temps
    for marker in [
        "= \"Model\"",
        "= \"BasePart\"",
        "= \"UnionOperation\"",
        "= \"MeshPart\"",
        "= \"Middle\"",
    ] {
        assert!(
            !out.contains(marker),
            "dead class-string temp marker {marker} must not survive:\n{out}"
        );
    }

    // 9. No obvious dead assignment like map = table.insert survives
    assert!(
        !out.contains("map = table.insert"),
        "obvious dead table.insert assignment must not survive:\n{out}"
    );
    assert!(
        !out.contains("key = 60"),
        "pure store after a variable's last read must not survive:\n{out}"
    );
}

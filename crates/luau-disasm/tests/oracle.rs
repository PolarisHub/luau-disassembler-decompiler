//! Oracle test: our disassembly must match `luau-compile --text` instruction-for-
//! instruction across the whole corpus. This proves opcode decoding, AUX handling (PC
//! stays synced), operand resolution, constant rendering, and jump labelling are correct,
//! by diffing against Luau's own dumper.

use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;

use luau_bytecode::opcode::Opcode;
use luau_bytecode::parse_and_validate;
use luau_disasm::disassemble;

fn corpus() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
}

/// All opcode mnemonics, used to recognize instruction lines in `--text` output.
fn opcode_names() -> HashSet<String> {
    (0u8..=255)
        .filter_map(Opcode::from_u8)
        .map(|o| o.name().to_string())
        .collect()
}

/// Strip a leading `L<digits>: ` label prefix, returning the remainder if present.
fn strip_label(line: &str) -> Option<&str> {
    let rest = line.strip_prefix('L')?;
    let colon = rest.find(": ")?;
    if rest[..colon].chars().all(|c| c.is_ascii_digit()) && !rest[..colon].is_empty() {
        Some(&rest[colon + 2..])
    } else {
        None
    }
}

/// Extract just the instruction lines from `luau-compile --text` output: drop the
/// `Function` headers, `local ...` debug lines, source annotations (`<n>: <source>`), and
/// blanks. An instruction line is one whose first token (after an optional label prefix)
/// is an opcode mnemonic.
fn extract_instruction_lines(text: &str, names: &HashSet<String>) -> Vec<String> {
    let mut out = Vec::new();
    for raw in text.lines() {
        let line = raw.trim_end();
        if line.is_empty() {
            continue;
        }
        let body = strip_label(line).unwrap_or(line);
        let first = body.split_whitespace().next().unwrap_or("");
        if names.contains(first) {
            out.push(line.to_string());
        }
    }
    out
}

#[test]
fn disassembly_matches_luau_text_for_corpus() {
    let names = opcode_names();
    let bc_dir = corpus().join("bytecode");
    let txt_dir = corpus().join("expected-text");

    let mut entries: Vec<PathBuf> = fs::read_dir(&bc_dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "luauc").unwrap_or(false))
        .collect();
    entries.sort();
    assert!(!entries.is_empty(), "run scripts/compile-corpus.sh first");

    let mut failures = Vec::new();

    for bc in entries {
        let name = bc.file_stem().unwrap().to_string_lossy().into_owned();
        let bytes = fs::read(&bc).unwrap();
        let module = parse_and_validate(&bytes).unwrap_or_else(|e| panic!("{name}: {e}"));
        let mine = disassemble(&module).luau_text();
        let mine_lines: Vec<&str> = mine.lines().collect();

        let expected_text = fs::read_to_string(txt_dir.join(format!("{name}.txt"))).unwrap();
        let expected_lines = extract_instruction_lines(&expected_text, &names);

        if mine_lines.len() != expected_lines.len() {
            failures.push(format!(
                "{name}: line count {} (mine) vs {} (luau)",
                mine_lines.len(),
                expected_lines.len()
            ));
        }
        for (i, (a, b)) in mine_lines.iter().zip(expected_lines.iter()).enumerate() {
            if a != b {
                failures.push(format!("{name}[{i}]: mine={a:?} luau={b:?}"));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "disassembly diverged from luau-compile --text:\n{}",
        failures.join("\n")
    );
}

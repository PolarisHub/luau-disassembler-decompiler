//! Snapshot test for the human-readable listing (the Stage 2 deliverable). Golden files
//! live in `corpus/expected-disasm/`. Regenerate them with:
//!   LUAU_UPDATE_SNAPSHOTS=1 cargo test -p luau-disasm --test snapshot
//! A diff against the committed golden is a signal that decoding or formatting changed.

use std::fs;
use std::path::PathBuf;

use luau_bytecode::parse_and_validate;
use luau_disasm::disassemble;

fn corpus() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
}

#[test]
fn human_listing_snapshots() {
    let update = std::env::var("LUAU_UPDATE_SNAPSHOTS").is_ok();
    let bc_dir = corpus().join("bytecode");
    let snap_dir = corpus().join("expected-disasm");
    fs::create_dir_all(&snap_dir).unwrap();

    let mut entries: Vec<PathBuf> = fs::read_dir(&bc_dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "luauc").unwrap_or(false))
        .collect();
    entries.sort();

    let mut mismatches = Vec::new();
    for bc in entries {
        let name = bc.file_stem().unwrap().to_string_lossy().into_owned();
        let bytes = fs::read(&bc).unwrap();
        let module = parse_and_validate(&bytes).unwrap();
        // Normalize line endings so the golden is stable across platforms.
        let listing = disassemble(&module).to_string().replace("\r\n", "\n");

        let golden = snap_dir.join(format!("{name}.disasm.txt"));
        if update || !golden.exists() {
            fs::write(&golden, &listing).unwrap();
            continue;
        }
        let expected = fs::read_to_string(&golden).unwrap().replace("\r\n", "\n");
        if expected != listing {
            mismatches.push(name);
        }
    }

    assert!(
        mismatches.is_empty(),
        "listing changed for: {} (set LUAU_UPDATE_SNAPSHOTS=1 to refresh)",
        mismatches.join(", ")
    );
}

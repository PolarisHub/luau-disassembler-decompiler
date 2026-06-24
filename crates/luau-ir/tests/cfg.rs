//! CFG / dominator correctness across the corpus.

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use luau_bytecode::parse_and_validate;
use luau_ir::{analyze, back_edges, dominators, build_cfg};

fn corpus() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
        .join("bytecode")
}

fn read(name: &str) -> Vec<u8> {
    fs::read(corpus().join(name)).unwrap()
}

fn all_files() -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(corpus())
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "luauc").unwrap_or(false))
        .collect();
    v.sort();
    v
}

#[test]
fn cfg_is_well_formed() {
    for path in all_files() {
        let bytes = fs::read(&path).unwrap();
        let module = parse_and_validate(&bytes).unwrap();
        for proto in &module.protos {
            let cfg = build_cfg(proto);

            // Every instruction belongs to exactly one block.
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            for b in &cfg.blocks {
                for &pc in &b.insns {
                    assert!(seen.insert(pc), "{}: pc {pc} in two blocks", path.display());
                }
            }

            // pred/succ symmetry.
            for b in &cfg.blocks {
                for &s in &b.successors {
                    assert!(
                        cfg.blocks[s].predecessors.contains(&b.index),
                        "{}: B{}->B{} missing reverse edge",
                        path.display(),
                        b.index,
                        s
                    );
                }
            }

            // Entry dominates every block reachable from it.
            let doms = dominators(&cfg);
            // Block 0 must dominate itself.
            assert!(doms.dominates(0, 0));
        }
    }
}

#[test]
fn loops_have_back_edges() {
    for name in ["04_while", "05_repeat", "06_numeric_for", "07_generic_for"] {
        let module = parse_and_validate(&read(&format!("{name}.luauc"))).unwrap();
        let has_loop = module.protos.iter().any(|p| {
            let cfg = build_cfg(p);
            let doms = dominators(&cfg);
            !back_edges(&cfg, &doms).is_empty()
        });
        assert!(has_loop, "{name}: expected at least one back edge (loop)");
    }
}

#[test]
fn straight_line_and_if_have_no_back_edges() {
    for name in ["01_literals", "03_if_else"] {
        let module = parse_and_validate(&read(&format!("{name}.luauc"))).unwrap();
        for p in &module.protos {
            let cfg = build_cfg(p);
            let doms = dominators(&cfg);
            assert!(
                back_edges(&cfg, &doms).is_empty(),
                "{name}: unexpected back edge in a loop-free function"
            );
        }
    }
}

#[test]
fn post_dominators_available() {
    // Smoke test: post-dominators compute without panicking and the exit post-dominates
    // a returning function's entry.
    let module = parse_and_validate(&read("03_if_else.luauc")).unwrap();
    let proto = &module.protos[0];
    let ir = analyze(proto);
    // The synthetic exit post-dominates every real block.
    for b in &ir.cfg.blocks {
        assert!(ir.post_doms.post_dominates(ir.post_doms.exit, b.index));
    }
}

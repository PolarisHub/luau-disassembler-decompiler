//! `luau-ir`: control-flow graph and the analyses the decompiler structures on top of —
//! basic blocks, dominators, post-dominators, and natural loops.

pub mod cfg;
pub mod dom;

pub use cfg::{build_cfg, BasicBlock, Cfg, Terminator};
pub use dom::{back_edges, dominators, natural_loop, post_dominators, Doms, PostDoms};

use luau_bytecode::{Module, Proto};
use luau_disasm::{compute_labels, format_instruction};

/// Everything the decompiler needs for one proto, computed once.
pub struct ProtoIr {
    pub cfg: Cfg,
    pub doms: Doms,
    pub post_doms: PostDoms,
    pub back_edges: Vec<(usize, usize)>,
}

pub fn analyze(proto: &Proto) -> ProtoIr {
    let cfg = build_cfg(proto);
    let doms = dominators(&cfg);
    let post_doms = post_dominators(&cfg);
    let back = back_edges(&cfg, &doms);
    ProtoIr {
        cfg,
        doms,
        post_doms,
        back_edges: back,
    }
}

/// A readable block listing: each block with its successors, back-edge markers, and its
/// resolved instructions. This is the Stage 3 deliverable.
pub fn block_listing(module: &Module, proto: &Proto) -> String {
    let ir = analyze(proto);
    let labels = compute_labels(proto);
    let back: std::collections::HashSet<(usize, usize)> = ir.back_edges.iter().copied().collect();

    let mut out = String::new();
    for b in &ir.cfg.blocks {
        let succ: Vec<String> = b
            .successors
            .iter()
            .map(|&s| {
                if back.contains(&(b.index, s)) {
                    format!("B{s}(back)")
                } else {
                    format!("B{s}")
                }
            })
            .collect();
        out.push_str(&format!(
            "B{} [pc {}..{}] idom=B{} -> {}\n",
            b.index,
            b.start_pc,
            b.end_pc,
            ir.doms.idom[b.index],
            if succ.is_empty() {
                "(exit)".to_string()
            } else {
                succ.join(", ")
            }
        ));
        for &pc in &b.insns {
            let label = match labels.get(pc).copied().flatten() {
                Some(id) => format!("L{id}:"),
                None => String::new(),
            };
            out.push_str(&format!(
                "    {:>5}  {:<5}{}\n",
                pc,
                label,
                format_instruction(module, proto, pc, &labels)
            ));
        }
    }
    out
}

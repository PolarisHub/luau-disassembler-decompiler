//! Dominators, post-dominators, and natural-loop (back-edge) detection.
//!
//! Uses the Cooper–Harvey–Kennedy iterative dominator algorithm, which is simple and fast
//! for the small CFGs a single proto produces. Post-dominators are the same algorithm run
//! on the reversed CFG with a synthetic exit node joining every return / sink block.

use std::collections::BTreeSet;

use crate::cfg::Cfg;

#[derive(Debug, Clone)]
pub struct Doms {
    /// Immediate dominator of each block; the entry's idom is itself.
    pub idom: Vec<usize>,
}

impl Doms {
    /// Does block `a` dominate block `b` (a == b counts)?
    pub fn dominates(&self, a: usize, b: usize) -> bool {
        let mut x = b;
        loop {
            if x == a {
                return true;
            }
            let up = self.idom[x];
            if up == x {
                return false; // reached entry
            }
            x = up;
        }
    }
}

/// Depth-first reverse-postorder of nodes reachable from `entry`, given a successor list.
fn reverse_postorder(n: usize, entry: usize, succ: &[Vec<usize>]) -> Vec<usize> {
    let mut visited = vec![false; n];
    let mut post = Vec::new();
    // Iterative DFS with an explicit stack of (node, next-child-index).
    let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
    visited[entry] = true;
    while let Some(&mut (node, ref mut ci)) = stack.last_mut() {
        if *ci < succ[node].len() {
            let next = succ[node][*ci];
            *ci += 1;
            if !visited[next] {
                visited[next] = true;
                stack.push((next, 0));
            }
        } else {
            post.push(node);
            stack.pop();
        }
    }
    post.reverse();
    post
}

fn compute(n: usize, entry: usize, preds: &[Vec<usize>], succ: &[Vec<usize>]) -> Doms {
    let rpo = reverse_postorder(n, entry, succ);
    let mut rpo_index = vec![usize::MAX; n];
    for (i, &b) in rpo.iter().enumerate() {
        rpo_index[b] = i;
    }

    // idom: usize::MAX means "undefined" for now.
    let mut idom = vec![usize::MAX; n];
    idom[entry] = entry;

    let intersect = |mut a: usize, mut b: usize, idom: &[usize], rpo_index: &[usize]| -> usize {
        while a != b {
            while rpo_index[a] > rpo_index[b] {
                a = idom[a];
            }
            while rpo_index[b] > rpo_index[a] {
                b = idom[b];
            }
        }
        a
    };

    let mut changed = true;
    while changed {
        changed = false;
        for &b in &rpo {
            if b == entry {
                continue;
            }
            let mut new_idom = usize::MAX;
            for &p in &preds[b] {
                if idom[p] == usize::MAX {
                    continue; // predecessor not processed yet
                }
                new_idom = if new_idom == usize::MAX {
                    p
                } else {
                    intersect(p, new_idom, &idom, &rpo_index)
                };
            }
            if new_idom != usize::MAX && idom[b] != new_idom {
                idom[b] = new_idom;
                changed = true;
            }
        }
    }

    // Unreachable blocks keep idom == MAX; point them at themselves so callers don't index
    // out of range. They have no bearing on real control flow.
    for b in 0..n {
        if idom[b] == usize::MAX {
            idom[b] = b;
        }
    }

    Doms { idom }
}

/// Dominators of the forward CFG from the entry block.
pub fn dominators(cfg: &Cfg) -> Doms {
    let n = cfg.blocks.len();
    let succ: Vec<Vec<usize>> = cfg.blocks.iter().map(|b| b.successors.clone()).collect();
    let preds: Vec<Vec<usize>> = cfg.blocks.iter().map(|b| b.predecessors.clone()).collect();
    compute(n, cfg.entry, &preds, &succ)
}

/// Post-dominators: dominators of the reversed CFG. Returns a `Doms` over `n+1` nodes where
/// node `n` is the synthetic exit; block post-dominance is `pdoms.dominates(n_exit=.., ..)`
/// restricted to real blocks. For convenience we also return the exit node id.
pub struct PostDoms {
    pub doms: Doms,
    pub exit: usize,
}

impl PostDoms {
    /// Does block `a` post-dominate block `b`?
    pub fn post_dominates(&self, a: usize, b: usize) -> bool {
        self.doms.dominates(a, b)
    }
}

pub fn post_dominators(cfg: &Cfg) -> PostDoms {
    let real = cfg.blocks.len();
    let exit = real; // synthetic exit node
    let n = real + 1;

    // Reversed edges: for forward edge u->v, add v->u. Sinks (no successors, e.g. RETURN)
    // get an edge from the synthetic exit so the reversed graph is rooted at `exit`.
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    let add = |from: usize, to: usize, succ: &mut Vec<Vec<usize>>, preds: &mut Vec<Vec<usize>>| {
        succ[from].push(to);
        preds[to].push(from);
    };
    for b in &cfg.blocks {
        if b.successors.is_empty() {
            add(exit, b.index, &mut succ, &mut preds);
        }
        for &s in &b.successors {
            add(s, b.index, &mut succ, &mut preds);
        }
    }

    let doms = compute(n, exit, &preds, &succ);
    PostDoms { doms, exit }
}

/// Back edges: edges `u -> v` where the target `v` dominates the source `u`. Each indicates
/// a natural loop with header `v`.
pub fn back_edges(cfg: &Cfg, doms: &Doms) -> Vec<(usize, usize)> {
    let mut edges = Vec::new();
    for b in &cfg.blocks {
        for &s in &b.successors {
            if doms.dominates(s, b.index) {
                edges.push((b.index, s));
            }
        }
    }
    edges
}

/// The set of blocks in the natural loop of back edge `(tail -> header)`: the header plus
/// every block that can reach `tail` without going through the header.
pub fn natural_loop(cfg: &Cfg, tail: usize, header: usize) -> BTreeSet<usize> {
    let mut body = BTreeSet::new();
    body.insert(header);
    let mut stack = vec![tail];
    while let Some(b) = stack.pop() {
        if body.insert(b) {
            for &p in &cfg.blocks[b].predecessors {
                stack.push(p);
            }
        }
    }
    body
}

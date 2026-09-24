//! What a body's control flow says about the panics it raises.

use rustc_middle::mir::{self, BasicBlock, TerminatorKind};

use crate::fold;

/// Which blocks of a body can reach an `UnwindResume`, by block index.
///
/// A cleanup path that aborts instead keeps the panic in the function. The
/// walk runs backwards from each resumption and marks each block once.
pub(super) fn resuming(mir: &mir::Body<'_>) -> Vec<bool> {
    let mut out = vec![false; mir.basic_blocks.len()];
    let mut stack: Vec<BasicBlock> = Vec::new();
    for (bb, data) in mir.basic_blocks.iter_enumerated() {
        let resumes = data.terminator.as_ref().is_some_and(|term| {
            matches!(term.kind, TerminatorKind::UnwindResume)
        });
        if resumes && let Some(slot) = out.get_mut(bb.as_usize()) {
            *slot = true;
            stack.push(bb);
        }
    }
    let predecessors = mir.basic_blocks.predecessors();
    while let Some(bb) = stack.pop() {
        let Some(from) = predecessors.get(bb) else {
            continue;
        };
        for &pred in from {
            if let Some(slot) = out.get_mut(pred.as_usize())
                && !*slot
            {
                *slot = true;
                stack.push(pred);
            }
        }
    }
    out
}

/// Whether every execution of a body that gets past its entry runs one
/// block.
///
/// Every path from the entry through live blocks is followed while it
/// avoids the block. Reaching a way out of the body shows the block can
/// be got round, and so does closing a loop, since a loop the walk cannot
/// prove finite might spin instead. The walk enters each block once, so
/// it is bounded by the edges of the body.
pub(super) fn unavoidable(
    mir: &mir::Body<'_>,
    reach: &fold::Reach,
    avoid: BasicBlock,
) -> bool {
    const NEW: u8 = 0;
    const OPEN: u8 = 1;
    const DONE: u8 = 2;
    let blocks = mir.basic_blocks.len();
    let mut state = vec![NEW; blocks];
    let mut stack: Vec<(BasicBlock, usize)> = vec![(mir::START_BLOCK, 0)];
    if let Some(slot) = state.get_mut(mir::START_BLOCK.as_usize()) {
        *slot = OPEN;
    }
    let edges: usize = mir
        .basic_blocks
        .iter()
        .map(|data| data.terminator().successors().count())
        .sum();
    for _ in 0..edges.saturating_add(blocks).saturating_add(1) {
        let Some(&(bb, next)) = stack.last() else {
            return true;
        };
        let term = mir.basic_blocks[bb].terminator();
        if matches!(
            term.kind,
            TerminatorKind::Return
                | TerminatorKind::TailCall { .. }
                | TerminatorKind::Yield { .. }
        ) {
            return false;
        }
        let Some(succ) = term.successors().nth(next) else {
            if let Some(slot) = state.get_mut(bb.as_usize()) {
                *slot = DONE;
            }
            stack.pop();
            continue;
        };
        if let Some(top) = stack.last_mut() {
            top.1 = next.saturating_add(1);
        }
        if succ == avoid || !reach.is_live(succ) {
            continue;
        }
        match state.get(succ.as_usize()).copied() {
            Some(OPEN) => return false,
            Some(NEW) => {
                if let Some(slot) = state.get_mut(succ.as_usize()) {
                    *slot = OPEN;
                }
                stack.push((succ, 0));
            }
            _ => {}
        }
    }
    false
}

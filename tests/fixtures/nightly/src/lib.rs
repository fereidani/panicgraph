//! Unstable syntax, kept apart from the main fixture so a change to these
//! features breaks only this crate.

#![feature(asm_unwind, explicit_tail_calls)]
#![allow(incomplete_features)]

/// Indexes.
#[inline(never)]
pub fn index_at(v: &[u8], i: usize) -> u8 {
    v[i]
}

/// Reaches `index` through a tail call.
pub fn must_index_by_tail_call(v: &[u8], i: usize) -> u8 {
    become index_at(v, i)
}

/// Reaches `foreign`: unwinding assembly may run code that panics.
pub fn must_run_unwinding_assembly() {
    // SAFETY: the template is empty.
    unsafe { core::arch::asm!("", options(may_unwind)) }
}

/// Clean. This assembly cannot unwind.
pub fn clean_run_assembly() {
    // SAFETY: the template is empty.
    unsafe { core::arch::asm!("", options(nomem, nostack)) }
}

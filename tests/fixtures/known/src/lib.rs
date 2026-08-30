//! A crate whose panics are known, used to pin what the analysis reports.
//!
//! Every function is named for the answer it must produce. A `must_` function
//! reaches the panic its name gives; a `clean_` function reaches none. The
//! clean ones are the interesting half: each is code the compiler proves safe
//! and a naive reading of MIR does not.

/// Reaches `index`.
pub fn must_index(v: &[u8], i: usize) -> u8 {
    v[i]
}

/// Reaches `divide-by-zero`, since the divisor is a runtime value.
pub fn must_divide(a: u32, b: u32) -> u32 {
    a / b
}

/// Reaches `remainder-by-zero`, since the divisor is a runtime value.
pub fn must_remainder(a: u32, b: u32) -> u32 {
    a % b
}

/// Reaches `unwrap`.
pub fn must_unwrap(o: Option<u8>) -> u8 {
    o.unwrap()
}

/// Reaches `explicit`, since the condition is a runtime comparison.
pub fn must_assert(a: u32, b: u32) {
    assert!(a < b, "a must be below b");
}

/// Reaches `index` through the subtraction in the range.
pub fn must_slice_tail(v: &[u8]) -> &[u8] {
    &v[v.len() - 2..]
}

/// Reaches `explicit` through the length check in `copy_from_slice`.
pub fn must_copy(dst: &mut [u8], src: &[u8]) {
    dst.copy_from_slice(src);
}

/// Reaches `explicit`. The assertion is about the length, which no constant
/// settles, so it survives folding.
pub fn must_assert_generic<T>(v: &[T]) {
    assert!(!v.is_empty(), "the slice must not be empty");
}

/// Reaches `explicit`. The assertion is false for this size, and a check
/// that always fails is still a panic.
pub fn must_assert_false() -> usize {
    assert!(size_of::<u32>() == 8);
    size_of::<u32>()
}

/// Clean. The divisor is a constant the analysis can settle.
pub fn clean_divide_by_constant(a: u32) -> u32 {
    a / 7
}

/// Clean. Walking a slice reaches the pointer distance check inside the
/// standard library, which holds for every sized element type.
pub fn clean_fold(v: &[u8]) -> u8 {
    v.iter().fold(0u8, |a, b| a.wrapping_add(*b))
}

/// Clean. Iterating by reference indexes nothing.
pub fn clean_count_zeros(v: &[u8]) -> usize {
    let mut n = 0usize;
    for byte in v {
        if *byte == 0 {
            n = n.wrapping_add(1);
        }
    }
    n
}

/// Clean. A checked read and a wrapping counter.
pub fn clean_sum_by_get(v: &[u8]) -> u8 {
    let mut total = 0u8;
    let mut i = 0usize;
    while let Some(byte) = v.get(i) {
        total = total.wrapping_add(*byte);
        i = i.wrapping_add(1);
    }
    total
}

/// Clean. The assertion holds for this size.
pub fn clean_assert_true() -> usize {
    assert!(size_of::<u32>() == 4);
    size_of::<u32>()
}

/// Clean. The guard settles the divisor before the division reads it.
pub fn clean_guarded_divide(a: u32, b: u32) -> u32 {
    if b == 0 { 0 } else { a / b }
}

/// Clean. The same guard, written the other way round.
pub fn clean_guarded_divide_ne(a: u32, b: u32) -> Option<u32> {
    if b != 0 { Some(a / b) } else { None }
}

/// Clean. An early return settles the divisor for the rest of the body.
pub fn clean_guarded_remainder(a: u64, b: u64) -> u64 {
    if b == 0 {
        return 0;
    }
    a % b
}

/// Reaches `divide-by-zero`. The guard is on a different value, so it says
/// nothing about the divisor.
pub fn must_divide_misguarded(a: u32, b: u32, c: u32) -> u32 {
    if c != 0 { a / b } else { 0 }
}

/// Reaches `divide-by-zero`. The guard admits only the arm that divides by
/// zero, so the check fails every time rather than never.
pub fn must_divide_inverted_guard(a: u32, b: u32) -> u32 {
    if b == 0 { a / b } else { 0 }
}

/// Reaches `divide-by-zero` but not `remainder-by-zero`: the remainder is
/// free once the division above it has passed the same check.
pub fn must_divide_once_of_two(a: u32, b: u32) -> u32 {
    let quotient = a / b;
    let remainder = a % b;
    quotient.wrapping_add(remainder)
}

/// Clean. The guard survives a cast that cannot lose information.
pub fn clean_guarded_widening(a: u64, b: u32) -> u64 {
    if b == 0 { 0 } else { a / u64::from(b) }
}

/// Reaches `divide-by-zero`. A narrowing cast can turn a value the guard
/// admitted into zero.
pub fn must_divide_narrowed(a: u8, b: u32) -> u8 {
    if b == 0 { 0 } else { a / (b as u8) }
}

/// Reaches `capacity-overflow` and `alloc-failure`. Growth funnels through
/// one entry point that raises either, decided at run time, so a report of
/// only one would let suppressing it clear the other.
pub fn must_push(v: &mut Vec<u8>, x: u8) {
    v.push(x);
}

/// Reaches `explicit`. Raising a caught payload again is a panic in its own
/// right, named rather than reported as a call into unknown code.
pub fn must_rethrow(r: Result<u8, Box<dyn std::any::Any + Send>>) -> u8 {
    match r {
        Ok(v) => v,
        Err(e) => std::panic::resume_unwind(e),
    }
}

/// Reaches `poison`, not `unwrap`: the error the unwrap discards names the
/// panic, and a poisoned lock is its own category.
pub fn must_lock(m: &std::sync::Mutex<u32>) -> u32 {
    *m.lock().unwrap()
}

/// Reaches `fmt`, not `unwrap`: what is unwrapped is the error a formatting
/// trait implementation returned.
pub fn must_write(x: u32) -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    write!(s, "{x}").unwrap();
    s
}

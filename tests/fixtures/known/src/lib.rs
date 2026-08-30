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

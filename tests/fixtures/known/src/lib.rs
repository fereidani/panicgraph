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

/// Reaches `refcount-overflow`: cloning aborts when the strong count would
/// wrap, and an abort raised by the counting machinery is that category.
pub fn must_rc_clone(rc: &std::rc::Rc<u32>) -> std::rc::Rc<u32> {
    rc.clone()
}

/// Reaches `str-boundary`: the end is a runtime value that can split a
/// character.
pub fn must_slice_str(s: &str, end: usize) -> &str {
    &s[..end]
}

/// Reaches `borrow`.
pub fn must_borrow(c: &std::cell::RefCell<u32>) -> u32 {
    *c.borrow()
}

/// Reaches `dyn-call`: the target set of a dynamic call is not resolved.
pub fn must_dyn(f: &dyn Fn() -> u8) -> u8 {
    f()
}

/// Reaches `foreign`: the callee has no Rust body to read.
pub fn must_foreign(x: u32) -> u32 {
    unsafe extern "C" {
        fn known_external(x: u32) -> u32;
    }
    unsafe { known_external(x) }
}

/// Does not reach `explicit`: the assertion in the closure unwinds only as
/// far as the catch. What remains reachable is the catch machinery itself.
pub fn must_not_catch_explicit(x: u32) -> u32 {
    std::panic::catch_unwind(move || {
        assert!(x < 10, "x is too big");
        x
    })
    .unwrap_or(0)
}

/// Reaches `alloc-failure` through the catch: an aborting panic does not
/// unwind, so no catch can contain it.
pub fn must_catch_abort(x: u32) -> u32 {
    std::panic::catch_unwind(move || *Box::new(x)).unwrap_or(0)
}

/// Clean. The remainder of anything by eight lies below eight.
pub fn clean_modulo_index(v: &[u8; 8], i: usize) -> u8 {
    v[i % 8]
}

/// Clean. A mask with no sign bit pins the index below the length.
pub fn clean_masked_index(v: &[u8; 4], i: usize) -> u8 {
    v[i & 3]
}

/// Clean. The guard compares against the length the check reads.
pub fn clean_guarded_index(v: &[u8], i: usize) -> u8 {
    if i < v.len() { v[i] } else { 0 }
}

/// Clean. The same guard, written the other way round.
pub fn clean_guarded_index_flipped(v: &[u8], i: usize) -> u8 {
    if v.len() > i { v[i] } else { 0 }
}

/// Clean. The loop's own condition proves each read in range.
pub fn clean_while_index(v: &[u8]) -> u32 {
    let mut total = 0u32;
    let mut i = 0usize;
    while i < v.len() {
        total = total.wrapping_add(u32::from(v[i]));
        i = i.wrapping_add(1);
    }
    total
}

/// Reaches `index`: the guard admits an index one past the end.
pub fn must_index_off_by_one(v: &[u8], i: usize) -> u8 {
    if i <= v.len() { v[i] } else { 0 }
}

/// Reaches `index`: the guard measures a different slice.
pub fn must_index_wrong_slice(a: &[u8], b: &[u8], i: usize) -> u8 {
    if i < a.len() { b[i] } else { 0 }
}

/// Reaches `index`: a signed remainder can be negative, and the cast wraps
/// it far past the end.
pub fn must_modulo_signed(v: &[u8; 8], i: isize) -> u8 {
    v[(i % 8) as usize]
}

/// Clean. The value inside a nonzero is never zero, so the division's own
/// check cannot fail.
pub fn clean_nonzero_divide(a: u32, b: std::num::NonZeroU32) -> u32 {
    a / b.get()
}

/// Reaches `fn-pointer`: the target of the call is whatever the pointer
/// holds.
pub fn must_fn_ptr(f: fn() -> u8) -> u8 {
    f()
}

/// Reaches `generic-bound`: which implementation runs is decided by the
/// caller that picks the type.
pub fn must_generic<T: std::fmt::Display>(x: T) -> String {
    x.to_string()
}

/// A trait with one loud and one quiet implementation, for the candidate
/// expansion below.
pub trait Speak {
    fn speak(&self) -> u8;
}

pub struct Quiet;
impl Speak for Quiet {
    fn speak(&self) -> u8 {
        0
    }
}

pub struct Loud;
impl Speak for Loud {
    fn speak(&self) -> u8 {
        panic!("loud")
    }
}

/// Reaches `dyn-call` always, and `explicit` once candidates are followed:
/// one implementation of the trait panics.
pub fn must_dyn_speak(s: &dyn Speak) -> u8 {
    s.speak()
}

/// The panicking target a reified pointer can name.
fn loud_pointer_target() -> u8 {
    panic!("via pointer")
}

/// Names a panicking function, so a pointer of its signature exists and
/// every call through such a pointer gains it as a candidate.
pub fn reifies_loud() -> fn() -> u8 {
    loud_pointer_target
}

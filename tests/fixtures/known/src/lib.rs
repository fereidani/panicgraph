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

/// Reaches `index`: neither length was measured against this slice, so
/// nothing here proves the read is in range. Both lengths carry an ordering
/// and a length claim at once, which is what the folder has to compare
/// without exchanging the operands back and forth forever.
pub fn must_two_lengths(a: &[u8], b: &[u8], c: &[u8], d: &[u8]) -> u8 {
    let n = a.len();
    let m = b.len();
    if n < c.len() && m < d.len() && n == m { a[0] } else { 0 }
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

/// Reaches `explicit`: a zeroed reference is invalid, and the guard on the
/// instantiation aborts in every build.
pub fn must_zeroed_ref() -> u8 {
    let r: &'static u8 = unsafe { std::mem::zeroed() };
    *r
}

/// Clean. A zeroed integer is a valid integer, so no check is emitted.
pub fn clean_zeroed_int() -> u32 {
    unsafe { std::mem::zeroed() }
}

/// Reaches `index` at the language level; the index comes back out of an
/// iterator the folder does not read, and the optimizer proves it in range
/// and keeps no check, which the verifying sweep must say.
pub fn verify_absent_loop(v: &[u8; 16]) -> u32 {
    let mut s = 0u32;
    for (i, _) in v.iter().enumerate() {
        s = s.wrapping_add(u32::from(v[i]));
    }
    s
}

/// Clean. The counter is bounded by the length the read is checked against,
/// and the bound survives every turn of the loop.
pub fn clean_range_loop(v: &[u8]) -> u32 {
    let mut s = 0u32;
    for i in 0..v.len() {
        s = s.wrapping_add(u32::from(v[i]));
    }
    s
}

/// Reaches `explicit`, and the report quotes the message the panic
/// carries.
pub fn must_panic_literal(x: u32) -> u32 {
    if x > 10 {
        panic!("x is too big");
    }
    x
}

/// The frames below carry a caller's third parameter into a two parameter
/// frame. The validity check on the zeroed instantiation must read the
/// resolved argument as it is: instantiating it again against the inner
/// frame asks for a parameter that frame does not have.
pub struct Wrap<'w, T>(&'w (), std::marker::PhantomData<T>);

impl<T> Wrap<'_, T> {
    #[inline(never)]
    fn make(&self) -> T {
        unsafe { std::mem::zeroed() }
    }
}

/// Reaches `generic-bound`: whether the zeroed instantiation is valid is
/// decided by the caller's choice of type.
pub fn must_zeroed_chain<P, Q, T>(_p: &P, _q: &Q, w: &Wrap<'_, T>) -> T {
    w.make()
}

/// Clean. The divisor is at least one whatever the argument holds, which is
/// a fact about what `max` returns rather than anything written here.
pub fn clean_divide_by_max(a: u64, b: u64) -> u64 {
    a / b.max(1)
}

/// Reaches `divide-by-zero`. Raising a floor to zero raises nothing, so the
/// divisor is still whatever was passed in.
pub fn must_divide_by_max_zero(a: u64, b: u64) -> u64 {
    a / b.max(0)
}

/// Clean. The remainder's divisor is held away from zero the same way.
pub fn clean_remainder_by_max(a: u64, b: u64) -> u64 {
    a % b.max(1)
}

/// Clean. A ceiling of nine leaves a divisor between one and ten.
pub fn clean_divide_by_min_plus_one(a: u64, b: u64) -> u64 {
    a / (b.min(9) + 1)
}

/// Reaches `divide-by-zero`. A ceiling says nothing about the floor.
pub fn must_divide_by_min(a: u64, b: u64) -> u64 {
    a / b.min(9)
}

/// Clean. Clamping pins the divisor inside a range that excludes zero.
pub fn clean_divide_by_clamp(a: u64, b: u64) -> u64 {
    a / b.clamp(1, 100)
}

/// Raises the floor of a value to one.
fn at_least_one(x: u64) -> u64 {
    if x == 0 { 1 } else { x }
}

/// Clean. What a function returns is read from its body, so a divisor a
/// call holds away from zero settles the check a guard would have settled.
pub fn clean_divide_by_helper(a: u64, b: u64) -> u64 {
    a / at_least_one(b)
}

/// Clean. Each arm of the branch leaves a divisor of at least one, and the
/// range where they meet holds both.
pub fn clean_divide_by_either_arm(a: u64, b: u64) -> u64 {
    let divisor = if b > 10 { b } else { 1 };
    a / divisor
}

/// Clean. The guard proves the slice is not empty, and the length carries
/// that to the read below, which measures it again.
pub fn clean_index_after_empty_guard(v: &[u8]) -> u8 {
    if v.is_empty() { 0 } else { v[0] }
}

/// Clean. A length of at least four admits every index below four.
pub fn clean_index_after_length_guard(v: &[u8]) -> u8 {
    if v.len() >= 4 { v[3] } else { 0 }
}

/// Reaches `index`. A length of at least three does not admit a fourth
/// element.
pub fn must_index_past_length_guard(v: &[u8]) -> u8 {
    if v.len() >= 3 { v[3] } else { 0 }
}

/// Reaches `remainder-by-zero` but not `index`: a remainder by a length
/// lands inside the slice, and an empty one is caught by the remainder's
/// own check.
pub fn must_modulo_length(v: &[u8], i: usize) -> u8 {
    v[i % v.len()]
}

/// Clean. A masked index raised by four stays inside eight elements.
pub fn clean_masked_index_offset(v: &[u8; 8], i: usize) -> u8 {
    v[(i & 3) + 4]
}

/// Reaches `index`. The same mask raised one further leaves the slice.
pub fn must_masked_index_offset(v: &[u8; 8], i: usize) -> u8 {
    v[(i & 3) + 5]
}

/// Reaches `explicit`. Refuses anything at or above the limit.
fn must_be_below(x: u64, limit: u64) -> u64 {
    assert!(x < limit, "x must be below the limit");
    x
}

/// Clean. The callee's own check holds for the arguments this call makes,
/// so nothing it could raise is reachable from here.
pub fn clean_precondition_met() -> u64 {
    must_be_below(3, 10)
}

/// Reaches `explicit`. Which way the callee's check goes is decided by
/// values this caller does not settle.
pub fn must_pass_unchecked_limit(x: u64, limit: u64) -> u64 {
    must_be_below(x, limit)
}

/// A structure whose fields the checks below are written against.
pub struct Cursor {
    at: usize,
    step: u64,
    room: [u8; 16],
}

impl Cursor {
    /// Clean. The guard proves the field is in range, and the read measures
    /// the same place rather than a fresh copy of it.
    pub fn clean_field_index(&self) -> u8 {
        if self.at < 16 { self.room[self.at] } else { 0 }
    }

    /// Clean. The divisor is guarded once and read twice.
    pub fn clean_field_divide(&self, a: u64) -> u64 {
        if self.step == 0 {
            0
        } else {
            (a / self.step).wrapping_add(a % self.step)
        }
    }

    /// Reaches `index`. The field is written between the guard and the
    /// read, so what the guard proved is about the earlier value.
    pub fn must_field_written(&mut self) -> u8 {
        if self.at < 16 {
            self.at = self.at.wrapping_add(1);
            self.room[self.at]
        } else {
            0
        }
    }

    /// Reaches `index`. A call in between could change the field, and what
    /// it runs is a body this walk did not read.
    pub fn must_field_after_call(&mut self) -> u8 {
        if self.at < 16 {
            self.bump();
            self.room[self.at]
        } else {
            0
        }
    }

    #[inline(never)]
    fn bump(&mut self) {
        self.at = self.at.wrapping_add(1);
    }

    /// Reaches `index`. The guard measures another object's field.
    pub fn must_field_of_other(&self, other: &Self) -> u8 {
        if other.at < 16 { self.room[self.at] } else { 0 }
    }
}

/// Clean. Every byte is an index into a table with a place for each.
pub fn clean_byte_index(table: &[u8; 256], byte: u8) -> u8 {
    table[usize::from(byte)]
}

/// Reaches `index`. A wider value has more values than the table has room.
pub fn must_wide_index(table: &[u8; 256], word: u16) -> u8 {
    table[usize::from(word)]
}

/// Clean. The value was built here, so the arm that panics is not one this
/// call can take.
pub fn clean_unwrap_built(x: u8) -> u8 {
    Some(x).unwrap()
}

/// Clean. The arm proves which variant the value holds.
pub fn clean_unwrap_matched(o: Option<u8>) -> u8 {
    match o {
        Some(_) => o.unwrap(),
        None => 0,
    }
}

/// Clean. The same for a result built here.
pub fn clean_unwrap_ok(x: u8) -> u8 {
    let r: Result<u8, ()> = Ok(x);
    r.unwrap()
}

/// Reaches `unwrap`. Which variant arrives is the caller's choice.
pub fn must_unwrap_argument(o: Option<u8>) -> u8 {
    o.unwrap()
}

/// Reaches `unwrap`. The arm it is written in proves the empty variant.
pub fn must_unwrap_wrong_arm(o: Option<u8>) -> u8 {
    match o {
        Some(v) => v,
        None => o.unwrap(),
    }
}

/// Two variants, one of which the function below refuses.
pub enum Shape {
    Round,
    Flat,
}

/// Reaches `explicit`. Which variant arrives is the caller's choice.
pub fn must_match_panic(shape: Shape) -> u8 {
    match shape {
        Shape::Round => 1,
        Shape::Flat => panic!("flat"),
    }
}

/// Clean. The variant is fixed here, so the arm that panics is dead.
pub fn clean_match_panic() -> u8 {
    match Shape::Round {
        Shape::Round => 1,
        Shape::Flat => panic!("flat"),
    }
}

/// Clean. A pointer taken of a place holds an address, so the null check
/// inside the wrapper cannot fail.
pub fn clean_nonnull_of_place(x: &mut u8) -> std::ptr::NonNull<u8> {
    std::ptr::NonNull::new(x as *mut u8).unwrap()
}

/// Reaches `unwrap`. A raw pointer handed in can be null.
pub fn must_nonnull_of_argument(p: *mut u8) -> std::ptr::NonNull<u8> {
    std::ptr::NonNull::new(p).unwrap()
}

/// Clean. The guard is written against a literal, which reads the same in
/// every instantiation, so a generic body does not hide it.
pub fn clean_generic_guard<T>(_marker: &T, a: u64, b: u64) -> u64 {
    if b == 0 { 0 } else { a / b }
}

/// Reaches `divide-by-zero`. What the divisor is worth has no value until
/// the type does, and a type with no size is one of them.
pub fn must_generic_size_divide<T>(a: u64) -> u64 {
    a / (size_of::<T>() as u64)
}

/// Reaches `index`. Whether the index is in range is the caller's business.
fn must_take_indexed(v: &[u8], i: usize) -> u8 {
    v[i]
}

/// Clean. The guard proves the index in range before the call, and the
/// callee's own check is settled for the arguments this call makes.
pub fn clean_guard_before_call(v: &[u8], i: usize) -> u8 {
    if i < v.len() { must_take_indexed(v, i) } else { 0 }
}

/// Reaches `index` through the call, since nothing here settles it.
pub fn must_pass_unguarded(v: &[u8], i: usize) -> u8 {
    must_take_indexed(v, i)
}

/// A cursor over a slice, for the two checks below.
pub struct Window {
    at: usize,
    over: &'static [u8],
}

impl Window {
    /// Clean. The guard measures the same two places the read does.
    pub fn clean_window_read(&self) -> u8 {
        if self.at < self.over.len() { self.over[self.at] } else { 0 }
    }

    /// Reaches `index`. The guard measures another window's slice.
    pub fn must_window_of_other(&self, other: &Self) -> u8 {
        if self.at < other.over.len() { self.over[self.at] } else { 0 }
    }
}

/// Clean. Shifting a byte down by four leaves a nibble, and the table has
/// room for every one of them.
pub fn clean_shifted_index(table: &[u8; 16], byte: u8) -> u8 {
    table[usize::from(byte >> 4)]
}

/// Reaches `index`. One bit less of a shift leaves twice the values.
pub fn must_shifted_index(table: &[u8; 16], byte: u8) -> u8 {
    table[usize::from(byte >> 3)]
}

/// Reaches `index`. A shift by a runtime amount is a shift by anything.
pub fn must_shift_by_runtime(table: &[u8; 16], byte: u8, at: u32) -> u8 {
    table[usize::from(byte >> at)]
}

/// Reaches `index`. A signed shift keeps the sign, and a negative index
/// read as unsigned is far past the end.
pub fn must_signed_shift_index(table: &[u8; 16], x: i32) -> u8 {
    table[(x >> 28) as usize]
}

/// Clean. Four values raised two bits stay inside a table of sixty four.
pub fn clean_shifted_left_index(table: &[u8; 64], n: u8) -> u8 {
    table[usize::from((n & 0x0f) << 2)]
}

/// Reaches `index`. One bit further leaves the table behind.
pub fn must_shifted_left_index(table: &[u8; 64], n: u8) -> u8 {
    table[usize::from((n & 0x0f) << 3)]
}

/// Clean. Setting the low bit keeps the divisor away from zero.
pub fn clean_or_divide(x: u32, d: u32) -> u32 {
    x / (d | 1)
}

/// Reaches `divide-by-zero`. Two runtime values can both be zero.
pub fn must_or_divide(x: u32, d: u32, e: u32) -> u32 {
    x / (d | e)
}

/// Clean. Neither masked value reaches above the table.
pub fn clean_or_index(table: &[u8; 16], a: u8, b: u8) -> u8 {
    table[usize::from((a & 0x0c) | (b & 0x03))]
}

/// Reaches `index`. The wider mask carries a bit the table has no room for.
pub fn must_or_index(table: &[u8; 16], a: u8, b: u8) -> u8 {
    table[usize::from((a & 0x1c) | (b & 0x03))]
}

/// Clean. Flipping bits reaches no higher than the bits either side had.
pub fn clean_xor_index(table: &[u8; 16], a: u8, b: u8) -> u8 {
    table[usize::from((a & 0x0f) ^ (b & 0x0f))]
}

/// Reaches `index`. The wider mask carries a bit past the table.
pub fn must_xor_index(table: &[u8; 16], a: u8, b: u8) -> u8 {
    table[usize::from((a & 0x0f) ^ (b & 0x1f))]
}

/// Clean. A byte divided by sixteen is a nibble.
pub fn clean_divided_index(table: &[u8; 16], i: usize) -> u8 {
    table[(i & 0xff) / 16]
}

/// Reaches `index`. Dividing by fifteen leaves seventeen values.
pub fn must_divided_index(table: &[u8; 16], i: usize) -> u8 {
    table[(i & 0xff) / 15]
}

/// Clean. The divisor is pinned to a range, and a remainder lies below it.
pub fn clean_remainder_by_bounded(table: &[u8; 16], x: u32, d: u32) -> u8 {
    let d = d.max(1).min(16);
    table[(x % d) as usize]
}

/// Reaches `index`. One further leaves a remainder the table cannot hold.
pub fn must_remainder_by_bounded(table: &[u8; 16], x: u32, d: u32) -> u8 {
    let d = d.max(1).min(17);
    table[(x % d) as usize]
}

/// Clean. A word has thirty three possible counts of leading zeros.
pub fn clean_leading_zeros_index(table: &[u8; 33], x: u32) -> u8 {
    table[x.leading_zeros() as usize]
}

/// Reaches `index`. A word with no bits set counts every one of them.
pub fn must_leading_zeros_index(table: &[u8; 32], x: u32) -> u8 {
    table[x.leading_zeros() as usize]
}

/// Clean. The same holds for counting from the other end.
pub fn clean_trailing_zeros_index(table: &[u8; 33], x: u32) -> u8 {
    table[x.trailing_zeros() as usize]
}

/// Clean. And for counting the bits that are set.
pub fn clean_count_ones_index(table: &[u8; 33], x: u32) -> u8 {
    table[x.count_ones() as usize]
}

/// Reaches `index`. The counter is bounded by a length the read is not
/// measured against.
pub fn must_range_loop_of_other(v: &[u8], other: &[u8]) -> u32 {
    let mut s = 0u32;
    for i in 0..other.len() {
        s = s.wrapping_add(u32::from(v[i]));
    }
    s
}

/// Clean. The option carries the value the guard settled, and the field it
/// is read back from is the one it was built with.
pub fn clean_option_carries_index(table: &[u8; 16], i: usize) -> u8 {
    let held = if i < 16 { Some(i) } else { None };
    match held {
        Some(at) => table[at],
        None => 0,
    }
}

/// Reaches `index`. A wider guard lets a value past the table through.
pub fn must_option_carries_index(table: &[u8; 16], i: usize) -> u8 {
    let held = if i < 32 { Some(i) } else { None };
    match held {
        Some(at) => table[at],
        None => 0,
    }
}

/// Clean. Both slices are as long as their types say, so the lengths the
/// copy compares are equal and the check it writes cannot fail.
pub fn clean_copy_same_length(dst: &mut [u8; 4], src: &[u8; 4]) {
    dst.copy_from_slice(src);
}

/// Clean. The counter is bounded by one array's length, the other is as
/// long, and storing into a slice cannot change how long it is.
pub fn clean_copy_two_arrays(dst: &mut [u8; 8], src: &[u8; 8]) {
    for i in 0..dst.len() {
        dst[i] = src[i];
    }
}

/// Reaches `index`. Two slices of unrelated length share no bound.
pub fn must_copy_two_slices(dst: &mut [u8], src: &[u8]) {
    for i in 0..dst.len() {
        dst[i] = src[i];
    }
}

/// Clean. A slice that is not empty has a last element.
pub fn clean_last_of_guarded(v: &[u8]) -> u8 {
    if v.is_empty() { 0 } else { v[v.len() - 1] }
}

/// Reaches `index`. Two off the end leaves a slice that holds one.
pub fn must_second_last_of_guarded(v: &[u8]) -> u8 {
    if v.is_empty() { 0 } else { v[v.len() - 2] }
}

/// Reaches `explicit`. Nothing here says how long the slice is.
pub fn must_take_four(v: &[u8]) -> u8 {
    assert!(v.len() == 4, "the slice must hold four bytes");
    v[0]
}

/// Clean. The slice was made of an array, so it carries the length that
/// array's type states and the callee's own check is settled.
pub fn clean_pass_array_of_four(v: &[u8; 4]) -> u8 {
    must_take_four(v)
}

/// Moves the slice on by one, which is a write to the caller's own local.
fn shrink_slice(s: &mut &[u8]) {
    *s = &s[1..];
}

/// Reaches `index`. The guard was about the slice as it stood, and the call
/// replaced it with a shorter one.
pub fn must_index_after_shrink(mut s: &[u8]) -> u8 {
    if s.len() >= 2 {
        shrink_slice(&mut s);
        s[1]
    } else {
        0
    }
}

/// Reaches `index`. The counter runs one past the end of the array.
pub fn must_loop_past_the_end(table: &[u8; 16]) -> u32 {
    let mut total = 0u32;
    for i in 0..17 {
        total = total.wrapping_add(u32::from(table[i]));
    }
    total
}

/// Clean. The chunk size is a constant the library's own check settles, and
/// every call it makes below that is read the same way.
pub fn clean_chunks_of_a_constant(v: &[u8]) -> &[u8] {
    v.chunks_exact(4).remainder()
}

/// Reaches `explicit`. A chunk size the caller does not settle is one the
/// library refuses.
pub fn must_chunks_of_a_size(v: &[u8], size: usize) -> &[u8] {
    v.chunks_exact(size).remainder()
}

/// Clean. The step is a constant, so the check the adapter writes over it
/// cannot fail.
pub fn clean_step_by_a_constant(n: usize) -> usize {
    (0..n).step_by(2).count()
}

/// Reaches `explicit`. A step of zero is one the adapter refuses.
pub fn must_step_by_a_size(n: usize, step: usize) -> usize {
    (0..n).step_by(step).count()
}

/// Clean. The guard measures the same length the split is checked against.
pub fn clean_split_after_guard(v: &[u8]) -> (&[u8], &[u8]) {
    if v.len() >= 2 { v.split_at(2) } else { (v, v) }
}

/// Reaches `explicit`. Nothing here says the slice is long enough.
pub fn must_split_unguarded(v: &[u8]) -> (&[u8], &[u8]) {
    v.split_at(2)
}

/// Clean. The conversion cannot fail for this value, and the number it
/// hands back inside the wrapper is the one the division reads.
pub fn clean_convert_constant(x: u16) -> u16 {
    let scale: u16 = 10_000i32.try_into().expect("ten thousand fits");
    x % scale
}

/// Reaches `remainder-by-zero`. Nothing here settles what the conversion
/// leaves behind.
pub fn must_convert_runtime(x: u16, scale: i32) -> u16 {
    let scale: u16 = scale.try_into().unwrap_or(0);
    x % scale
}

/// Clean. The size the iterator carries is the constant it was built with,
/// so the division its own size hint writes cannot fail.
pub fn clean_chunk_count(v: &[u8]) -> usize {
    v.chunks_exact(4).count()
}

/// Reaches `index`, since a slice may be shorter than the prefix asked
/// for. The copy's own length check goes all the same: the prefix is
/// exactly as long as the array being written into it.
pub fn must_copy_into_prefix(buf: &mut [u8], n: u128) {
    buf[..16].copy_from_slice(&n.to_be_bytes());
}

/// Clean. The array has room for the prefix, and the prefix is as long as
/// what is copied into it.
pub fn clean_copy_into_array(buf: &mut [u8; 32], n: u128) {
    buf[..16].copy_from_slice(&n.to_be_bytes());
}

/// Clean. The guard measures the two slices the copy compares, so the
/// check the copy writes over them cannot fail.
pub fn clean_copy_after_guard(dst: &mut [u8], src: &[u8]) {
    if dst.len() == src.len() {
        dst.copy_from_slice(src);
    }
}

/// Reaches `explicit`. The guard measures a third slice, which says
/// nothing about the two being copied between.
pub fn must_copy_guarded_on_other(dst: &mut [u8], src: &[u8], other: &[u8]) {
    if dst.len() == other.len() {
        dst.copy_from_slice(src);
    }
}

/// Reaches `index`. Two slices of one length still say nothing about an
/// index into either.
pub fn must_index_of_equal_lengths(a: &[u8], b: &[u8], i: usize) -> u8 {
    if a.len() == b.len() { a[i] } else { 0 }
}

/// Clean. The wrapper holds a value exactly when that value is not zero,
/// so the option it hands back never takes the arm that panics.
pub fn clean_nonzero_of_set_bit(n: usize) -> usize {
    core::num::NonZeroUsize::new(n | 1)
        .expect("the low bit is set")
        .get()
}

/// Reaches `unwrap`. Nothing here keeps the value away from zero.
pub fn must_nonzero_of_anything(n: usize) -> usize {
    core::num::NonZeroUsize::new(n).expect("nonzero").get()
}

/// Clean. Half a length is no longer than the length, which is what the
/// split measures its argument against.
pub fn clean_split_in_half(v: &[u8]) -> (&[u8], &[u8]) {
    v.split_at(v.len() / 2)
}

/// Clean. The smaller of an index and the last position is in range.
pub fn clean_clamped_to_last(v: &[u8], i: usize) -> u8 {
    if v.is_empty() { 0 } else { v[i.min(v.len() - 1)] }
}

/// Reaches `index`. The larger of the two is past the end.
pub fn must_clamped_to_larger(v: &[u8], i: usize) -> u8 {
    if v.is_empty() { 0 } else { v[i.max(v.len() - 1)] }
}

/// Clean. The guard measures the same length the prefix is checked
/// against, and no length is below zero.
pub fn clean_prefix_under_guard(v: &[u8], n: usize) -> &[u8] {
    if n <= v.len() { &v[..n] } else { v }
}

/// Reaches `index`. Nothing here keeps the prefix inside the slice.
pub fn must_prefix_unguarded(v: &[u8], n: usize) -> &[u8] {
    &v[..n]
}

/// Clean. The inner guard measures against a value the outer one already
/// proved below the length, so the read is in range.
pub fn clean_guard_within_a_guard(v: &[u8], i: usize, j: usize) -> u8 {
    if i < v.len() && j < i { v[j] } else { 0 }
}

/// Reaches `index`. Two values at most the length can both be the length.
pub fn must_guard_within_a_loose_guard(v: &[u8], i: usize, j: usize) -> u8 {
    if i <= v.len() && j <= i { v[j] } else { 0 }
}

/// Reaches `index`. The outer guard measures another slice.
pub fn must_guard_within_a_guard_of_other(
    v: &[u8],
    w: &[u8],
    i: usize,
    j: usize,
) -> u8 {
    if i < w.len() && j < i { v[j] } else { 0 }
}

/// Clean. The counter starts at the length, and the guard above the
/// subtraction keeps it there through every turn of the loop.
pub fn clean_countdown_loop(v: &[u8]) -> u32 {
    let mut total = 0u32;
    let mut i = v.len();
    while i > 0 {
        i -= 1;
        total = total.wrapping_add(u32::from(v[i]));
    }
    total
}

/// Reaches `index`. The counter starts one past the end.
pub fn must_countdown_from_the_length(v: &[u8]) -> u32 {
    let mut total = 0u32;
    let mut i = v.len();
    while i > 0 {
        total = total.wrapping_add(u32::from(v[i]));
        i -= 1;
    }
    total
}

/// Clean. The guard above every write keeps the counter inside the buffer,
/// and a widening step stops at the bound the loop was written to keep.
pub fn clean_fill_bounded(n: u32, out: &mut [u8; 10]) -> usize {
    let mut used = 0;
    let mut left = n;
    while left > 0 && used < out.len() {
        out[used] = (left % 10) as u8;
        left /= 10;
        used += 1;
    }
    used
}

/// Reaches `index`. The guard leaves room for one more than the buffer
/// holds.
pub fn must_fill_past_the_end(n: u32, out: &mut [u8; 10]) -> usize {
    let mut used = 0;
    let mut left = n;
    while left > 0 && used <= out.len() {
        out[used] = (left % 10) as u8;
        left /= 10;
        used += 1;
    }
    used
}

/// Clean. A slice of two has a middle, and both ends of the range lie
/// inside it.
pub fn clean_middle_of_guarded(v: &[u8]) -> &[u8] {
    if v.len() >= 2 { &v[1..v.len() - 1] } else { v }
}

/// Reaches `index`. One element leaves no middle.
pub fn must_middle_of_one(v: &[u8]) -> &[u8] {
    if v.is_empty() { v } else { &v[1..v.len() - 1] }
}

/// Clean. The offset is at most the length and is not the length, so it is
/// inside the slice.
pub fn clean_offset_below_the_end(v: &[u8], off: usize) -> u8 {
    let at = off.min(v.len());
    if at == v.len() { 0 } else { v[at] }
}

/// Reaches `index`. Nothing here rules the end out.
pub fn must_offset_at_the_end(v: &[u8], off: usize) -> u8 {
    let at = off.min(v.len());
    v[at]
}

/// Clean. The smaller of two lengths is inside both slices, so a read of
/// either at that point is in range.
pub fn clean_prefix_of_both(a: &[u8], b: &[u8]) -> bool {
    let n = a.len().min(b.len());
    a[..n] == b[..n]
}

/// Reaches `index`. The larger of two lengths is outside one of them.
pub fn must_prefix_of_the_longer(a: &[u8], b: &[u8]) -> bool {
    let n = a.len().max(b.len());
    a[..n] == b[..n]
}

/// Clean. Everything past a byte inside a slice is still inside it, and the
/// counter is bounded by half a length that is itself bounded.
pub fn clean_split_at_a_byte(src: &[u8]) -> (&[u8], &[u8]) {
    let mut at = 0;
    while at < src.len() {
        if src[at] == b'\n' {
            return (&src[..at], &src[at + 1..]);
        }
        at += 1;
    }
    (src, &[])
}

/// Reaches `index`. Two past a byte inside a slice can be past its end.
pub fn must_split_two_past(v: &[u8], at: usize) -> &[u8] {
    if at < v.len() { &v[at + 2..] } else { v }
}

/// Clean. The counter is below half a length, and half a length is at most
/// that length.
pub fn clean_first_half(v: &[u8]) -> u32 {
    let half = v.len() / 2;
    let mut total = 0u32;
    let mut at = 0;
    while at < half {
        total = total.wrapping_add(u32::from(v[at]));
        at += 1;
    }
    total
}

/// Clean. The counter walks down from the last position and the guard above
/// the read keeps it there, so both ends of the move are inside the array.
pub fn clean_shift_along(state: &mut [u8; 8], b: u8) {
    let mut at = 7;
    while at > 0 {
        state[at] = state[at - 1];
        at -= 1;
    }
    state[0] = b;
}

/// Reaches `index`. The counter starts one past the last position.
pub fn must_shift_from_the_length(state: &mut [u8; 8], b: u8) {
    let mut at = 8;
    while at > 0 {
        state[at] = state[at - 1];
        at -= 1;
    }
    state[0] = b;
}

/// Clean. The guard measures the same element the read does, and the
/// element is named by an index nothing has changed since.
pub fn clean_inner_of_guarded(v: &[&[u8]], i: usize) -> u8 {
    if i < v.len() && !v[i].is_empty() { v[i][0] } else { 0 }
}

/// Reaches `index`. The guard measures another element.
pub fn must_inner_of_other(v: &[&[u8]], i: usize, j: usize) -> u8 {
    if i < v.len() && j < v.len() && !v[j].is_empty() {
        v[i][0]
    } else {
        0
    }
}

/// Reaches `index`. The index moved between the guard and the read, so the
/// element it names is not the one that was measured.
pub fn must_inner_after_move(v: &[&[u8]], mut i: usize) -> u8 {
    if i < v.len() && !v[i].is_empty() {
        i = 0;
        if i < v.len() { v[i][0] } else { 0 }
    } else {
        0
    }
}

/// Clean. A character holds fewer values than its width allows, so the top
/// bits of one are an index the table has room for.
pub fn clean_char_high_bits(c: char, table: &[u8; 136]) -> u8 {
    table[(c as usize) >> 13]
}

/// Reaches `index`. One entry short of what a character can reach.
pub fn must_char_high_bits(c: char, table: &[u8; 135]) -> u8 {
    table[(c as usize) >> 13]
}

/// Clean. A boolean is one of two values, and the table has both.
pub fn clean_bool_index(b: bool, table: &[u8; 2]) -> u8 {
    table[usize::from(b)]
}

/// Clean. The guard measures the two lengths the prefix and the copy read,
/// whichever way round it is written, and the prefix is exactly as long as
/// the slice being copied into.
pub fn clean_copy_prefix_under_guard(src: &[u8], dst: &mut [u8]) {
    if src.len() < dst.len() {
        return;
    }
    dst.copy_from_slice(&src[..dst.len()]);
}

/// Reaches `explicit`. The prefix is as long as a third slice, which says
/// nothing about the one being copied into.
pub fn must_copy_prefix_of_other(src: &[u8], dst: &mut [u8], other: &[u8]) {
    if src.len() < other.len() {
        return;
    }
    dst.copy_from_slice(&src[..other.len()]);
}

/// Clean. Both slices are cut to the same length, so the check the copy
/// writes over the two of them cannot fail.
pub fn clean_copy_the_shorter(dst: &mut [u8], src: &[u8]) {
    let n = dst.len().min(src.len());
    dst[..n].copy_from_slice(&src[..n]);
}

/// Reaches `explicit`. Two lengths that are each in range need not match.
pub fn must_copy_two_lengths(src: &[u8], dst: &mut [u8], n: usize, m: usize) {
    if n <= src.len() && m <= dst.len() {
        dst[..m].copy_from_slice(&src[..n]);
    }
}

/// Clean. An unsigned value below another leaves that other above zero, so
/// the remainder written under the guard cannot fail.
pub fn clean_modulo_above_guard(lo: u32, n: u32) -> u32 {
    if lo < n { lo % n } else { 0 }
}

/// Reaches `remainder-by-zero`. Two values merely not above each other can
/// both be zero.
pub fn must_modulo_at_most_guard(lo: u32, n: u32) -> u32 {
    if lo <= n { lo % n } else { 0 }
}

/// Clean. A value is never above itself raised by three, and three times a
/// byte leaves room for three more in a table of seven hundred and sixty
/// eight.
pub fn clean_table_of_threes(byte: u8, table: &[u8; 768]) -> &[u8] {
    let at = usize::from(byte) * 3;
    &table[at..at + 3]
}

/// Reaches `index`. One byte short of what three times a byte can reach.
pub fn must_table_of_threes(byte: u8, table: &[u8; 767]) -> &[u8] {
    let at = usize::from(byte) * 3;
    &table[at..at + 3]
}

/// Clean. The counter starts at nothing and only ever steps to the next
/// place inside the slice, so it never passes the end.
pub fn clean_scan_until(v: &[u8], stop: u8) -> &[u8] {
    let mut at = 0;
    while at < v.len() && v[at] != stop {
        at += 1;
    }
    &v[..at]
}

/// Reaches `index`. Stepping by two can walk over the end.
pub fn must_scan_by_two(v: &[u8], stop: u8) -> &[u8] {
    let mut at = 0;
    while at < v.len() && v[at] != stop {
        at += 2;
    }
    &v[..at]
}

/// Takes a value it only drops, so what the drop runs is decided by the
/// caller's choice of type.
fn take_and_index<T>(x: T, v: &[u8; 4], at: usize) -> u8 {
    let _ = x;
    v[at]
}

/// Clean. The guard settles the read, and the value the callee drops is of
/// a type with nothing to run, which is what this call makes of it.
pub fn clean_drop_beside_a_guard(v: &[u8; 4]) -> u8 {
    take_and_index(7u32, v, 3)
}

/// Reaches `index`. Nothing settles the read.
pub fn must_drop_beside_a_guard(v: &[u8; 4], at: usize) -> u8 {
    take_and_index(7u32, v, at)
}

/// Clean. Walking a deque asks the library for the whole of it, and a range
/// with neither end named cannot fall outside anything.
pub fn clean_deque_walk(q: &std::collections::VecDeque<u8>) -> usize {
    q.iter().count()
}

/// Reaches `index`. A range the caller names can leave the deque.
pub fn must_deque_range(q: &std::collections::VecDeque<u8>, at: usize) -> usize {
    q.range(at..).count()
}

/// Clean. The ordering is written at the call, so the arm rejecting a
/// releasing load folds away and what is left is an operation the compiler
/// defines rather than a body that could raise.
pub fn clean_atomic_load(a: &core::sync::atomic::AtomicUsize) -> usize {
    a.load(core::sync::atomic::Ordering::Relaxed)
}

/// Clean. A fence names its ordering the same way, and the barrier it
/// lowers to is not a body either.
pub fn clean_atomic_fence() {
    core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
}

/// Clean. Both orderings a compare and exchange takes are written here, so
/// neither of the arms rejecting a pairing survives.
pub fn clean_atomic_compare_exchange(
    a: &core::sync::atomic::AtomicUsize,
) -> bool {
    a.compare_exchange(
        0,
        1,
        core::sync::atomic::Ordering::AcqRel,
        core::sync::atomic::Ordering::Acquire,
    )
    .is_ok()
}

/// Reaches `explicit`. An ordering the caller chooses can be the one a load
/// rejects.
pub fn must_atomic_load(
    a: &core::sync::atomic::AtomicUsize,
    order: core::sync::atomic::Ordering,
) -> usize {
    a.load(order)
}

/// Clean. Masking leaves two bits, and all four values they can hold are
/// named, so the arm the compiler writes for the rest is dead.
pub fn clean_masked_switch(x: usize) -> u8 {
    match x & 0b11 {
        0 => 10,
        1 => 20,
        2 => 30,
        3 => 40,
        _ => unreachable!(),
    }
}

/// Reaches `explicit`. One of the four values the mask leaves is unnamed,
/// so the arm for the rest is reachable.
pub fn must_masked_switch(x: usize) -> u8 {
    match x & 0b11 {
        0 => 10,
        1 => 20,
        2 => 30,
        _ => unreachable!(),
    }
}

/// Clean. A remainder by four cannot leave the four values named either.
pub fn clean_remainder_switch(x: u32) -> u8 {
    match x % 4 {
        0 => 10,
        1 => 20,
        2 => 30,
        3 => 40,
        _ => unreachable!(),
    }
}

/// Clean. A vector's length is a field it is read out of, and the check the
/// index writes reads that same field again, so the guard covers it.
pub fn clean_vector_index_guard(v: &Vec<u8>, at: usize) -> u8 {
    if at >= v.len() { 0 } else { v[at] }
}

/// Reaches `index`. Nothing measures the index against the length.
pub fn must_vector_index(v: &Vec<u8>, at: usize) -> u8 {
    v[at]
}

/// Clean. The same holds for a deque, whose length is a field as well.
pub fn clean_deque_index_guard(
    q: &std::collections::VecDeque<u8>,
    at: usize,
) -> u8 {
    if at >= q.len() { 0 } else { q[at] }
}

/// Clean. A string's bytes are as many as its length says.
pub fn clean_string_index_guard(s: &String, at: usize) -> u8 {
    if at >= s.len() { 0 } else { s.as_bytes()[at] }
}

/// Reaches `index`. A guard read backwards proves nothing: failing `a > b`
/// leaves `a` at most `b`, which says nothing about where the bottom of
/// `b`'s range is, so the index is still anything the type admits.
pub fn must_index_after_le(a: usize, b: usize, t: &[u8; 4]) -> u8 {
    if a > b { 0 } else { t[a] }
}

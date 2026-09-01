//! What the analysis reports for a crate whose panics are known.
//!
//! This is the only test that runs the compiler driver, so it is what keeps
//! the two halves honest: the reachability of a body is decided against the
//! settings of the build in front of it, and a check the arguments settle is
//! not a panic. Both directions matter. Dropping a check that can fail would
//! make a clean report meaningless, and keeping one that cannot fail is the
//! noise the tool exists to remove.

mod support;

use crate::support::analyse_fixture;

/// The panic each function must be reported with.
const MUST_PANIC: &[(&str, &str)] = &[
    ("must_index", "index"),
    ("must_divide", "divide-by-zero"),
    ("must_remainder", "remainder-by-zero"),
    ("must_unwrap", "unwrap"),
    ("must_assert", "explicit"),
    ("must_slice_tail", "index"),
    ("must_copy", "explicit"),
    ("must_assert_generic", "explicit"),
    ("must_assert_false", "explicit"),
    ("must_divide_misguarded", "divide-by-zero"),
    ("must_divide_inverted_guard", "divide-by-zero"),
    ("must_divide_once_of_two", "divide-by-zero"),
    ("must_divide_narrowed", "divide-by-zero"),
    ("must_push", "capacity-overflow"),
    ("must_push", "alloc-failure"),
    ("must_rethrow", "explicit"),
    ("must_lock", "poison"),
    ("must_write", "fmt"),
    ("must_rc_clone", "refcount-overflow"),
    ("must_slice_str", "str-boundary"),
    ("must_borrow", "borrow"),
    ("must_dyn", "dyn-call"),
    ("must_foreign", "foreign"),
    ("must_catch_abort", "alloc-failure"),
    ("must_index_off_by_one", "index"),
    ("must_index_wrong_slice", "index"),
    ("must_modulo_signed", "index"),
    ("must_fn_ptr", "fn-pointer"),
    ("must_generic", "generic-bound"),
    ("must_dyn_speak", "dyn-call"),
    ("must_zeroed_ref", "explicit"),
    ("must_panic_literal", "explicit"),
    ("must_zeroed_chain", "generic-bound"),
    ("must_divide_by_max_zero", "divide-by-zero"),
    ("must_divide_by_min", "divide-by-zero"),
    ("must_index_past_length_guard", "index"),
    ("must_modulo_length", "remainder-by-zero"),
    ("must_masked_index_offset", "index"),
    ("must_be_below", "explicit"),
    ("must_pass_unchecked_limit", "explicit"),
    ("Cursor::must_field_written", "index"),
    ("Cursor::must_field_after_call", "index"),
    ("Cursor::must_field_of_other", "index"),
    ("must_wide_index", "index"),
    ("must_unwrap_argument", "unwrap"),
    ("must_two_lengths", "index"),
    ("must_unwrap_wrong_arm", "unwrap"),
    ("must_match_panic", "explicit"),
    ("must_nonnull_of_argument", "unwrap"),
    ("must_generic_size_divide", "divide-by-zero"),
    ("must_take_indexed", "index"),
    ("must_pass_unguarded", "index"),
    ("Window::must_window_of_other", "index"),
    ("must_shifted_index", "index"),
    ("must_shift_by_runtime", "index"),
    ("must_signed_shift_index", "index"),
    ("must_shifted_left_index", "index"),
    ("must_or_divide", "divide-by-zero"),
    ("must_or_index", "index"),
    ("must_xor_index", "index"),
    ("must_divided_index", "index"),
    ("must_remainder_by_bounded", "index"),
    ("must_leading_zeros_index", "index"),
    ("must_range_loop_of_other", "index"),
    ("must_option_carries_index", "index"),
    ("must_copy_two_slices", "index"),
    ("must_second_last_of_guarded", "index"),
    ("must_take_four", "explicit"),
    ("must_index_after_shrink", "index"),
    ("must_loop_past_the_end", "index"),
    ("must_chunks_of_a_size", "explicit"),
    ("must_step_by_a_size", "explicit"),
    ("must_split_unguarded", "explicit"),
    ("must_convert_runtime", "remainder-by-zero"),
    ("must_copy_into_prefix", "index"),
    ("must_copy_guarded_on_other", "explicit"),
    ("must_index_of_equal_lengths", "index"),
    ("must_nonzero_of_anything", "unwrap"),
    ("must_clamped_to_larger", "index"),
    ("must_prefix_unguarded", "index"),
    ("must_guard_within_a_loose_guard", "index"),
    ("must_guard_within_a_guard_of_other", "index"),
    ("must_countdown_from_the_length", "index"),
    ("must_fill_past_the_end", "index"),
    ("must_middle_of_one", "index"),
    ("must_offset_at_the_end", "index"),
    ("must_prefix_of_the_longer", "index"),
    ("must_split_two_past", "index"),
    ("must_shift_from_the_length", "index"),
    ("must_inner_of_other", "index"),
    ("must_inner_after_move", "index"),
];

/// The panics each function must *not* be reported with.
///
/// A check the analysis can settle has to go even where the same function
/// keeps another that it cannot.
const MUST_NOT_PANIC: &[(&str, &str)] = &[
    ("must_divide_once_of_two", "remainder-by-zero"),
    ("must_lock", "unwrap"),
    ("must_write", "unwrap"),
    ("must_not_catch_explicit", "explicit"),
    ("must_dyn_speak", "explicit"),
    ("must_modulo_length", "index"),
    ("must_copy_into_prefix", "explicit"),
];

/// The functions that must be reported with nothing at all.
const MUST_BE_CLEAN: &[&str] = &[
    "clean_divide_by_constant",
    "clean_fold",
    "clean_count_zeros",
    "clean_sum_by_get",
    "clean_assert_true",
    "clean_guarded_divide",
    "clean_guarded_divide_ne",
    "clean_guarded_remainder",
    "clean_guarded_widening",
    "clean_modulo_index",
    "clean_masked_index",
    "clean_guarded_index",
    "clean_guarded_index_flipped",
    "clean_while_index",
    "clean_nonzero_divide",
    "clean_zeroed_int",
    "clean_divide_by_max",
    "clean_remainder_by_max",
    "clean_divide_by_min_plus_one",
    "clean_divide_by_clamp",
    "clean_divide_by_helper",
    "clean_divide_by_either_arm",
    "clean_index_after_empty_guard",
    "clean_index_after_length_guard",
    "clean_masked_index_offset",
    "clean_precondition_met",
    "Cursor::clean_field_index",
    "Cursor::clean_field_divide",
    "clean_byte_index",
    "clean_unwrap_built",
    "clean_unwrap_matched",
    "clean_unwrap_ok",
    "clean_match_panic",
    "clean_nonnull_of_place",
    "clean_generic_guard",
    "clean_guard_before_call",
    "Window::clean_window_read",
    "clean_shifted_index",
    "clean_shifted_left_index",
    "clean_or_divide",
    "clean_or_index",
    "clean_xor_index",
    "clean_divided_index",
    "clean_remainder_by_bounded",
    "clean_leading_zeros_index",
    "clean_trailing_zeros_index",
    "clean_count_ones_index",
    "clean_range_loop",
    "clean_option_carries_index",
    "clean_copy_same_length",
    "clean_copy_two_arrays",
    "clean_last_of_guarded",
    "clean_pass_array_of_four",
    "clean_chunks_of_a_constant",
    "clean_step_by_a_constant",
    "clean_split_after_guard",
    "clean_convert_constant",
    "clean_chunk_count",
    "clean_copy_into_array",
    "clean_copy_after_guard",
    "clean_nonzero_of_set_bit",
    "clean_split_in_half",
    "clean_clamped_to_last",
    "clean_prefix_under_guard",
    "clean_guard_within_a_guard",
    "clean_countdown_loop",
    "clean_fill_bounded",
    "clean_middle_of_guarded",
    "clean_offset_below_the_end",
    "clean_prefix_of_both",
    "clean_split_at_a_byte",
    "clean_first_half",
    "clean_shift_along",
    "clean_inner_of_guarded",
];

/// The functions that must stay clean in a debug build as well.
///
/// A debug build folds the same guards without the optimizer's help: no
/// inlining has merged the comparison into the check, so every settled
/// verdict below is the analysis's own reasoning. The full clean list is
/// not used because a debug build genuinely adds checks inside the standard
/// library that some of those functions reach.
const MUST_BE_CLEAN_IN_DEBUG: &[&str] = &[
    "clean_divide_by_constant",
    "clean_guarded_divide",
    "clean_guarded_divide_ne",
    "clean_guarded_remainder",
    "clean_modulo_index",
    "clean_masked_index",
    "clean_guarded_index",
    "clean_guarded_index_flipped",
    "clean_while_index",
    "clean_nonzero_divide",
    "clean_divide_by_max",
    "clean_remainder_by_max",
    "clean_divide_by_clamp",
    "clean_divide_by_helper",
    "clean_divide_by_either_arm",
    "clean_precondition_met",
    "Cursor::clean_field_index",
    "Cursor::clean_field_divide",
    "clean_byte_index",
    "clean_unwrap_built",
    "clean_unwrap_matched",
    "clean_unwrap_ok",
    "clean_match_panic",
    "clean_generic_guard",
    "clean_shifted_index",
    "clean_shifted_left_index",
    "clean_or_divide",
    "clean_or_index",
    "clean_xor_index",
    "clean_divided_index",
    "clean_remainder_by_bounded",
    "clean_leading_zeros_index",
    "clean_trailing_zeros_index",
    "clean_count_ones_index",
];

#[test]
fn a_known_crate_reports_exactly_its_panics() {
    let reported = analyse_fixture("release", &[]);
    let found = |name: &str| {
        reported
            .iter()
            .find(|(function, _)| function == name)
            .map(|(_, categories)| categories.clone())
    };

    for (function, category) in MUST_PANIC {
        let categories = found(function).unwrap_or_else(|| {
            panic!("{function} can panic with {category} and was not reported")
        });
        assert!(
            categories.iter().any(|c| c == category),
            "{function} can panic with {category}, but was reported with \
             {categories:?}"
        );
    }

    for (function, category) in MUST_NOT_PANIC {
        let categories = found(function).unwrap_or_default();
        assert!(
            !categories.iter().any(|c| c == category),
            "{function} cannot panic with {category}, but was reported with \
             {categories:?}"
        );
    }

    for function in MUST_BE_CLEAN {
        assert!(
            found(function).is_none(),
            "{function} cannot panic, but was reported with {:?}",
            found(function)
        );
    }
}

#[test]
fn a_debug_build_still_folds_the_guards() {
    let reported = analyse_fixture("debug", &[]);
    let found = |name: &str| {
        reported
            .iter()
            .find(|(function, _)| function == name)
            .map(|(_, categories)| categories.clone())
    };

    for function in MUST_BE_CLEAN_IN_DEBUG {
        assert!(
            found(function).is_none(),
            "{function} cannot panic in a debug build either, but was \
             reported with {:?}",
            found(function)
        );
    }

    for (function, category) in MUST_PANIC {
        let categories = found(function).unwrap_or_else(|| {
            panic!(
                "{function} can panic with {category} in a debug build and \
                 was not reported"
            )
        });
        assert!(
            categories.iter().any(|c| c == category),
            "{function} can panic with {category}, but a debug build \
             reported {categories:?}"
        );
    }
}

#[test]
fn candidates_expand_dyn_and_pointer_calls() {
    let reported = analyse_fixture("release", &["--candidates"]);
    let found = |name: &str| {
        reported
            .iter()
            .find(|(function, _)| function == name)
            .map(|(_, categories)| categories.clone())
            .unwrap_or_default()
    };

    let dyn_call = found("must_dyn_speak");
    assert!(
        dyn_call.iter().any(|c| c == "explicit"),
        "one implementation panics, so following candidates must surface \
         it, got {dyn_call:?}"
    );
    assert!(
        dyn_call.iter().any(|c| c == "dyn-call"),
        "candidates narrow the unknown, they do not close it, got \
         {dyn_call:?}"
    );

    let pointer = found("must_fn_ptr");
    assert!(
        pointer.iter().any(|c| c == "explicit"),
        "a reified function of this signature panics, got {pointer:?}"
    );
    assert!(
        pointer.iter().any(|c| c == "fn-pointer"),
        "the pointer could still hold something unseen, got {pointer:?}"
    );
}

#[test]
fn a_static_panic_message_is_quoted_in_the_reason() {
    let exe = std::path::PathBuf::from(env!("CARGO_BIN_EXE_panicgraph"));
    let output = std::process::Command::new(&exe)
        .arg("--manifest-dir")
        .arg(support::fixture_dir())
        .arg("--suppress")
        .arg("")
        .output()
        .expect("the front end should run");
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(
        text.contains("panics with \"assertion failed: "),
        "the report should quote the message a panic carries:\n{text}"
    );
}

#[test]
fn closures_fold_into_their_parent_on_request() {
    let reported = analyse_fixture("release", &["--closures", "parent"]);
    assert!(
        reported.iter().all(|(f, _)| !f.contains("{closure")),
        "the parent view must not name closures on their own"
    );
    let folded = reported
        .iter()
        .find(|(f, _)| f == "must_not_catch_explicit")
        .map(|(_, c)| c.clone())
        .unwrap_or_default();
    assert!(
        folded.iter().any(|c| c == "explicit"),
        "the compact view attributes a closure's panics to the function it \
         is written in, even the contained ones; got {folded:?}"
    );
}

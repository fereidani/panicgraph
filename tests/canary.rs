//! The compiled fixture must not call a panic entry point the analysis
//! failed to report anywhere.
//!
//! The analysis reads MIR; the linker reads what codegen produced. Sweeping
//! the compiled library for undefined panic entry points and demanding that
//! each is dominated by some finding catches a taxonomy hole mechanically:
//! a new entry point in the standard library, or a path the extraction
//! stopped seeing, turns up here as an undominated symbol.

mod support;

use std::{path::PathBuf, process::Command};

use crate::support::{analyse_fixture, fixture_dir};

/// Symbols the panic runtime plants around every unwind.
///
/// These are emitted by codegen for cleanup paths and panic bookkeeping,
/// not called from any MIR the analysis reads, so no finding maps to them.
const MACHINERY: &[&str] = &[
    "core::panicking::panic_in_cleanup",
    "core::panicking::panic_cannot_unwind",
    "std::panicking::panic_count",
    "std::panicking::catch_unwind",
    "rust_eh_personality",
];

/// Panic entry points and the categories that dominate each.
///
/// More specific rows come first, because matching is by substring and the
/// generic `core::panicking` prefix would otherwise swallow the rest.
const ENTRIES: &[(&str, &[&str])] = &[
    ("core::panicking::panic_bounds_check", &["index"]),
    ("core::slice::index::", &["index"]),
    ("core::str::slice_error_fail", &["str-boundary"]),
    ("core::option::unwrap_failed", &["unwrap", "poison", "fmt"]),
    ("core::option::expect_failed", &["unwrap", "poison", "fmt"]),
    ("core::result::unwrap_failed", &["unwrap", "poison", "fmt"]),
    ("core::cell::panic_already", &["borrow"]),
    ("alloc::raw_vec::capacity_overflow", &["capacity-overflow"]),
    (
        "alloc::raw_vec::handle_error",
        &["capacity-overflow", "alloc-failure"],
    ),
    ("handle_alloc_error", &["alloc-failure"]),
    ("resume_unwind", &["explicit"]),
    ("len_mismatch_fail", &["explicit"]),
    ("core::panicking::", &["explicit"]),
];

/// Prefixes that mark a symbol as panic related even when no row above
/// names it. An entry point the table does not know is exactly the drift
/// this test exists to catch.
const SUSPICIOUS: &[&str] = &[
    "core::panicking::",
    "core::slice::index::slice_",
    "core::str::slice_error",
    "core::option::unwrap",
    "core::option::expect",
    "core::result::unwrap",
    "core::cell::panic",
    "alloc::raw_vec::capacity",
    "alloc::raw_vec::handle",
    "alloc::alloc::handle",
];

/// Runs a command and returns its stdout as text.
fn text_of(cmd: &mut Command) -> String {
    let output = cmd.output().expect("the command should run");
    assert!(
        output.status.success(),
        "the command failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("the output should be utf-8")
}

/// The demangling nm shipped with the pinned toolchain.
fn llvm_nm() -> PathBuf {
    let sysroot = text_of(Command::new("rustc").arg("--print").arg("sysroot"));
    let host = text_of(Command::new("rustc").arg("-vV"))
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_owned))
        .expect("rustc should report a host triple");
    let nm = PathBuf::from(sysroot.trim())
        .join("lib")
        .join("rustlib")
        .join(host.trim())
        .join("bin")
        .join("llvm-nm");
    assert!(
        nm.exists(),
        "llvm-nm is missing; install the llvm-tools component"
    );
    nm
}

#[test]
fn every_panic_entry_in_the_binary_is_dominated_by_a_finding() {
    // The analysis run also produces the library the sweep reads.
    let reported = analyse_fixture("release", &[]);
    let mut live: Vec<String> = Vec::new();
    for (_, categories) in &reported {
        for category in categories {
            if !live.contains(category) {
                live.push(category.clone());
            }
        }
    }

    let rlib = fixture_dir()
        .join("target")
        .join("panicgraph")
        .join("build")
        .join("release")
        .join("libknown.rlib");
    assert!(rlib.exists(), "the analysis build should leave {rlib:?}");

    let listing = text_of(
        Command::new(llvm_nm())
            .arg("--demangle")
            .arg("--undefined-only")
            .arg(&rlib),
    );

    for line in listing.lines() {
        let Some(symbol) = line.trim().strip_prefix("U ") else {
            continue;
        };
        if MACHINERY.iter().any(|known| symbol.contains(known)) {
            continue;
        }
        if let Some((_, categories)) =
            ENTRIES.iter().find(|(name, _)| symbol.contains(name))
        {
            assert!(
                categories.iter().any(|c| live.iter().any(|l| l == c)),
                "the binary calls {symbol}, but no finding carries any of \
                 {categories:?}; the analysis lost sight of this entry point"
            );
            continue;
        }
        assert!(
            !SUSPICIOUS.iter().any(|prefix| symbol.contains(prefix)),
            "the binary calls {symbol}, which looks like a panic entry \
             point this test does not know; the sink table and this sweep \
             both need a row for it"
        );
    }
}

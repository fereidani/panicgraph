//! Checks that the toolchain can build the analysis driver.
//!
//! The driver links against compiler internals. Without this check the build
//! fails deep inside the driver with an error about an unstable feature or a
//! missing crate, neither of which tells the reader what to install.

use std::{path::Path, process::Command};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if let Err(problem) = check() {
        // Printed as a warning so cargo shows it prominently, and repeated on
        // stderr so it survives in a captured log.
        println!("cargo:warning={problem}");
        eprintln!("\npanicgraph: {problem}\n");
        std::process::exit(1);
    }
}

/// Reports the first missing prerequisite, if any.
fn check() -> Result<(), String> {
    let version = rustc_field("release: ")?;
    if !version.contains("nightly") && !version.contains("dev") {
        return Err(format!(
            "the analysis driver reads compiler internals, which needs a \
             nightly toolchain, but this build is using {version}. Install \
             with `cargo +nightly install --path .`, or add a \
             rust-toolchain.toml pinning nightly."
        ));
    }

    let libdir = rustc_field_from(&["--print", "target-libdir"])?;
    if !has_compiler_libraries(Path::new(&libdir)) {
        return Err(
            "the rustc-dev component is missing, so the analysis driver \
             cannot link against the compiler. Install it with `rustup \
             component add rustc-dev llvm-tools`."
                .to_owned(),
        );
    }
    Ok(())
}

/// Whether the compiler's own libraries are present to link against.
fn has_compiler_libraries(libdir: &Path) -> bool {
    let Ok(entries) = std::fs::read_dir(libdir) else {
        // An unreadable libdir is not proof of a broken toolchain, so let the
        // real build report whatever the actual problem turns out to be.
        return true;
    };
    entries.filter_map(Result::ok).any(|entry| {
        entry
            .file_name()
            .to_string_lossy()
            .starts_with("librustc_middle-")
    })
}

/// Reads one labelled field from `rustc --version --verbose`.
fn rustc_field(label: &str) -> Result<String, String> {
    let text = run(&["--version", "--verbose"])?;
    text.lines()
        .find_map(|line| line.strip_prefix(label))
        .map(|value| value.trim().to_owned())
        .ok_or_else(|| format!("rustc did not report `{label}`"))
}

/// Runs rustc and returns the first line of its output.
fn rustc_field_from(args: &[&str]) -> Result<String, String> {
    Ok(run(args)?.trim().to_owned())
}

/// Runs the compiler that cargo selected for this build.
fn run(args: &[&str]) -> Result<String, String> {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let output = Command::new(&rustc)
        .args(args)
        .output()
        .map_err(|err| format!("could not run {rustc}: {err}"))?;
    String::from_utf8(output.stdout)
        .map_err(|_| format!("{rustc} printed invalid utf-8"))
}

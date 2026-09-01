//! Checks that the toolchain can build the analysis driver.
//!
//! The driver links against compiler internals. Without this check the build
//! fails deep inside the driver with an error about an unstable feature or a
//! missing crate, neither of which tells the reader what to install.

use std::{path::Path, process::Command};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    match check() {
        Ok(banner) => println!("cargo:rustc-env=PANICGRAPH_RUSTC={banner}"),
        Err(problem) => {
            // Printed as a warning so cargo shows it prominently, and
            // repeated on stderr so it survives in a captured log.
            println!("cargo:warning={problem}");
            eprintln!("\npanicgraph: {problem}\n");
            std::process::exit(1);
        }
    }
}

/// Reports the first missing prerequisite, or names the compiler.
///
/// The driver loads that compiler's own libraries, which are named after the
/// build they came from, so it cannot start once the toolchain has moved. The
/// front end compares the name returned here against the compiler it finds
/// and says so, rather than leaving the loader to report a missing file.
fn check() -> Result<String, String> {
    let text = run(&["--version", "--verbose"])?;
    let banner = text.lines().next().unwrap_or_default().trim().to_owned();
    let version = text
        .lines()
        .find_map(|line| line.strip_prefix("release: "))
        .map(str::trim)
        .ok_or_else(|| "rustc did not report `release: `".to_owned())?;
    if !version.contains("nightly") && !version.contains("dev") {
        return Err(format!(
            "the analysis driver reads compiler internals, which needs a \
             nightly toolchain, but this build is using {version}. Install \
             with `cargo +nightly install --path .`, or add a \
             rust-toolchain.toml pinning nightly."
        ));
    }

    let libdir = run(&["--print", "target-libdir"])?;
    if !has_compiler_libraries(Path::new(libdir.trim())) {
        return Err(
            "the rustc-dev component is missing, so the analysis driver \
             cannot link against the compiler. Install it with `rustup \
             component add rustc-dev llvm-tools`."
                .to_owned(),
        );
    }
    Ok(banner)
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

/// Runs the compiler that cargo selected for this build.
fn run(args: &[&str]) -> Result<String, String> {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let output = Command::new(&rustc)
        .args(args)
        .output()
        .map_err(|err| format!("could not run {rustc}: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "{rustc} {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|_| format!("{rustc} printed invalid utf-8"))
}

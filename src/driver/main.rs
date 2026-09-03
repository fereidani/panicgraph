//! Compiler driver that records panic facts from MIR.
//!
//! Cargo runs this in place of `rustc` through `RUSTC_WRAPPER`. Compilation
//! proceeds normally; once analysis finishes, the reachable call graph of the
//! crate is written to the directory named by `PANICGRAPH_OUT`.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;

mod extract;
mod fold;
mod read;
mod sinks;
mod state;
mod summary;
mod value;

use std::{path::PathBuf, process::Command};

use panicgraph::{Artifact, BuildConfig, StdMode};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;

use crate::extract::Extractor;

/// Directory the driver writes artifacts into.
const OUT_DIR: &str = "PANICGRAPH_OUT";

/// Cargo profile the build is running under, supplied by the front end.
const PROFILE: &str = "PANICGRAPH_PROFILE";

/// Which standard library the front end arranged for.
const STD_MODE: &str = "PANICGRAPH_STD_MODE";

/// The MIR optimization level the front end asked for, if any.
const MIR_OPT_LEVEL: &str = "PANICGRAPH_MIR_OPT_LEVEL";

struct PanicGraph;

impl Callbacks for PanicGraph {
    fn after_analysis(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation {
        if let Err(err) = emit(tcx) {
            // A failure to record facts must not fail the user's build.
            eprintln!("panicgraph: could not write artifact: {err}");
        }
        Compilation::Continue
    }
}

/// Extracts the current crate's panic facts and writes them out.
///
/// Only the package under analysis is extracted. Dependencies are walked
/// through their metadata from that crate's own graph, so analysing them
/// separately would repeat the work and pull in bodies nothing calls.
fn emit(tcx: TyCtxt<'_>) -> std::io::Result<()> {
    let Some(dir) = std::env::var_os(OUT_DIR) else {
        return Ok(());
    };
    if std::env::var_os("CARGO_PRIMARY_PACKAGE").is_none() {
        return Ok(());
    }
    let dir = PathBuf::from(dir);
    std::fs::create_dir_all(&dir)?;

    let krate = tcx.crate_name(LOCAL_CRATE).to_string();
    let extraction = Extractor::new(tcx).run();
    let artifact = Artifact {
        krate: krate.clone(),
        config: build_config(tcx),
        bodies: extraction.bodies,
        reified: extraction.reified,
    };

    let stamp = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    let path = dir.join(format!("{krate}-{stamp:016x}.json"));
    let json = serde_json::to_vec(&artifact).map_err(std::io::Error::other)?;
    if let Err(err) = std::fs::write(&path, json) {
        // A write that failed must not leave the previous build's answer
        // where the analysis will read it as though it described this one.
        // A write that never opened the file left nothing behind, and
        // reporting the absence of what it was trying to remove would bury
        // the error that actually stopped it.
        match std::fs::remove_file(&path) {
            Ok(()) => {}
            Err(stuck) if stuck.kind() == std::io::ErrorKind::NotFound => {}
            Err(stuck) => {
                eprintln!(
                    "panicgraph: could not remove the stale artifact {}: \
                     {stuck}",
                    path.display()
                );
            }
        }
        return Err(err);
    }
    Ok(())
}

/// Records the settings that change which panics exist.
fn build_config(tcx: TyCtxt<'_>) -> BuildConfig {
    let debug_assertions = tcx.sess.opts.debug_assertions;
    // The front end writes this with `StdMode::name`, so anything else is
    // the two halves disagreeing. Reporting the artifact under a mode it
    // was not built in would misdescribe every finding in it, so say so
    // rather than settle on a default.
    let raw = std::env::var(STD_MODE).unwrap_or_default();
    let std_mode = StdMode::from_name(&raw).unwrap_or_else(|| {
        if !raw.is_empty() {
            eprintln!(
                "panicgraph: {STD_MODE} is `{raw}`, which names no standard \
                 library mode; reading it as shipped"
            );
        }
        StdMode::Shipped
    });
    BuildConfig {
        rustc: tcx.sess.cfg_version.to_owned(),
        profile: std::env::var(PROFILE)
            .unwrap_or_else(|_| "unknown".to_owned()),
        debug_assertions,
        overflow_checks: tcx
            .sess
            .opts
            .cg
            .overflow_checks
            .unwrap_or(debug_assertions),
        std_mode,
        mir_opt_level: mir_opt_level(),
    }
}

/// The MIR optimization level the front end asked for, if it asked.
fn mir_opt_level() -> Option<u8> {
    std::env::var(MIR_OPT_LEVEL).ok()?.parse().ok()
}

/// Asks the real compiler where its sysroot is.
fn sysroot() -> Option<String> {
    let out = Command::new("rustc").arg("--print=sysroot").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8(out.stdout).ok()?;
    Some(text.trim().to_owned())
}

fn main() -> std::process::ExitCode {
    let mut args: Vec<String> = std::env::args().collect();

    // Cargo passes the real compiler as the first argument when running as a
    // wrapper. Drop it so the argument list is a plain rustc invocation.
    if args.len() > 1 && args[1].ends_with("rustc") {
        args.remove(1);
    }

    if let Some(root) = sysroot() {
        args.push(format!("--sysroot={root}"));
    }

    // Cargo learns about the target by compiling an empty crate it names
    // on standard input, which it opens on the null device. That device is
    // not always what it should be: on a machine where it has become an
    // ordinary file, the probe reads whatever was last written there as
    // the crate. A file the driver empties itself is empty for certain.
    let probe = args
        .iter()
        .any(|arg| arg == "-")
        .then(empty_source)
        .flatten();
    if let Some(path) = &probe {
        for arg in &mut args {
            if arg == "-" {
                path.to_string_lossy().as_ref().clone_into(arg);
            }
        }
    }

    // Without this, dependencies keep MIR only for generic and small items,
    // so concrete functions become opaque and the panics inside them are
    // invisible.
    args.push("-Zalways-encode-mir".to_owned());

    // A level the front end asked for applies to every crate the build
    // compiles, so a body read out of a dependency was optimized the same
    // way as one of the crate under analysis.
    if let Some(level) = mir_opt_level() {
        args.push(format!("-Zmir-opt-level={level}"));
    }

    // A test crate is read for the instantiations it makes of the
    // library's generic functions, and inlining would fold those into the
    // tests, which are not reported. The tests are not what is measured,
    // so keeping their calls as calls costs the analysis nothing.
    if args.iter().any(|arg| arg == "--test") {
        args.push("-Zinline-mir=no".to_owned());
    }

    // The crate under analysis is the leaf of the build, so nothing ever
    // inlines from it, and marking its functions inlinable only makes
    // codegen skip their machine code. Keeping every body in the compiled
    // library is what lets a finding be checked against the artifact.
    // Dependencies are left alone: their inlinability into the leaf is part
    // of what the analysis measures.
    if std::env::var_os("CARGO_PRIMARY_PACKAGE").is_some() {
        args.push("-Zcross-crate-inline-threshold=never".to_owned());
    }

    let code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut PanicGraph);
    });
    if let Some(path) = &probe {
        // The file was only ever the probe's input, so it is not needed
        // once the probe has run; a leftover is a nuisance, not a fault.
        let _ = std::fs::remove_file(path);
    }
    code
}

/// An empty source file for the compiler probe to read.
fn empty_source() -> Option<PathBuf> {
    let path = std::env::temp_dir()
        .join(format!("panicgraph-probe-{}.rs", std::process::id()));
    std::fs::write(&path, b"").ok()?;
    Some(path)
}

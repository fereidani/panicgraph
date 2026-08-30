//! Compiler driver that records panic facts from MIR.
//!
//! Cargo runs this in place of `rustc` through `RUSTC_WRAPPER`. Compilation
//! proceeds normally; once analysis finishes, the reachable call graph of the
//! crate is written to the directory named by `PANICGRAPH_OUT`.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod extract;
mod fold;
mod sinks;
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
    std::fs::write(path, json)
}

/// Records the settings that change which panics exist.
fn build_config(tcx: TyCtxt<'_>) -> BuildConfig {
    let debug_assertions = tcx.sess.opts.debug_assertions;
    let std_mode = match std::env::var(STD_MODE).as_deref() {
        Ok("full") => StdMode::Full,
        _ => StdMode::Shipped,
    };
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
    }
}

/// Asks the real compiler where its sysroot is.
fn sysroot() -> Option<String> {
    let out = Command::new("rustc").arg("--print=sysroot").output().ok()?;
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

    // Without this, dependencies keep MIR only for generic and small items,
    // so concrete functions become opaque and the panics inside them are
    // invisible.
    args.push("-Zalways-encode-mir".to_owned());

    // The crate under analysis is the leaf of the build, so nothing ever
    // inlines from it, and marking its functions inlinable only makes
    // codegen skip their machine code. Keeping every body in the compiled
    // library is what lets a finding be checked against the artifact.
    // Dependencies are left alone: their inlinability into the leaf is part
    // of what the analysis measures.
    if std::env::var_os("CARGO_PRIMARY_PACKAGE").is_some() {
        args.push("-Zcross-crate-inline-threshold=never".to_owned());
    }

    rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut PanicGraph);
    })
}

//! Drives a cargo build through the analysis wrapper and loads the results.

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result, bail};

use crate::{Artifact, StdMode, args::Args};

/// The toolchain this tool was built with.
///
/// The driver links against a specific compiler, so the analysis build has to
/// run under that same toolchain. Without this, cargo would pick whatever the
/// analysed crate's directory resolves to and the driver would be handed a
/// sysroot it cannot read.
const TOOLCHAIN: Option<&str> = option_env!("RUSTUP_TOOLCHAIN");

/// Where the driver writes artifacts and where the analysis build happens.
struct Layout {
    out: PathBuf,
    target: PathBuf,
}

/// Builds the crate under the wrapper and returns every artifact produced.
///
/// # Errors
///
/// Returns an error if the driver is missing, the build fails, or an
/// artifact cannot be read.
pub fn collect(args: &Args) -> Result<Vec<Artifact>> {
    let driver = driver_path()?;
    let root = match &args.manifest_dir {
        Some(dir) => dir.clone(),
        None => env::current_dir()
            .context("could not determine the current directory")?,
    };
    let layout = prepare(&root, args)?;

    build(args, &driver, &root, &layout)?;
    let mut artifacts = load(&layout.out)?;

    if artifacts.is_empty() {
        // Cargo recompiles nothing when the build is already current, so the
        // wrapper never runs and records nothing. Discarding the analysis
        // build is the only way to observe a crate that is already cached.
        if layout.target.exists() {
            fs::remove_dir_all(&layout.target).with_context(|| {
                format!("could not clear {}", layout.target.display())
            })?;
        }
        build(args, &driver, &root, &layout)?;
        artifacts = load(&layout.out)?;
    }

    if artifacts.is_empty() {
        bail!("the build produced no analysis artifacts");
    }
    Ok(artifacts)
}

/// Runs one analysis build.
fn build(
    args: &Args,
    driver: &Path,
    root: &Path,
    layout: &Layout,
) -> Result<()> {
    let mut cmd = Command::new("cargo");
    cmd.current_dir(root)
        .arg("build")
        .arg("--profile")
        .arg(cargo_profile(&args.profile))
        .arg("--target-dir")
        .arg(&layout.target);

    if let Some(pkg) = &args.package {
        cmd.arg("--package").arg(pkg);
    }
    if args.std_mode == StdMode::Full {
        cmd.arg("-Z")
            .arg("build-std=core,alloc,std")
            .arg("--target")
            .arg(host_triple()?);
    }

    cmd.env("RUSTC_WRAPPER", driver)
        .env("PANICGRAPH_OUT", &layout.out)
        .env("PANICGRAPH_PROFILE", &args.profile)
        .env("PANICGRAPH_STD_MODE", args.std_mode.name());
    if let Some(toolchain) = TOOLCHAIN {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    if let Some(path) = library_path()? {
        cmd.env("LD_LIBRARY_PATH", path);
    }

    let status = cmd
        .status()
        .context("could not run cargo; is it on the PATH?")?;
    if !status.success() {
        bail!("the analysis build failed; the errors above are from cargo");
    }
    Ok(())
}

/// Name of the marker written into every directory this version owns.
///
/// Earlier versions wrote artifacts into differently named directories, and
/// those linger as caches nothing will ever read again. The marker tells the
/// two apart without having to guess from the directory name.
const SLOT_MARKER: &str = ".panicgraph-slot";

/// Creates the directories the analysis build writes into.
///
/// Artifacts are deliberately kept between runs. Each is named after the
/// crate that produced it, so cargo rewrites exactly the ones it recompiles
/// and the rest stay valid.
fn prepare(root: &Path, args: &Args) -> Result<Layout> {
    // Artifacts are kept between runs, so the directory has to separate
    // every input that changes what they describe. The standard library mode
    // changes how crates are compiled and so changes their symbol names, and
    // a different package selection analyses a different program: merging
    // those would silently report one crate's panics against another's.
    let base = root.join("target").join("panicgraph");
    let slot = format!(
        "{}-{}-{}",
        args.profile,
        args.std_mode.name(),
        args.package.as_deref().unwrap_or("all"),
    );
    let layout = Layout {
        out: base.join(&slot),
        target: base.join("build"),
    };
    fs::create_dir_all(&layout.out).with_context(|| {
        format!("could not create {}", layout.out.display())
    })?;
    fs::write(layout.out.join(SLOT_MARKER), slot.as_bytes()).with_context(
        || format!("could not write the marker in {}", layout.out.display()),
    )?;
    prune_stale(&base, &layout);
    Ok(layout)
}

/// Removes result directories that no version in use writes to any more.
///
/// A directory is kept when it holds the marker, which every current slot
/// carries, and when it is the shared build tree. Anything else was written
/// by an older layout and would otherwise sit on disk forever.
fn prune_stale(base: &Path, layout: &Layout) {
    let Ok(entries) = fs::read_dir(base) else {
        return;
    };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if !path.is_dir() || path == layout.out || path == layout.target {
            continue;
        }
        if path.join(SLOT_MARKER).exists() {
            continue;
        }
        if fs::remove_dir_all(&path).is_ok() {
            println!("removed stale results in {}", path.display());
        }
    }
}

/// Reads every artifact in a directory.
fn load(dir: &Path) -> Result<Vec<Artifact>> {
    let mut out = Vec::new();
    for entry in fs::read_dir(dir)
        .with_context(|| format!("could not read {}", dir.display()))?
    {
        let path = entry?.path();
        if path.extension().is_none_or(|e| e != "json") {
            continue;
        }
        let text = fs::read(&path)
            .with_context(|| format!("could not read {}", path.display()))?;
        let artifact: Artifact = serde_json::from_slice(&text)
            .with_context(|| format!("could not parse {}", path.display()))?;
        out.push(artifact);
    }
    Ok(out)
}

/// Locates the compiler driver next to this executable.
fn driver_path() -> Result<PathBuf> {
    let exe = env::current_exe().context("could not locate this program")?;
    let dir = exe
        .parent()
        .context("this program has no containing directory")?;
    let driver = dir.join("panicgraph-driver");
    if !driver.exists() {
        bail!(
            "the analysis driver is missing from {}; it is installed \
             alongside this program, so reinstall with `cargo install \
             --path .`",
            dir.display()
        );
    }
    Ok(driver)
}

/// The directory holding the compiler's shared libraries.
///
/// The driver links against the compiler, so this must be on the loader path
/// for it to start at all.
fn library_path() -> Result<Option<OsString>> {
    let Some(sysroot) = sysroot()? else {
        return Ok(None);
    };
    let lib = PathBuf::from(sysroot).join("lib");
    let mut value = lib.into_os_string();
    if let Some(existing) = env::var_os("LD_LIBRARY_PATH") {
        value.push(":");
        value.push(existing);
    }
    Ok(Some(value))
}

/// The compiler's sysroot.
fn sysroot() -> Result<Option<String>> {
    let out = rustc()
        .arg("--print")
        .arg("sysroot")
        .output()
        .context("could not run rustc")?;
    let text =
        String::from_utf8(out.stdout).context("rustc printed invalid utf-8")?;
    let text = text.trim();
    Ok((!text.is_empty()).then(|| text.to_owned()))
}

/// The compiler's host target triple.
fn host_triple() -> Result<String> {
    rustc_field("host: ")?.context("rustc did not report a host triple")
}

/// Reads one labelled field from `rustc --version --verbose`.
fn rustc_field(label: &str) -> Result<Option<String>> {
    let out = rustc()
        .arg("--version")
        .arg("--verbose")
        .output()
        .context("could not run rustc")?;
    let text =
        String::from_utf8(out.stdout).context("rustc printed invalid utf-8")?;
    Ok(text
        .lines()
        .find_map(|l| l.strip_prefix(label))
        .map(str::trim)
        .map(str::to_owned))
}

/// A compiler invocation pinned to this tool's toolchain.
fn rustc() -> Command {
    let mut cmd = Command::new("rustc");
    if let Some(toolchain) = TOOLCHAIN {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    cmd
}

/// Maps a profile name onto the one cargo expects.
fn cargo_profile(profile: &str) -> &str {
    if profile == "debug" { "dev" } else { profile }
}

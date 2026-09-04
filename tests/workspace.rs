//! Telling the standard library's workspace from every other by its
//! manifest.

use panicgraph::run::is_library_manifest;

const LIBRARY: &str = r"
cargo-features = ['profile-rustflags']

[workspace]
resolver = '1'
members = ['std', 'sysroot']

[patch.crates-io]
# See the shim's own README for what is going on here
rustc-std-workspace-core = { path = 'rustc-std-workspace-core' }
rustc-std-workspace-alloc = { path = 'rustc-std-workspace-alloc' }
";

#[test]
fn the_library_workspace_patches_its_shim_in() {
    assert!(is_library_manifest(LIBRARY));
}

#[test]
fn quoting_and_spacing_of_the_patch_do_not_matter() {
    let quoted = "[ patch . \"crates-io\" ]\n\"rustc-std-workspace-core\" = \
                  { path = 'x' }\n";
    assert!(is_library_manifest(quoted));
    let own_table = "[patch.crates-io.rustc-std-workspace-core]\npath = 'x'\n";
    assert!(is_library_manifest(own_table));
}

#[test]
fn a_crate_vendored_into_the_library_is_not_the_library() {
    // Published manifests spell every dependency as a table of its own,
    // under the name the crate uses for it.
    let renamed = "[dependencies.core]\nversion = \"1.0\"\noptional = true\n\
                   package = \"rustc-std-workspace-core\"\n";
    assert!(!is_library_manifest(renamed));
    let named = "[dependencies.rustc-std-workspace-core]\nversion = \"1.0\"\n\
                 optional = true\n";
    assert!(!is_library_manifest(named));
    let inline = "[dependencies]\nrustc-std-workspace-core = \
                  { version = \"1.0\", optional = true }\n";
    assert!(!is_library_manifest(inline));
}

#[test]
fn patching_something_else_is_not_the_library() {
    let other = "[patch.crates-io]\nserde = { path = 'serde' }\n\n\
                 [dependencies]\nrustc-std-workspace-core = \"1.0\"\n";
    assert!(!is_library_manifest(other));
    let commented = "[patch.crates-io]\n# rustc-std-workspace-core = \
                     { path = 'x' }\n";
    assert!(!is_library_manifest(commented));
}

#[test]
fn an_ordinary_manifest_is_not_the_library() {
    let plain = "[package]\nname = \"x\"\nversion = \"0.1.0\"\n\n\
                 [dependencies]\nserde = \"1\"\n";
    assert!(!is_library_manifest(plain));
}

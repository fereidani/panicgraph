//! Command line parsing.

use panicgraph::{
    Category, CategorySet, StdMode,
    args::{self, Command, Format},
};

/// Parses a borrowed argument list.
fn parse(argv: &[&str]) -> anyhow::Result<args::Args> {
    args::parse(argv.iter().map(|s| (*s).to_owned()))
}

#[test]
fn defaults_suppress_allocation_noise() {
    let args = parse(&[]).expect("an empty argument list is valid");
    assert!(matches!(args.command, Command::Analyze));
    assert!(args.suppress.contains(Category::CapacityOverflow));
    assert!(args.suppress.contains(Category::AllocFailure));
    assert!(
        !args.suppress.contains(Category::Unwrap),
        "interesting panics are never suppressed by default"
    );
    assert_eq!(args.std_mode, StdMode::Shipped);
    assert_eq!(args.format, Format::Human);
}

#[test]
fn suppression_can_be_cleared() {
    let args = parse(&["--suppress", ""]).expect("an empty list is valid");
    assert_eq!(args.suppress, CategorySet::EMPTY);
}

#[test]
fn categories_are_named_individually() {
    let args =
        parse(&["--only", "unwrap,index"]).expect("both names are valid");
    let only = args.only.expect("--only was given");
    assert!(only.contains(Category::Unwrap));
    assert!(only.contains(Category::Index));
    assert!(!only.contains(Category::Explicit));
}

#[test]
fn why_takes_a_function_name() {
    let args = parse(&["why", "mycrate::parse"]).expect("a name was given");
    match args.command {
        Command::Why { function } => assert_eq!(function, "mycrate::parse"),
        other => panic!("expected a why command, got {other:?}"),
    }
}

#[test]
fn why_without_a_name_is_rejected() {
    assert!(parse(&["why"]).is_err());
}

#[test]
fn unknown_category_is_rejected_with_its_name() {
    let err = parse(&["--suppress", "nonsense"])
        .expect_err("the category does not exist");
    assert!(
        err.to_string().contains("nonsense"),
        "the message should name the offending token, got: {err}"
    );
}

#[test]
fn unknown_flag_is_rejected() {
    assert!(parse(&["--wat"]).is_err());
}

#[test]
fn flags_needing_values_are_checked() {
    assert!(parse(&["--profile"]).is_err());
    assert!(parse(&["--format"]).is_err());
}

#[test]
fn std_mode_is_selectable() {
    let args = parse(&["--std", "full"]).expect("full is a valid mode");
    assert_eq!(args.std_mode, StdMode::Full);
    assert!(parse(&["--std", "partial"]).is_err());
}

//! Parsing of the `-l` listen argument.

#![cfg(feature = "serve")]

use std::net::{IpAddr, Ipv4Addr};

use panicgraph::args;

/// Parses a borrowed argument list.
fn parse(argv: &[&str]) -> anyhow::Result<args::Args> {
    args::parse(argv.iter().map(|s| (*s).to_owned()))
}

#[test]
fn absent_by_default() {
    let args = parse(&[]).expect("an empty argument list is valid");
    assert!(args.listen.is_none());
}

#[test]
fn a_bare_port_binds_loopback_only() {
    let args = parse(&["-l", "8080"]).expect("a bare port is valid");
    let addr = args.listen.expect("-l was given");
    assert_eq!(addr.port(), 8080);
    assert_eq!(
        addr.ip(),
        IpAddr::V4(Ipv4Addr::LOCALHOST),
        "a bare port must never open on every interface, because this serves \
         the source of the crate being analysed"
    );
}

#[test]
fn an_explicit_host_is_honoured() {
    let args =
        parse(&["-l", "0.0.0.0:9001"]).expect("an explicit host is valid");
    let addr = args.listen.expect("-l was given");
    assert_eq!(addr.port(), 9001);
    assert_eq!(addr.ip(), IpAddr::V4(Ipv4Addr::UNSPECIFIED));
}

#[test]
fn the_long_spelling_works_too() {
    let args = parse(&["--listen", "127.0.0.1:1234"]).expect("valid address");
    assert_eq!(args.listen.map(|a| a.port()), Some(1234));
}

#[test]
fn a_missing_value_is_rejected() {
    assert!(parse(&["-l"]).is_err());
}

#[test]
fn an_unresolvable_host_is_rejected() {
    assert!(parse(&["-l", "not a host:99999999"]).is_err());
}

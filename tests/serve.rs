//! Behaviour of the interactive view's HTTP server.

#![cfg(feature = "serve")]

use std::{
    io::{Read, Write},
    net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream},
    thread,
};

use panicgraph::{Graph, serve};

/// One response, split into its head and body.
struct Response {
    head: String,
    body: Vec<u8>,
}

impl Response {
    /// Whether a header line is present, matched case insensitively.
    fn has(&self, needle: &str) -> bool {
        self.head
            .to_ascii_lowercase()
            .contains(&needle.to_ascii_lowercase())
    }

    /// The value of the `Content-Length` header.
    fn content_length(&self) -> usize {
        self.head
            .to_ascii_lowercase()
            .lines()
            .find_map(|line| line.strip_prefix("content-length:"))
            .and_then(|value| value.trim().parse().ok())
            .unwrap_or(0)
    }
}

/// Starts a server on an ephemeral port and returns its address.
fn start() -> SocketAddr {
    let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0))
        .expect("the loopback interface should accept an ephemeral port");
    let addr = listener
        .local_addr()
        .expect("a bound listener should report its address");
    thread::spawn(move || {
        let graph = Graph::from_artifacts(Vec::new());
        let _ = serve::serve_on(
            &listener,
            graph,
            panicgraph::solve::Edges::default(),
        );
    });
    addr
}

/// Issues one request and reads the whole reply.
fn get(addr: SocketAddr, path: &str, accept_gzip: bool) -> Response {
    let mut stream =
        TcpStream::connect(addr).expect("the server should accept a client");
    let encoding = if accept_gzip {
        "Accept-Encoding: gzip\r\n"
    } else {
        ""
    };
    let request =
        format!("GET {path} HTTP/1.1\r\nHost: localhost\r\n{encoding}\r\n");
    stream
        .write_all(request.as_bytes())
        .expect("the request should be written");

    let mut raw = Vec::new();
    stream
        .read_to_end(&mut raw)
        .expect("the reply should be readable");
    let split = raw
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("a reply should have a header terminator");
    Response {
        head: String::from_utf8_lossy(&raw[..split]).into_owned(),
        body: raw[split + 4..].to_vec(),
    }
}

#[test]
fn a_client_that_accepts_gzip_receives_it() {
    let addr = start();
    let packed = get(addr, "/d3.min.js", true);
    assert!(packed.has("content-encoding: gzip"));
    assert!(
        packed.has("vary: accept-encoding"),
        "a compressed reply must not be cached for clients that cannot \
         decode it"
    );
    assert_eq!(
        packed.body.len(),
        packed.content_length(),
        "the length must describe the bytes actually sent"
    );
    assert_eq!(
        &packed.body[..2],
        &[0x1f, 0x8b],
        "the body should carry the gzip magic number"
    );
}

#[test]
fn a_client_that_does_not_accept_gzip_receives_plain_bytes() {
    let addr = start();
    let plain = get(addr, "/d3.min.js", false);
    assert!(!plain.has("content-encoding"));
    assert_eq!(plain.body.len(), plain.content_length());
    assert!(
        plain.body.starts_with(b"// https://d3js.org"),
        "an uncompressed reply should be the asset itself"
    );
}

#[test]
fn compression_shrinks_a_large_asset() {
    let addr = start();
    let plain = get(addr, "/d3.min.js", false);
    let packed = get(addr, "/d3.min.js", true);
    assert!(
        packed.body.len() * 2 < plain.body.len(),
        "compressing a large script should at least halve it, got {} from {}",
        packed.body.len(),
        plain.body.len()
    );
}

#[test]
fn a_small_reply_is_left_alone() {
    let addr = start();
    let missing = get(addr, "/nothing-here", true);
    assert!(missing.has("404"));
    assert!(
        !missing.has("content-encoding"),
        "a reply shorter than the gzip header saves nothing by being \
         compressed"
    );
}

#[test]
fn json_endpoints_compress_too() {
    let addr = start();
    let packed = get(addr, "/api/graph", true);
    assert!(packed.has("application/json"));
    assert_eq!(packed.body.len(), packed.content_length());
}

#[test]
fn an_unknown_path_is_a_not_found() {
    let addr = start();
    assert!(get(addr, "/api/nope", false).has("404"));
}

#[test]
fn an_escape_before_a_multibyte_character_is_answered() {
    let addr = start();
    // The two characters after a `%` need not sit on a character boundary,
    // and a decoder that slices the text through one takes the connection
    // down with it.
    let reply = get(addr, "/api/source?file=%\u{20ac}x", false);
    assert!(
        reply.head.starts_with("HTTP/1.1 "),
        "a malformed escape must be answered, not dropped"
    );
}

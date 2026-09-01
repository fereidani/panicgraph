//! A small HTTP server for the interactive view.
//!
//! This serves one page and a handful of JSON endpoints on the loopback
//! interface. It is deliberately dependency free apart from compression: the
//! surface is a few routes, and a web framework would be a larger liability
//! than the code it replaces.

use std::{
    io::{BufRead, BufReader, ErrorKind, Read, Write},
    net::{SocketAddr, TcpListener, TcpStream},
    sync::{Arc, OnceLock},
};

use anyhow::{Context, Result};
use flate2::{Compression, write::GzEncoder};

use crate::{CategorySet, Graph, api, parse_selector, solve::Edges, util::Set};

/// Largest request head accepted, which is ample for a local browser.
const MAX_HEAD_BYTES: u64 = 16 * 1024;

/// Largest number of header lines accepted.
const MAX_HEADER_LINES: usize = 100;

/// Bodies below this size are sent as they are, because the header and the
/// deflate block cost more than the saving.
const COMPRESS_ABOVE: usize = 900;

/// Content type used for the page shell.
const HTML: &str = "text/html; charset=utf-8";
/// Content type used for every script this server returns.
const JS: &str = "application/javascript; charset=utf-8";
/// Content type used for every JSON response.
const JSON: &str = "application/json; charset=utf-8";

/// The page shell.
const INDEX_HTML: &str = include_str!("../assets/index.html");
/// The view itself.
const APP_JS: &str = include_str!("../assets/app.js");
/// Vendored so the view works without network access.
const D3_JS: &str = include_str!("../assets/d3.min.js");
/// Vendored so the view works without network access.
const VUE_JS: &str = include_str!("../assets/vue.global.prod.js");

/// Everything a request handler needs.
struct State {
    graph: Graph,
    sources: Set<String>,
    edges: Edges,
}

/// One parsed request.
struct Request {
    target: String,
    gzip: bool,
}

/// Writes responses for one connection, compressing when the client asked.
struct Responder<'a> {
    stream: &'a TcpStream,
    gzip: bool,
}

impl Responder<'_> {
    /// Writes one complete response, compressing the body when that is worth
    /// doing and the client advertised support.
    fn send(&self, status: u16, content_type: &str, body: &[u8]) -> Result<()> {
        let compressed = self.maybe_compress(body)?;
        let payload = compressed.as_deref().unwrap_or(body);
        self.write(status, content_type, payload, compressed.is_some())
    }

    /// Writes a response whose compressed form is already known.
    fn send_cached(
        &self,
        content_type: &str,
        plain: &[u8],
        packed: &[u8],
    ) -> Result<()> {
        // No packed bytes means compression failed. An empty body is not
        // what the asset says, and it would win the comparison below, so
        // the plain bytes have to be what goes out.
        let use_packed =
            self.gzip && !packed.is_empty() && packed.len() < plain.len();
        let payload = if use_packed { packed } else { plain };
        self.write(200, content_type, payload, use_packed)
    }

    /// Compresses a body, or returns `None` when it is not worth it.
    fn maybe_compress(&self, body: &[u8]) -> Result<Option<Vec<u8>>> {
        if !self.gzip || body.len() < COMPRESS_ABOVE {
            return Ok(None);
        }
        let packed = gzip(body)?;
        Ok((packed.len() < body.len()).then_some(packed))
    }

    /// Writes the status line, the headers, and the body as it stands.
    fn write(
        &self,
        status: u16,
        content_type: &str,
        payload: &[u8],
        compressed: bool,
    ) -> Result<()> {
        let reason = if status == 200 { "OK" } else { "Error" };
        let encoding = if compressed {
            "Content-Encoding: gzip\r\n"
        } else {
            ""
        };
        let head = format!(
            "HTTP/1.1 {status} {reason}\r\n\
             Content-Type: {content_type}\r\n\
             Content-Length: {}\r\n\
             {encoding}\
             Vary: Accept-Encoding\r\n\
             Cache-Control: no-store\r\n\
             Connection: close\r\n\r\n",
            payload.len()
        );
        let mut stream = self.stream;
        stream.write_all(head.as_bytes())?;
        stream.write_all(payload)?;
        stream.flush()?;
        Ok(())
    }

    /// Writes one embedded asset, deflating it at most once per process so
    /// a static file is not compressed again on every page load.
    fn asset(
        &self,
        content_type: &str,
        cell: &'static OnceLock<Vec<u8>>,
        text: &str,
    ) -> Result<()> {
        let packed =
            cell.get_or_init(|| gzip(text.as_bytes()).unwrap_or_default());
        self.send_cached(content_type, text.as_bytes(), packed)
    }

    /// Writes a JSON response.
    fn json(&self, value: &serde_json::Value) -> Result<()> {
        self.send(200, JSON, &serde_json::to_vec(value)?)
    }

    /// Writes an error as JSON, so the view can show it rather than hanging.
    fn fail(&self, err: &anyhow::Error) -> Result<()> {
        let body = serde_json::json!({ "error": format!("{err:#}") });
        self.send(400, JSON, &serde_json::to_vec(&body)?)
    }

    /// Writes a plain text response.
    fn text(&self, status: u16, body: &str) -> Result<()> {
        self.send(status, "text/plain; charset=utf-8", body.as_bytes())
    }

    /// Answers with a value or with the error that produced it.
    fn result(&self, outcome: Result<serde_json::Value>) -> Result<()> {
        match outcome {
            Ok(value) => self.json(&value),
            Err(err) => self.fail(&err),
        }
    }
}

/// Compresses a body with gzip.
fn gzip(body: &[u8]) -> Result<Vec<u8>> {
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(body)?;
    Ok(encoder.finish()?)
}

/// Serves the interactive view until the process is stopped.
///
/// # Errors
///
/// Returns an error if the address cannot be bound.
pub fn run(graph: Graph, addr: SocketAddr, edges: Edges) -> Result<()> {
    let listener = TcpListener::bind(addr)
        .with_context(|| format!("could not bind {addr}"))?;
    let bound = listener.local_addr().unwrap_or(addr);
    println!("panicgraph is serving http://{bound}");
    println!("press ctrl-c to stop");
    serve_on(&listener, graph, edges)
}

/// Serves on an already bound listener.
///
/// Splitting this out lets a caller choose the port, which is how the tests
/// take an ephemeral one instead of racing for a fixed number.
///
/// # Errors
///
/// Returns an error only if the listener stops yielding connections.
pub fn serve_on(
    listener: &TcpListener,
    graph: Graph,
    edges: Edges,
) -> Result<()> {
    let sources = api::source_allowlist(&graph);
    let state = Arc::new(State {
        graph,
        sources,
        edges,
    });

    // A server runs until it is stopped. Each connection is handled on its
    // own thread and returns as soon as the response is written.
    for stream in listener.incoming() {
        let stream = match stream {
            Ok(stream) => stream,
            // A connection lost or a signal caught while waiting says
            // nothing about the next one. Anything else is the listener
            // itself failing, and retrying it would spin.
            Err(err)
                if matches!(
                    err.kind(),
                    ErrorKind::ConnectionAborted | ErrorKind::Interrupted
                ) =>
            {
                continue;
            }
            Err(err) => {
                return Err(err).context("could not accept a connection");
            }
        };
        let state = Arc::clone(&state);
        std::thread::spawn(move || {
            if let Err(err) = handle(&stream, &state) {
                eprintln!("panicgraph: request failed: {err}");
            }
        });
    }
    Ok(())
}

/// Reads one request and writes one response.
fn handle(stream: &TcpStream, state: &State) -> Result<()> {
    let Some(request) = read_request(stream)? else {
        let out = Responder {
            stream,
            gzip: false,
        };
        return out.text(400, "bad request");
    };
    let out = Responder {
        stream,
        gzip: request.gzip,
    };
    let (path, query) = split_once_or(&request.target, '?');
    route(&out, state, path, query)
}

/// Chooses a handler for one request path.
fn route(
    out: &Responder<'_>,
    state: &State,
    path: &str,
    query: &str,
) -> Result<()> {
    static APP: OnceLock<Vec<u8>> = OnceLock::new();
    static D3: OnceLock<Vec<u8>> = OnceLock::new();
    static VUE: OnceLock<Vec<u8>> = OnceLock::new();
    static INDEX: OnceLock<Vec<u8>> = OnceLock::new();

    match path {
        "/" | "/index.html" => out.asset(HTML, &INDEX, INDEX_HTML),
        "/app.js" => out.asset(JS, &APP, APP_JS),
        "/d3.min.js" => out.asset(JS, &D3, D3_JS),
        "/vue.global.prod.js" => out.asset(JS, &VUE, VUE_JS),
        "/api/graph" => out.json(&api::graph(&state.graph)),
        "/api/solve" => out.result(api::solve(
            &state.graph,
            suppressed_from(query),
            state.edges,
        )),
        "/api/flame" => out.result(api::flame(
            &state.graph,
            suppressed_from(query),
            state.edges,
            param(query, "expand").is_none(),
        )),
        "/api/why" => out.result(node_of(query).and_then(|node| {
            api::why(
                &state.graph,
                node,
                &param(query, "category").unwrap_or_default(),
                suppressed_from(query),
                state.edges,
            )
        })),
        "/api/source" => out.result(api::source(
            &state.sources,
            &param(query, "file").unwrap_or_default(),
        )),
        _ => out.text(404, "not found"),
    }
}

/// Reads the suppression policy out of a query string.
fn suppressed_from(query: &str) -> CategorySet {
    param(query, "suppress").map_or(CategorySet::EMPTY, |text| {
        parse_selector(&text).unwrap_or(CategorySet::EMPTY)
    })
}

/// Reads the request line and the one header the server acts on.
fn read_request(stream: &TcpStream) -> Result<Option<Request>> {
    let mut reader = BufReader::new(stream.take(MAX_HEAD_BYTES));
    let mut line = String::new();
    if reader.read_line(&mut line)? == 0 {
        return Ok(None);
    }
    let mut parts = line.split_whitespace();
    let method = parts.next().unwrap_or_default();
    let target = parts.next().unwrap_or_default().to_owned();
    if method != "GET" || target.is_empty() {
        return Ok(None);
    }

    // Drain the headers so the client sees a clean read before the response,
    // noting the only one that changes what is sent.
    let mut gzip = false;
    for _ in 0..MAX_HEADER_LINES {
        let mut header = String::new();
        if reader.read_line(&mut header)? == 0 || header.trim().is_empty() {
            break;
        }
        let lower = header.to_ascii_lowercase();
        if let Some(value) = lower.strip_prefix("accept-encoding:") {
            gzip = value.split(',').any(|token| {
                token.split(';').next().unwrap_or_default().trim() == "gzip"
            });
        }
    }
    Ok(Some(Request { target, gzip }))
}

/// Splits on the first occurrence of a separator.
fn split_once_or(text: &str, sep: char) -> (&str, &str) {
    text.split_once(sep).unwrap_or((text, ""))
}

/// Reads one parameter out of a query string.
fn param(query: &str, name: &str) -> Option<String> {
    query.split('&').find_map(|pair| {
        let (key, value) = split_once_or(pair, '=');
        (key == name).then(|| percent_decode(value))
    })
}

/// The function a request asks about.
///
/// An index that does not read as a number is a mistake worth naming. Taking
/// it for the first function instead would explain a function nobody asked
/// about, which reads as an answer rather than as the error it is.
fn node_of(query: &str) -> Result<usize> {
    let Some(text) = param(query, "node") else {
        return Ok(0);
    };
    text.parse()
        .with_context(|| format!("`{text}` is not a function index"))
}

/// The two hexadecimal digits of the percent escape at `at`.
///
/// Read from the bytes rather than by slicing the text: the two characters
/// after a `%` need not begin a character, and slicing a string through one
/// panics.
fn escape(bytes: &[u8], at: usize) -> Option<(u8, u8)> {
    let (Some(hi), Some(lo)) = (nibble(bytes, at + 1), nibble(bytes, at + 2))
    else {
        return None;
    };
    Some((hi, lo))
}

/// One hexadecimal digit of an escape, as its value.
fn nibble(bytes: &[u8], at: usize) -> Option<u8> {
    let &digit = bytes.get(at)?;
    Some(match digit {
        b'0'..=b'9' => digit - b'0',
        b'a'..=b'f' => digit - b'a' + 10,
        b'A'..=b'F' => digit - b'A' + 10,
        // Anything else is not an escape, so the `%` stands for itself.
        _ => return None,
    })
}

/// Decodes percent escapes and `+` in a query value.
fn percent_decode(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    // Each pass consumes at least one byte, so this ends within the input.
    while i < bytes.len() {
        match bytes[i] {
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b'%' if let Some((hi, lo)) = escape(bytes, i) => {
                out.push(hi * 16 + lo);
                i += 3;
            }
            byte => {
                out.push(byte);
                i += 1;
            }
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

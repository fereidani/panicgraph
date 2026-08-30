//! The standalone flame graph.

#![cfg(feature = "svg")]

mod support;

use panicgraph::{Body, Category, CategorySet, svg};

use crate::support::{BodyBuilder, graph};

/// A function that panics once, under the given name.
fn body(name: &str, category: Category) -> Body {
    BodyBuilder::new(name).panics(category).build()
}

/// Renders a graph of the given functions.
fn render(bodies: Vec<Body>) -> String {
    let mut out = String::new();
    svg::render(&graph(bodies), CategorySet::EMPTY, true, true, &mut out)
        .expect("the graph should render");
    out
}

/// Removes the embedded styling and script, whose contents are not markup
/// and would otherwise be read as tags.
fn markup_only(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) =
        rest.find("<style>").or_else(|| rest.find("<script"))
    {
        out.push_str(&rest[..start]);
        let after = &rest[start..];
        let end = after
            .find("</style>")
            .map(|i| i + "</style>".len())
            .or_else(|| after.find("</script>").map(|i| i + "</script>".len()));
        match end {
            Some(i) => rest = &after[i..],
            None => return out,
        }
    }
    out.push_str(rest);
    out
}

/// Rejects anything that is not well formed, so a broken document fails here
/// rather than in whatever opens it.
fn parse(text: &str) {
    let markup = markup_only(text);
    let mut depth = 0i32;
    let mut chars = markup.chars().peekable();
    let mut in_tag = false;
    while let Some(c) = chars.next() {
        match c {
            '<' => match chars.peek() {
                Some('/') => {
                    in_tag = true;
                    depth -= 1;
                }
                Some('?' | '!') => in_tag = false,
                _ => {
                    in_tag = true;
                    depth += 1;
                }
            },
            '/' if in_tag && chars.peek() == Some(&'>') => depth -= 1,
            '>' => in_tag = false,
            _ => {}
        }
    }
    assert_eq!(depth, 0, "every element should be closed");
}

#[test]
fn the_document_stands_alone() {
    let out = render(vec![body("parse", Category::Unwrap)]);
    assert!(out.starts_with("<?xml"));
    assert!(out.trim_end().ends_with("</svg>"));
    assert!(out.contains("<style>"), "styling travels with the file");
    assert!(
        out.contains("<script"),
        "so does the script that explores it"
    );
    assert!(
        !out.contains("http://127.0.0.1"),
        "nothing may point at a server that will not be running"
    );
    parse(&out);
}

#[test]
fn a_rust_path_does_not_break_the_document() {
    // Generic arguments and trait qualification put angle brackets and
    // ampersands straight into a name.
    let name = "<Vec<T> as Index<&'a str>>::index & \"more\"";
    let out = render(vec![body(name, Category::Index)]);
    assert!(
        !out.contains("<Vec<T>"),
        "the raw brackets would have closed the tag"
    );
    assert!(out.contains("&lt;Vec&lt;T&gt;"));
    assert!(out.contains("&amp;"));
    assert!(out.contains("&quot;"));
    parse(&out);
}

#[test]
fn every_frame_carries_a_title_so_it_reads_without_script() {
    let out = render(vec![
        body("parse", Category::Unwrap),
        body("read", Category::Index),
    ]);
    let frames = out.matches("<g class=\"f\"").count();
    let titles = out.matches("<title>").count();
    assert!(frames > 0);
    assert_eq!(frames, titles, "a frame with no title is mute when hovered");
}

#[test]
fn a_panic_is_named_not_only_coloured() {
    let out = render(vec![body("parse", Category::Unwrap)]);
    assert!(
        out.contains("unwrap panic"),
        "the category belongs in the text, not in the fill alone"
    );
}

#[test]
fn an_empty_graph_still_renders() {
    let out = render(Vec::new());
    assert!(out.contains("</svg>"));
    parse(&out);
}

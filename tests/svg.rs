//! The standalone flame graph.

#![cfg(feature = "svg")]

mod support;

use panicgraph::{
    Body, Category, CategorySet,
    palette::{Palette, Theme},
    solve::Edges,
    svg::{self, View},
};

use crate::support::{BodyBuilder, graph};

/// A function that panics once, under the given name.
fn body(name: &str, category: Category) -> Body {
    BodyBuilder::new(name).panics(category).build()
}

/// A view of everything, folded, in the light theme.
fn view() -> View {
    View {
        suppressed: CategorySet::EMPTY,
        only: None,
        edges: Edges::default(),
        fold: true,
        theme: Theme::Light,
    }
}

/// Renders a graph of the given functions.
fn render(bodies: Vec<Body>) -> String {
    render_view(bodies, view())
}

/// Renders a graph of the given functions, seen the given way.
fn render_view(bodies: Vec<Body>, view: View) -> String {
    let mut out = String::new();
    svg::render(&graph(bodies), view, &mut out)
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

/// Every value the named attribute takes anywhere in the text.
fn values_of<'a>(text: &'a str, name: &str) -> Vec<&'a str> {
    let key = format!(" {name}=\"");
    let mut values = Vec::new();
    let mut rest = text;
    while let Some(start) = rest.find(&key) {
        let value = &rest[start + key.len()..];
        let end = value.find('"').expect("an attribute value ends");
        values.push(&value[..end]);
        rest = &value[end..];
    }
    values
}

/// The lines of the frame with the given name: its group, its title, its
/// rect and its label.
fn frame<'a>(out: &'a str, name: &str) -> Vec<&'a str> {
    let lines: Vec<&str> = out.lines().collect();
    let key = format!("data-name=\"{name}\"");
    let at = lines
        .iter()
        .position(|line| {
            line.starts_with("<g class=\"f\"") && line.contains(&key)
        })
        .unwrap_or_else(|| panic!("no frame is named {name}"));
    lines[at..at + 4].to_vec()
}

/// Where the named frame starts, in the units the file is laid out in.
fn frame_x(out: &str, name: &str) -> f64 {
    values_of(frame(out, name)[0], "data-x")[0]
        .parse()
        .expect("data-x is a number")
}

/// The fill of the named frame.
fn frame_fill<'a>(out: &'a str, name: &str) -> &'a str {
    values_of(frame(out, name)[2], "fill")[0]
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
    // The mark carries the one title that is not a frame's.
    assert_eq!(
        frames + 1,
        titles,
        "a frame with no title is mute when hovered"
    );
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

#[test]
fn the_picture_carries_the_controls_it_describes() {
    let out = render(vec![body("parse", Category::Unwrap)]);
    for id in [
        "title", "subtitle", "unzoom", "search", "matched", "detail", "note",
    ] {
        assert!(
            out.contains(&format!("id=\"{id}\"")),
            "the {id} element is what the script reads and writes"
        );
    }
    assert!(
        out.contains("id=\"frames\""),
        "the frames travel in one group, which is what the script walks"
    );
    for rule in [".hide", ".parent rect", ".match rect", ".ctl"] {
        assert!(
            out.contains(rule),
            "the {rule} rule is what a zoom or a search turns on"
        );
    }
    parse(&out);
}

#[test]
fn the_assumptions_are_written_on_the_picture() {
    let bare = render(vec![body("parse", Category::Unwrap)]);
    assert!(
        bare.contains("assuming nothing impossible"),
        "a graph drawn under no assumption has to say so"
    );

    let assumed = render_view(
        vec![body("parse", Category::Unwrap)],
        View {
            suppressed: CategorySet::oom(),
            ..view()
        },
    );
    assert!(
        assumed.contains("assuming impossible:"),
        "a graph is only readable beside the policy it was drawn under"
    );
    assert!(assumed.contains("alloc-failure"));
    parse(&assumed);
}

#[test]
fn a_selection_narrows_what_is_drawn_and_is_written_on_the_picture() {
    let bodies = || {
        vec![
            body("parse", Category::Unwrap),
            body("read", Category::Index),
        ]
    };
    let all = render(bodies());
    assert!(all.contains("unwrap panic") && all.contains("index panic"));

    let some = render_view(
        bodies(),
        View {
            only: Some(CategorySet::single(Category::Unwrap)),
            ..view()
        },
    );
    assert!(some.contains("unwrap panic"), "the selection is drawn");
    assert!(!some.contains("index panic"), "the rest is not");
    assert!(
        some.contains("showing only: unwrap"),
        "the picture says what it was narrowed to"
    );
    parse(&some);
}

#[test]
fn a_frame_carries_what_the_script_zooms_and_searches_with() {
    let out = render(vec![
        body("parse", Category::Unwrap),
        body("read", Category::Index),
    ]);
    let frames = out.matches("<g class=\"f\"").count();
    assert!(frames > 0);
    for attribute in ["data-x=", "data-w=", "data-y=", "data-name="] {
        assert_eq!(
            out.matches(attribute).count(),
            frames,
            "every frame needs {attribute} for the script to place it again"
        );
    }
}

#[test]
fn the_picture_is_as_wide_as_the_window() {
    let out = render(vec![
        body("parse", Category::Unwrap),
        body("read", Category::Index),
    ]);
    assert!(
        out.contains("<svg version=\"1.1\" width=\"100%\""),
        "the drawing takes the width of whatever holds it"
    );
    assert!(
        out.contains("viewBox=\"0 0 1200 "),
        "and names the width it was fitted for, which a viewer without \
         scripting scales as a whole"
    );
    assert!(
        out.contains("<svg id=\"frames\" x=\"10\" width=\"1180\">"),
        "the frames keep the margin flame graphs keep at either side"
    );

    // Every frame is placed as a share of the width, never at a pixel, so
    // it stretches with the window, and every frame has a label element to
    // write its name into once it has the room.
    let frames = out.matches("<g class=\"f\"").count();
    assert!(frames > 0);
    let rects: Vec<&str> = out
        .lines()
        .filter(|line| line.starts_with("<rect x="))
        .collect();
    let labels: Vec<&str> = out
        .lines()
        .filter(|line| {
            line.starts_with("<text x=") && line.contains("class=\"l\"")
        })
        .collect();
    assert_eq!(rects.len(), frames, "one rect per frame");
    assert_eq!(labels.len(), frames, "one label per frame");
    for tag in rects.iter().chain(&labels) {
        for value in values_of(tag, "x") {
            assert!(value.ends_with('%'), "{tag} is placed at a pixel");
        }
    }
    for tag in &rects {
        for value in values_of(tag, "width") {
            assert!(value.ends_with('%'), "{tag} is sized in pixels");
        }
    }
}

#[test]
fn the_picture_is_signed_with_the_project_mark() {
    let out = render(vec![body("parse", Category::Unwrap)]);
    let lockup = include_str!("../assets/panicgraph-lockup.svg");
    // The mark is the one the interactive view shows, stroke for stroke.
    let strokes = values_of(lockup, "d");
    assert!(!strokes.is_empty(), "the lockup draws its mark with paths");
    for stroke in strokes {
        assert!(
            out.contains(&format!("d=\"{stroke}\"")),
            "the stroke {stroke} is missing from the mark"
        );
    }
    assert!(out.contains(">PanicGraph<"), "the name goes with the mark");
    assert!(
        out.contains(&format!("href=\"{}\"", env!("CARGO_PKG_REPOSITORY"))),
        "the mark links to the project"
    );
    assert!(
        out.contains(&format!("PanicGraph {}", env!("CARGO_PKG_VERSION"))),
        "the tooltip names the version that drew the file"
    );
    parse(&out);
}

#[test]
fn the_dark_theme_draws_on_a_dark_page_in_its_own_ink() {
    let out = render_view(
        vec![body("parse", Category::Unwrap)],
        View {
            theme: Theme::Dark,
            ..view()
        },
    );
    let colours = Palette::load(Theme::Dark).expect("the palette loads");
    let colours = colours.colours();
    assert!(
        out.contains(&format!(
            "<rect width=\"100%\" height=\"100%\" fill=\"{}\"/>",
            colours.page
        )),
        "the page takes the theme's colour"
    );
    assert!(
        out.contains(&format!("stroke=\"{}\"", colours.brand)),
        "the mark takes the theme's ink"
    );
    assert!(
        out.contains(&format!("fill: {};", colours.ink)),
        "so does the title"
    );
    parse(&out);
}

#[test]
fn each_category_takes_a_step_of_its_own() {
    let out = render_view(
        vec![
            body("parse", Category::Unwrap),
            body("read", Category::Index),
        ],
        View {
            fold: false,
            ..view()
        },
    );
    let palette = Palette::load(Theme::Light).expect("the palette loads");
    assert_eq!(frame_fill(&out, "unwrap"), palette.panic(Category::Unwrap));
    assert_eq!(frame_fill(&out, "index"), palette.panic(Category::Index));
    assert_ne!(
        frame_fill(&out, "unwrap"),
        frame_fill(&out, "index"),
        "two panics of one family are still told apart"
    );
}

#[test]
fn siblings_band_by_family_and_a_call_takes_the_tint_of_what_is_under_it() {
    // Named so that the alphabet would order them differently from the
    // families, which is what decides.
    let out = render_view(
        vec![
            body("a_alloc", Category::CapacityOverflow),
            body("b_logic", Category::Unwrap),
            body("c_unsure", Category::Unknown),
        ],
        View {
            fold: false,
            ..view()
        },
    );
    assert!(
        frame_x(&out, "b_logic") < frame_x(&out, "a_alloc"),
        "logic leads"
    );
    assert!(
        frame_x(&out, "a_alloc") < frame_x(&out, "c_unsure"),
        "allocation comes before what is unverified"
    );

    let palette = Palette::load(Theme::Light).expect("the palette loads");
    let calls = &palette.colours().call;
    assert_eq!(frame_fill(&out, "b_logic"), calls.logic);
    assert_eq!(frame_fill(&out, "a_alloc"), calls.alloc);
    assert_eq!(frame_fill(&out, "c_unsure"), calls.unsure);
    assert_eq!(
        frame_fill(&out, "crate"),
        calls.logic,
        "a tie between families goes to the one listed first"
    );
}

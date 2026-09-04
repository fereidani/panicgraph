//! A standalone flame graph.
//!
//! The file is self contained: one document carrying its own styling and the
//! small amount of script that makes it explorable, so it can be attached to
//! a report, committed beside a release, or opened straight from disk. It
//! degrades to a readable picture with scripting turned off, because every
//! frame carries a native title.
//!
//! The shape follows the flame graph convention, which readers already know:
//! width is how much reaches through a frame, depth is call depth, clicking
//! a frame zooms into it, and `ctrl-F` searches. Zooming keeps the path to
//! the frame in view as full width bars and hides what the frame does not
//! contain, so the picture stays a picture of one path. Searching colours
//! what matched and says how much of the whole it accounts for.
//!
//! The picture is as wide as the window it is opened in. Frames are placed
//! as shares of the width rather than at pixels, so they stretch with the
//! window while the text keeps its size, and the script fits every label
//! again whenever the width changes. What is written into the file is fitted
//! for the width flame graph tools draw at, which is the picture a viewer
//! without scripting shows, scaled as a whole to fit.
//!
//! The project's mark sits in the corner, at the height of a control, so it
//! says what drew the file without competing with the title. It links to the
//! project and names the version, so a file handed on alone still says where
//! it came from.

// Laying out a drawing means turning counts into coordinates. The counts are
// frame and panic totals, which stay many orders of magnitude below the point
// where a double stops representing an integer exactly, and the results are
// rounded on the way out.
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]

use std::fmt::Write as _;

use anyhow::Result;

use crate::{
    CategorySet, Graph,
    api::{FlameRow, children_of},
    solve::Edges,
};

/// Height of one row of frames.
const ROW: f64 = 17.0;
/// Gap between frames, so neighbours stay separable.
const GAP: f64 = 1.0;
/// Space above the frames for the mark, the title, the policy it was drawn
/// under, and the controls.
const HEAD: f64 = 62.0;
/// Space below the frames for the hovered frame's details.
const FOOT: f64 = 34.0;
/// Width the picture is fitted for before any script runs.
///
/// Frames are placed as shares of this width and stretch with the window in
/// a browser, where the script fits the labels again. Without scripting the
/// drawing is scaled as a whole, so this is also how wide it is when opened
/// in a viewer, and it is the width the flame graph tools readers know draw
/// at.
const WIDTH: f64 = 1200.0;
/// Rough width of one character at the label size, for fitting text.
const CHAR: f64 = 5.9;
/// Narrowest frame that can carry a label.
const MIN_LABEL: f64 = 28.0;
/// Narrowest frame that is drawn at all, at the width the picture is fitted
/// for.
///
/// A frame thinner than this is a sliver no reader can hover or click, and
/// dropping it with everything under it keeps a wide graph a file that can
/// be opened.
const MIN_WIDTH: f64 = 0.1;

/// Colours, matching the interactive view.
///
/// Three hues carry identity because an icicle places arbitrary frames side
/// by side, and only the first three slots of the palette clear the
/// all-pairs colour vision floors. The exact category is written on the
/// frame and in its title, never left to colour alone.
const LOGIC: &str = "#2a78d6";
const ALLOC: &str = "#eb6834";
const UNSURE: &str = "#1baf7a";
const NEUTRAL: &str = "#c9c6bd";

/// Categories drawn as a call rather than a panic.
fn family(category: Option<&str>) -> &'static str {
    category.map_or(NEUTRAL, |name| match name {
        "capacity-overflow" | "alloc-failure" | "refcount-overflow" => ALLOC,
        "unknown" | "ub-check" | "fmt" | "null-deref" | "misaligned-ref" => {
            UNSURE
        }
        _ => LOGIC,
    })
}

/// One laid out frame.
struct Frame {
    row: usize,
    x: f64,
    width: f64,
    depth: usize,
    value: usize,
}

/// Renders the flame graph as a standalone document.
///
/// # Errors
///
/// Returns an error if the fixpoint does not converge.
pub fn render(
    graph: &Graph,
    suppressed: CategorySet,
    edges: Edges,
    fold: bool,
    out: &mut String,
) -> Result<()> {
    let rows = crate::api::flame_rows(graph, suppressed, edges, fold)?;
    let frames = layout(&rows);
    let depth = frames.iter().map(|f| f.depth).max().unwrap_or(0);
    let height = (depth as f64 + 1.0).mul_add(ROW, HEAD + FOOT);
    let total = frames.first().map_or(1, |f| f.value.max(1));

    header(WIDTH, height, out);
    out.push_str(BRAND);
    // Whatever belongs to the middle or the right edge is placed as a share
    // of the width, or as an offset back from the edge, so it follows the
    // window rather than the width the file was fitted for.
    let _ = writeln!(
        out,
        "<text id=\"title\" x=\"50%\" y=\"22\" text-anchor=\"middle\" \
         class=\"title\">Reachable panics</text>"
    );
    // The policy belongs on the picture. A flame graph of what can panic
    // says nothing definite without the assumptions it was drawn under.
    let _ = writeln!(
        out,
        "<text id=\"subtitle\" x=\"50%\" y=\"38\" text-anchor=\"middle\" \
         class=\"note\">{}</text>",
        escape(&policy(suppressed))
    );
    // The zoom control stays at the left, where flame graphs keep it, after
    // the mark.
    let _ = writeln!(
        out,
        "<text id=\"unzoom\" x=\"150\" y=\"22\" class=\"ctl\">Reset \
         Zoom</text>"
    );
    let _ = writeln!(
        out,
        "<text id=\"search\" x=\"100%\" dx=\"-10\" y=\"22\" \
         text-anchor=\"end\" class=\"ctl on\">Search</text>"
    );
    let _ = writeln!(
        out,
        "<text id=\"note\" x=\"10\" y=\"{:.1}\" class=\"note\">{} frames, \
         {total} reachable panics. Click a frame to zoom, ctrl-F to \
         search.</text>",
        height - 12.0,
        frames.len()
    );
    let _ = writeln!(
        out,
        "<text id=\"detail\" x=\"10\" y=\"{:.1}\" class=\"detail\"> </text>",
        height - 12.0
    );
    let _ = writeln!(
        out,
        "<text id=\"matched\" x=\"100%\" dx=\"-10\" y=\"{:.1}\" \
         text-anchor=\"end\" class=\"note\"> </text>",
        height - 12.0
    );

    out.push_str("<g id=\"frames\">\n");
    for frame in &frames {
        let row = &rows[frame.row];
        draw(frame, row, total, out);
    }
    out.push_str("</g>\n");

    out.push_str("</svg>\n");
    Ok(())
}

/// The assumptions the picture was drawn under, written out.
fn policy(suppressed: CategorySet) -> String {
    let names = suppressed.names();
    if names.is_empty() {
        return "assuming nothing impossible".to_owned();
    }
    format!("assuming impossible: {}", names.join(", "))
}

/// Places every frame, widest first so the heavy paths lead.
fn layout(rows: &[FlameRow]) -> Vec<Frame> {
    let mut children = children_of(rows);

    // Values accumulate from the leaves, so a frame is exactly as wide as
    // the panics reachable through it. Computed bottom up without recursion,
    // by walking the frames in reverse discovery order.
    let mut order = Vec::with_capacity(rows.len());
    let mut stack = vec![0usize];
    while let Some(id) = stack.pop() {
        order.push(id);
        for kid in children.get(&id).into_iter().flatten() {
            stack.push(*kid);
        }
    }
    let mut value = vec![0usize; rows.len()];
    for id in order.iter().rev() {
        let kids = children.get(id).map(Vec::as_slice).unwrap_or_default();
        value[*id] = if kids.is_empty() {
            rows[*id].value.max(1)
        } else {
            kids.iter().map(|k| value[*k]).sum()
        };
    }
    for list in children.values_mut() {
        list.sort_by(|a, b| {
            value[*b]
                .cmp(&value[*a])
                .then_with(|| rows[*a].name.cmp(&rows[*b].name))
        });
    }

    let root = value.first().copied().unwrap_or(1).max(1);
    let scale = WIDTH / root as f64;
    let mut frames = Vec::with_capacity(rows.len());
    let mut work = vec![(0usize, 0.0f64, 0usize)];
    while let Some((id, x, depth)) = work.pop() {
        let width = value[id] as f64 * scale;
        frames.push(Frame {
            row: id,
            x,
            width,
            depth,
            value: value[id],
        });
        let mut at = x;
        for kid in children.get(&id).into_iter().flatten() {
            let span = value[*kid] as f64 * scale;
            // A sliver cannot be read, hovered or clicked, and neither can
            // anything under it, so the whole branch goes.
            if span >= MIN_WIDTH {
                work.push((*kid, at, depth + 1));
            }
            at += span;
        }
    }
    frames
}

/// A distance across the drawing, as the share of the width it takes.
///
/// Frames are placed in these shares rather than at pixels, which is what
/// lets them stretch to the window.
fn percent(units: f64) -> f64 {
    100.0 * units / WIDTH
}

/// Writes one frame.
fn draw(frame: &Frame, row: &FlameRow, total: usize, out: &mut String) {
    let y = (frame.depth as f64).mul_add(ROW, HEAD);
    let width = (frame.width - GAP).max(0.6);
    let share = 100.0 * frame.value as f64 / total as f64;
    let kind = row.category.map_or_else(
        || format!("{} call", row.kind),
        |category| format!("{category} panic"),
    );
    let folded = if row.elided.is_empty() {
        String::new()
    } else {
        format!(", through {} more calls", row.elided.len())
    };

    // The same sentence labels the frame for the script and for a reader
    // hovering it with scripting off, so it is built once. Only the name can
    // carry markup; the rest is generated from counts and fixed words.
    let name = escape(&row.name);
    let info = format!(
        "{name} ({kind}, {} reachable, {share:.1}%{folded})",
        frame.value
    );
    // The label is fitted here for a reader with scripting off, and the
    // whole name is kept beside it so the script can fit it again whenever
    // the window or a zoom changes how much room the frame has. Every frame
    // carries a label element, empty when there is no room yet, so one that
    // gains room later has somewhere to write its name.
    let _ = writeln!(
        out,
        "<g class=\"f\" data-name=\"{name}\" data-info=\"{info}\" \
         data-more=\"{}\" data-x=\"{:.2}\" data-w=\"{:.2}\" \
         data-y=\"{y:.1}\">",
        row.elided.len(),
        frame.x,
        frame.width
    );
    let _ = writeln!(out, "<title>{info}</title>");
    let _ = writeln!(
        out,
        "<rect x=\"{:.4}%\" y=\"{y:.1}\" width=\"{:.4}%\" \
         height=\"{:.1}\" fill=\"{}\"{} rx=\"2\"/>",
        percent(frame.x),
        percent(width),
        ROW - GAP,
        family(row.category),
        if row.cleanup {
            " stroke=\"#8a5a00\" stroke-dasharray=\"3 2\""
        } else {
            ""
        }
    );
    let label = if width > MIN_LABEL {
        let room = ((width - 8.0) / CHAR) as usize;
        escape(&tail(&row.name, room, row.elided.len()))
    } else {
        String::new()
    };
    let _ = writeln!(
        out,
        "<text x=\"{:.4}%\" dx=\"4\" y=\"{:.1}\" class=\"l\">{label}</text>",
        percent(frame.x),
        y + ROW / 2.0 + 3.0,
    );
    out.push_str("</g>\n");
}

/// Keeps the end of a path, which is the part that identifies it.
fn tail(text: &str, room: usize, folded: usize) -> String {
    let badge = if folded > 0 {
        format!(" +{folded}")
    } else {
        String::new()
    };
    let room = room.saturating_sub(badge.len());
    if room < 5 {
        return badge.trim().to_owned();
    }
    let chars: Vec<char> = text.chars().collect();
    if chars.len() <= room {
        return format!("{text}{badge}");
    }
    if let Some(cut) = text.rfind("::") {
        let end = &text[cut + 2..];
        if end.chars().count() <= room.saturating_sub(2) {
            return format!("..{end}{badge}");
        }
    }
    let keep: String = chars[chars.len() - room.saturating_sub(2)..]
        .iter()
        .collect();
    format!("..{keep}{badge}")
}

/// Escapes the characters that would otherwise close a tag or an attribute.
fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            _ => out.push(c),
        }
    }
    out
}

/// Writes the document head, its styling, and the script that explores it.
///
/// The document takes the whole width of whatever holds it, and its viewBox
/// names the width the labels were fitted for. The script drops the viewBox
/// once the file is open, which lets the frames spread to the window at
/// their own text size; without the script it stays, and the drawing is
/// scaled as a whole to fit.
fn header(width: f64, height: f64, out: &mut String) {
    let _ = writeln!(out, "<?xml version=\"1.0\" standalone=\"no\"?>");
    let _ = writeln!(
        out,
        "<svg version=\"1.1\" width=\"100%\" height=\"{height:.0}\" \
         viewBox=\"0 0 {width:.0} {height:.0}\" \
         xmlns=\"http://www.w3.org/2000/svg\" onload=\"init()\">"
    );
    out.push_str(STYLE);
    out.push_str(SCRIPT);
    let _ = writeln!(
        out,
        "<rect width=\"100%\" height=\"100%\" fill=\"#fcfcfb\"/>"
    );
}

/// The project's mark and name, for the corner of the picture.
///
/// This is the lockup the interactive view shows, drawn at the height of a
/// control so it reads as a signature rather than a heading, and linked to
/// the project. Its tooltip names the version, so a reader handed the file
/// alone can still find where it came from.
const BRAND: &str = concat!(
    "<a class=\"brand\" href=\"",
    env!("CARGO_PKG_REPOSITORY"),
    "\" target=\"_blank\">\n<title>Drawn by PanicGraph ",
    env!("CARGO_PKG_VERSION"),
    "</title>\n",
    // The lockup is drawn in a 300 by 64 box, shown here 24 high.
    "<g fill=\"none\" transform=\"translate(10 6) scale(0.375)\">\n",
    "<path d=\"M6 14H58M6 32H58M6 50H58\" stroke=\"#2E2B27\" \
     stroke-opacity=\"0.32\" stroke-width=\"2\"/>\n",
    "<path d=\"M13 14H26V32H44V50\" stroke=\"#2E2B27\" stroke-width=\"4.5\" \
     stroke-linecap=\"square\"/>\n",
    "<circle cx=\"13\" cy=\"14\" r=\"3.5\" fill=\"#2E2B27\"/>\n",
    "<circle cx=\"44\" cy=\"50\" r=\"7\" fill=\"#E8A33D\"/>\n",
    "<circle cx=\"44\" cy=\"50\" r=\"7\" fill=\"none\" stroke=\"#2E2B27\" \
     stroke-width=\"3\"/>\n",
    "<text x=\"76\" y=\"42\" fill=\"#2E2B27\">PanicGraph</text>\n",
    "</g>\n</a>\n",
);

/// Styling, kept inside the document so the file stands alone.
const STYLE: &str = r#"<style>
  text { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; }
  .title { font-family: ui-sans-serif, system-ui, sans-serif; font-size: 15px;
    font-weight: 600; fill: #0b0b0b; cursor: pointer; }
  .note, .detail, .ctl { font-family: ui-sans-serif, system-ui, sans-serif;
    font-size: 11px; fill: #78766f; }
  .detail { fill: #0b0b0b; }
  .ctl { fill: #0b0b0b; cursor: pointer; display: none; }
  .ctl.on { display: inline; }
  .ctl:hover { text-decoration: underline; }
  .brand text { font-family: "Space Grotesk", "Helvetica Neue", Helvetica,
    Arial, sans-serif; font-size: 34px; font-weight: 600;
    letter-spacing: -0.8px; }
  .brand:hover { opacity: 0.7; }
  .l { font-size: 10px; fill: #0b0b0b; pointer-events: none; }
  .f rect { stroke-width: 1; }
  .f:hover rect { opacity: 0.72; cursor: pointer; }
  .parent rect { opacity: 0.28; }
  .hide { display: none; }
  /* Magenta belongs to no category, so a match is never read as one. */
  .match rect { fill: #e600e6; }
</style>
"#;

/// The script that makes the picture explorable.
///
/// Zooming rescales the frames rather than redrawing them, so the file stays
/// one pass of output and works from the filesystem with no server. What a
/// search matched is written into the address, so a picture opened at a
/// finding can be handed to someone else as it stands.
const SCRIPT: &str = r#"<script type="text/ecmascript"><![CDATA[
var frames = [], base = [], detail = null, note = null;
var unzoombtn = null, searchbtn = null, matchedtxt = null;
var width = 0, pixel = 1, searching = "";

function init() {
  var svg = document.documentElement;
  /* The frames are placed as shares of the width, so with the viewBox gone
     they spread to the window while the text keeps its size. The viewBox
     is read first: it names the width the file was laid out at, which is
     the unit every position below is written in. */
  width = svg.viewBox.baseVal.width;
  svg.removeAttribute("viewBox");
  detail = document.getElementById("detail");
  note = document.getElementById("note");
  unzoombtn = document.getElementById("unzoom");
  searchbtn = document.getElementById("search");
  matchedtxt = document.getElementById("matched");
  frames = Array.prototype.slice.call(
    document.getElementById("frames").children);
  frames.forEach(function (g) {
    var x = +g.getAttribute("data-x"), w = +g.getAttribute("data-w");
    base.push({
      x: x, w: w, y: +g.getAttribute("data-y"),
      cx: x, cw: w, hidden: false, above: false, hit: false
    });
    g.addEventListener("mouseover", function () {
      detail.textContent = g.getAttribute("data-info");
      note.style.display = "none";
    });
    g.addEventListener("mouseout", function () {
      detail.textContent = " ";
      note.style.display = "";
    });
    g.addEventListener("click", function (e) { zoom(g); e.stopPropagation(); });
  });
  document.getElementById("title").addEventListener("click", unzoom);
  unzoombtn.addEventListener("click", unzoom);
  searchbtn.addEventListener("click", prompt_for_search);
  window.addEventListener("keydown", function (e) {
    if (e.keyCode === 114 || (e.ctrlKey && e.keyCode === 70)) {
      e.preventDefault();
      prompt_for_search();
    }
  });
  window.addEventListener("resize", refit);
  refit();
  var asked = /[?&]s=([^&]*)/.exec(window.location.search);
  if (asked) search(decodeURIComponent(asked[1].replace(/\+/g, " ")));
}

/* Rescales so the clicked frame fills the width. The frames it sits under
   stay as full width bars, because the path to a frame is part of reading
   it, and everything the frame does not contain is taken out of the way. */
function zoom(target) {
  var i = frames.indexOf(target);
  if (i < 0) return;
  var at = base[i], span = at.w || 1, scale = width / span;
  frames.forEach(function (g, j) {
    var b = base[j];
    b.hidden = !(inside(b, at) || inside(at, b));
    b.above = !b.hidden && b.y < at.y;
    if (b.above) {
      place(g, b, 0, width);
    } else if (!b.hidden) {
      place(g, b, (b.x - at.x) * scale, b.w * scale);
    }
    paint(g, b);
  });
  show(unzoombtn, true);
  if (searching) search(searching);
}

/* Whether one frame lies within another's span. Frames nest or stand
   apart and never overlap, so the centre of the inner one decides, and
   the rounding the positions are written with cannot carry a centre across
   an edge the way it can an end. */
function inside(inner, outer) {
  var centre = inner.x + inner.w / 2;
  return centre >= outer.x && centre <= outer.x + outer.w;
}

function unzoom() {
  frames.forEach(function (g, j) {
    var b = base[j];
    b.hidden = false;
    b.above = false;
    place(g, b, b.x, b.w);
    paint(g, b);
  });
  show(unzoombtn, false);
  if (searching) search(searching);
}

/* Writes what a frame is now: out of the way, on the path to the zoom, or
   matching the search. One place decides, so the three cannot disagree. */
function paint(g, b) {
  var cls = "f";
  if (b.hidden) cls += " hide";
  if (b.above) cls += " parent";
  if (b.hit) cls += " match";
  g.setAttribute("class", cls);
}

/* Moves one frame, and fits its label to the room it now has. Where the
   frame stands is kept, so the label can be fitted again on its own when
   the window changes width. */
function place(g, b, x, w) {
  b.cx = x;
  b.cw = w;
  var r = g.getElementsByTagName("rect")[0];
  r.setAttribute("x", percent(x));
  r.setAttribute("width", percent(Math.max(w - 1, 0.6)));
  g.getElementsByTagName("text")[0].setAttribute("x", percent(x));
  fit(g, w);
}

/* A distance across the drawing, as the share of the width it takes. */
function percent(units) {
  return (100 * units / width).toFixed(4) + "%";
}

/* Writes the label a frame has room for, in the pixels it has now. */
function fit(g, w) {
  var px = w * pixel;
  g.getElementsByTagName("text")[0].textContent = px <= 28 ? "" :
    tail(g.getAttribute("data-name"), Math.floor((px - 8) / 5.9),
      +g.getAttribute("data-more"));
}

/* Fits every label to the room its frame has in the window as it stands.
   Runs once the file is open and again whenever the window changes width,
   which the labels written into the file could not know about. */
function refit() {
  pixel = document.documentElement.getBoundingClientRect().width / width;
  frames.forEach(function (g, j) {
    if (!base[j].hidden) fit(g, base[j].cw);
  });
}

/* Keeps the end of a path, which is the part that identifies it. */
function tail(text, room, more) {
  var badge = more > 0 ? " +" + more : "";
  room -= badge.length;
  if (room < 5) return badge.replace(" ", "");
  if (text.length <= room) return text + badge;
  var cut = text.lastIndexOf("::");
  if (cut >= 0 && text.length - cut - 2 <= room - 2) {
    return ".." + text.slice(cut + 2) + badge;
  }
  return ".." + text.slice(text.length - (room - 2)) + badge;
}

function prompt_for_search() {
  if (searching) {
    reset_search();
    return;
  }
  var term = window.prompt("Search frames, as a regular expression", "");
  if (term) search(term);
}

/* Colours what matched, and says how much of the whole it accounts for.
   A frame under another that also matched is not counted twice: only the
   widest claim at each position is kept, which is the one that contains
   the rest. */
function search(term) {
  var re;
  try { re = new RegExp(term, "i"); } catch (e) { return; }
  var widest = {};
  searching = term;
  frames.forEach(function (g, j) {
    var b = base[j];
    b.hit = !b.hidden && re.test(g.getAttribute("data-name"));
    if (b.hit && (widest[b.x] === undefined || widest[b.x] < b.w)) {
      widest[b.x] = b.w;
    }
    paint(g, b);
  });
  var matched = 0;
  for (var x in widest) matched += widest[x];
  var whole = base.length ? base[0].w || 1 : 1;
  matchedtxt.textContent =
    "Matched: " + (100 * matched / whole).toFixed(1) + "%";
  searchbtn.textContent = "Reset Search";
  remember(term);
}

function reset_search() {
  frames.forEach(function (g, j) {
    base[j].hit = false;
    paint(g, base[j]);
  });
  searching = "";
  matchedtxt.textContent = " ";
  searchbtn.textContent = "Search";
  remember("");
}

function show(el, on) {
  el.setAttribute("class", on ? "ctl on" : "ctl");
}

/* Writes the search into the address, where the file can be opened from
   again. A document opened straight off a filesystem may refuse this, and
   the picture is no worse for it. */
function remember(term) {
  try {
    var here = window.location.href.split("?")[0];
    window.history.replaceState(null, "",
      term ? here + "?s=" + encodeURIComponent(term) : here);
  } catch (e) {}
}
]]></script>
"#;

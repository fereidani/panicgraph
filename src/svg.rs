//! A standalone flame graph.
//!
//! The file is self contained: one document carrying its own styling and the
//! small amount of script that makes it explorable, so it can be attached to
//! a report, committed beside a release, or opened straight from disk. It
//! degrades to a readable picture with scripting turned off, because every
//! frame carries a native title.
//!
//! The shape follows the flame graph convention, which readers already know:
//! width is how much reaches through a frame, depth is call depth, and
//! clicking a frame zooms into it.

// Laying out a drawing means turning counts into coordinates. The counts are
// frame and panic totals, which stay many orders of magnitude below the point
// where a double stops representing an integer exactly, and the results are
// rounded to a tenth of a pixel on the way out.
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]

use std::fmt::Write as _;

use anyhow::Result;

use crate::{
    CategorySet, Graph,
    api::{FlameRow, children_of},
};

/// Height of one row of frames.
const ROW: f64 = 17.0;
/// Gap between frames, so neighbours stay separable.
const GAP: f64 = 1.0;
/// Space above the frames for the title and the search box.
const HEAD: f64 = 46.0;
/// Space below the frames for the hovered frame's details.
const FOOT: f64 = 34.0;
/// Width of the drawing.
const WIDTH: f64 = 1200.0;
/// Rough width of one character at the label size, for fitting text.
const CHAR: f64 = 5.9;
/// Narrowest frame that can carry a label.
const MIN_LABEL: f64 = 28.0;

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
    follow_inexact: bool,
    fold: bool,
    out: &mut String,
) -> Result<()> {
    let rows = crate::api::flame_rows(graph, suppressed, follow_inexact, fold)?;
    let frames = layout(&rows);
    let depth = frames.iter().map(|f| f.depth).max().unwrap_or(0);
    let height = (depth as f64 + 1.0).mul_add(ROW, HEAD + FOOT);
    let total = frames.first().map_or(1, |f| f.value.max(1));

    header(WIDTH, height, out);
    let _ = writeln!(
        out,
        "<text id=\"title\" x=\"{:.1}\" y=\"24\" text-anchor=\"middle\" \
         class=\"title\">Reachable panics</text>",
        WIDTH / 2.0
    );
    let _ = writeln!(
        out,
        "<text id=\"note\" x=\"10\" y=\"{:.1}\" class=\"note\">{} frames, \
         {total} reachable panics. Click a frame to zoom, click the title to \
         reset.</text>",
        height - 12.0,
        frames.len()
    );
    let _ = writeln!(
        out,
        "<text id=\"detail\" x=\"10\" y=\"{:.1}\" class=\"detail\"> </text>",
        height - 12.0
    );

    for frame in &frames {
        let row = &rows[frame.row];
        draw(frame, row, total, out);
    }

    out.push_str("</svg>\n");
    Ok(())
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
            work.push((*kid, at, depth + 1));
            at = (value[*kid] as f64).mul_add(scale, at);
        }
    }
    frames
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
    let _ = writeln!(
        out,
        "<g class=\"f\" data-name=\"{name}\" data-info=\"{info}\">"
    );
    let _ = writeln!(out, "<title>{info}</title>");
    let _ = writeln!(
        out,
        "<rect x=\"{:.1}\" y=\"{y:.1}\" width=\"{width:.1}\" \
         height=\"{:.1}\" fill=\"{}\"{} rx=\"2\"/>",
        frame.x,
        ROW - GAP,
        family(row.category),
        if row.cleanup {
            " stroke=\"#8a5a00\" stroke-dasharray=\"3 2\""
        } else {
            ""
        }
    );
    if width > MIN_LABEL {
        let room = ((width - 8.0) / CHAR) as usize;
        let _ = writeln!(
            out,
            "<text x=\"{:.1}\" y=\"{:.1}\" class=\"l\">{}</text>",
            frame.x + 4.0,
            y + ROW / 2.0 + 3.0,
            escape(&tail(&row.name, room, row.elided.len()))
        );
    }
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
fn header(width: f64, height: f64, out: &mut String) {
    let _ = writeln!(out, "<?xml version=\"1.0\" standalone=\"no\"?>");
    let _ = writeln!(
        out,
        "<svg version=\"1.1\" width=\"{width:.0}\" height=\"{height:.0}\" \
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

/// Styling, kept inside the document so the file stands alone.
const STYLE: &str = r"<style>
  text { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; }
  .title { font-family: ui-sans-serif, system-ui, sans-serif; font-size: 15px;
    font-weight: 600; fill: #0b0b0b; cursor: pointer; }
  .note, .detail { font-family: ui-sans-serif, system-ui, sans-serif;
    font-size: 11px; fill: #78766f; }
  .detail { fill: #0b0b0b; }
  .l { font-size: 10px; fill: #0b0b0b; pointer-events: none; }
  .f rect { stroke-width: 1; }
  .f:hover rect { opacity: 0.72; cursor: pointer; }
  .dim rect { opacity: 0.16; }
  .hit rect { stroke: #0b0b0b; stroke-width: 2; }
</style>
";

/// The script that makes the picture explorable.
///
/// Zooming rescales the frames rather than redrawing them, so the file stays
/// one pass of output and works from the filesystem with no server.
const SCRIPT: &str = r#"<script type="text/ecmascript"><![CDATA[
var frames = [], base = [], detail = null, note = null, width = 0;

function init() {
  width = document.documentElement.width.baseVal.value;
  detail = document.getElementById("detail");
  note = document.getElementById("note");
  frames = Array.prototype.slice.call(document.getElementsByClassName("f"));
  frames.forEach(function (g) {
    var r = g.getElementsByTagName("rect")[0];
    base.push({ x: +r.getAttribute("x"), w: +r.getAttribute("width") });
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
  document.getElementById("title").addEventListener("click", reset);
}

/* Rescales so the clicked frame fills the width. Frames outside it keep
   their place but are dimmed, so the surrounding shape is still legible. */
function zoom(target) {
  var i = frames.indexOf(target);
  if (i < 0) return;
  var from = base[i].x, span = base[i].w || 1, scale = width / span;
  frames.forEach(function (g, j) {
    var b = base[j];
    var x = (b.x - from) * scale, w = b.w * scale;
    var outside = x + w < 0 || x > width;
    g.setAttribute("class", outside ? "f dim" : "f");
    var r = g.getElementsByTagName("rect")[0];
    r.setAttribute("x", x.toFixed(1));
    r.setAttribute("width", Math.max(w - 1, 0.6).toFixed(1));
    var t = g.getElementsByTagName("text")[0];
    if (t) {
      t.setAttribute("x", (x + 4).toFixed(1));
      t.style.display = w > 28 ? "" : "none";
    }
  });
}

function reset() {
  frames.forEach(function (g, j) {
    var b = base[j];
    g.setAttribute("class", "f");
    var r = g.getElementsByTagName("rect")[0];
    r.setAttribute("x", b.x.toFixed(1));
    r.setAttribute("width", Math.max(b.w - 1, 0.6).toFixed(1));
    var t = g.getElementsByTagName("text")[0];
    if (t) {
      t.setAttribute("x", (b.x + 4).toFixed(1));
      t.style.display = b.w > 28 ? "" : "none";
    }
  });
}
]]></script>
"#;

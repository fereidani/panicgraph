/* panicgraph interactive view.
 *
 * Vue owns the page chrome: header, policy panel, detail pane, table. D3 owns
 * every mark inside the chart's <svg> and Vue never touches those children.
 * Mixing the two over one subtree is the classic failure of this pairing.
 *
 * The Rust solver stays authoritative. Flipping a category sends the new mask
 * to the server and renders what comes back, so there is exactly one
 * implementation of the suppression semantics.
 */
const { createApp, ref, computed, watch, onMounted, nextTick } = Vue;

/* Three colour families, because an icicle places arbitrary cells side by
 * side and only three categorical slots clear the all-pairs colour-vision
 * floors. The finer 17-category detail lives in labels, tooltips and the
 * table, never in colour alone. */
const FAMILY = {
  logic: ['index', 'overflow', 'divide-by-zero', 'remainder-by-zero', 'unwrap',
          'explicit', 'str-boundary', 'borrow', 'poison'],
  alloc: ['capacity-overflow', 'alloc-failure', 'refcount-overflow'],
  unsure: ['unknown', 'ub-check', 'fmt', 'null-deref', 'misaligned-ref',
           'foreign', 'dyn-call', 'fn-pointer', 'generic-bound'],
};
const FAMILY_OF = {};
for (const [family, names] of Object.entries(FAMILY)) {
  for (const name of names) FAMILY_OF[name] = family;
}
const FAMILY_LABEL = {
  logic: 'Logic and bounds',
  alloc: 'Allocation',
  unsure: 'Unverified',
};

function cssVar(name) {
  return getComputedStyle(document.documentElement)
    .getPropertyValue(name).trim();
}

/* Relative luminance of a hex colour, used to pick a legible ink for text
   drawn on top of a filled mark. The series steps sit mid-range, so neither
   ink is right for all three in both themes. */
function luminance(hex) {
  const m = /^#?([\da-f]{2})([\da-f]{2})([\da-f]{2})$/i.exec(hex.trim());
  if (!m) return 0;
  const channel = v => {
    const c = parseInt(v, 16) / 255;
    return c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4;
  };
  return 0.2126 * channel(m[1]) + 0.7152 * channel(m[2])
    + 0.0722 * channel(m[3]);
}

/* Picks whichever ink actually contrasts better against the fill rather than
   guessing from a lightness threshold. Every step in the current palette is
   mid-range, so the dark ink wins on all of them by a wide margin, but the
   comparison keeps that true if the palette is ever swapped. */
function inkOn(fill) {
  const contrast = ink => {
    const a = luminance(fill);
    const b = luminance(ink);
    return (Math.max(a, b) + 0.05) / (Math.min(a, b) + 0.05);
  };
  return contrast('#0b0b0b') >= contrast('#ffffff') ? '#0b0b0b' : '#ffffff';
}
function familyColor(family) {
  return cssVar(family === 'alloc' ? '--series-alloc'
    : family === 'unsure' ? '--series-unsure' : '--series-logic');
}

async function getJson(path) {
  const res = await fetch(path);
  const body = await res.json();
  if (body && body.error) throw new Error(body.error);
  return body;
}

/* ---------------------------------------------------------------- icicle */

const IcicleChart = {
  props: ['flame', 'theme', 'query'],
  emits: ['pick', 'trail', 'matches', 'warn'],
  template: `<div class="chart-host"><svg ref="svg"
      role="img" aria-label="Call paths from local functions to the panics they can reach"></svg></div>`,
  setup(props, { emit }) {
    const svg = ref(null);
    const ROW = 20, GAP = 2, MIN_LABEL = 32, STRIP = 6;
    let tip = null;
    let tree = null;
    let focusId = 0;
    // Matches in drawing order, so stepping through them moves left to right
    // and down, and the position survives the re-render that zooming causes.
    let matchIds = [];
    let matchAt = -1;

    function ensureTip() {
      if (!tip) {
        tip = d3.select('body').append('div')
          .attr('class', 'tooltip').style('display', 'none');
      }
      return tip;
    }

    /* Rebuilds the hierarchy. Called when the policy changes. */
    function build() {
      const raw = props.flame && props.flame.nodes ? props.flame.nodes : [];
      if (raw.length <= 1) { tree = null; return; }
      const rows = raw;
      tree = d3.stratify().id(d => d.id).parentId(d => d.parent)(rows);
      // Values accumulate from the leaves, so an interior frame is exactly as
      // wide as the panics reachable through it.
      tree.eachAfter(node => {
        node.value = node.children
          ? d3.sum(node.children, c => c.value)
          : Math.max(node.data.value, 1);
        node.family = node.data.category
          ? (FAMILY_OF[node.data.category] || 'unsure')
          : dominant(node);
      });
      // Every path in this tree is a witness, so it ends at a panic. A frame
       // with nothing under it and no category of its own would be claiming
       // reachable panics while showing none, which is what a transform that
       // drops edges looks like from the outside.
      const orphans = tree.leaves()
        .filter(d => d !== tree && !d.data.category).length;
      emit('warn', orphans
        ? `${orphans} frames report reachable panics but show none below `
          + 'them, so the graph is dropping paths. Treat it as unreliable.'
        : null);

      // Widest first; then by family, so the many equal width siblings form
      // contiguous bands of colour instead of confetti.
      const rank = { logic: 0, alloc: 1, unsure: 2 };
      tree.sort((a, b) =>
        b.value - a.value
        || (rank[a.family] ?? 3) - (rank[b.family] ?? 3)
        || (a.data.name < b.data.name ? -1 : 1));
    }

    function focusNode() {
      if (!tree) return null;
      return tree.descendants().find(d => d.data.id === focusId) || tree;
    }

    function setFocus(node) {
      focusId = node.data.id;
      emit('trail', node.ancestors().reverse()
        .map(n => ({ id: n.data.id, name: n.data.name })));
      render();
    }

    function render() {
      const host = svg.value;
      if (!host) return;
      const root = d3.select(host);
      root.selectAll('*').remove();
      if (!tree) { root.attr('width', 10).attr('height', 10); return; }

      const focus = focusNode();
      const width = Math.max(host.parentElement.clientWidth - 34, 320);
      const total = 1 + d3.max(tree.descendants(), d => d.depth);
      d3.partition().size([1, total])(tree);

      const test = matcher(props.query);
      /* A folded frame stands in for the calls it absorbed, so it answers a
         query that names one of them. Without this, collapsing chains would
         quietly hide search results. */
      const match = test && (d => test(d.data.name)
        || (d.data.elided || []).some(test));
      if (match) {
        matchIds = tree.descendants()
          .filter(d => d !== tree && match(d))
          .sort((a, b) => a.x0 - b.x0 || a.depth - b.depth)
          .map(d => d.data.id);
        if (matchAt >= matchIds.length) matchAt = -1;
        report(focus, match);
      } else {
        matchIds = [];
        matchAt = -1;
        emit('matches', null);
      }
      const currentId = matchAt >= 0 ? matchIds[matchAt] : null;

      const shown = focus.descendants();
      const depth = 1 + d3.max(shown, d => d.depth) - focus.depth;
      const strip = match ? STRIP : 0;
      const height = Math.max(depth, 1) * ROW + strip;
      const x = d3.scaleLinear().domain([focus.x0, focus.x1]).range([0, width]);

      root.attr('width', width).attr('height', height)
        .attr('viewBox', [0, 0, width, height]);


      // A tick per match, like the annotations on an editor scrollbar, so a
      // match that is only a pixel wide can still be located.
      if (match) {
        root.append('g').selectAll('rect')
          .data(shown.filter(d => d !== tree && match(d)))
          .join('rect')
          .attr('class', d =>
            'match-tick' + (d.data.id === currentId ? ' current' : ''))
          .attr('x', d => x(d.x0))
          .attr('y', 0)
          .attr('width', d => Math.max(x(d.x1) - x(d.x0), 2))
          .attr('height', STRIP - 2)
          .attr('rx', 1);
      }

      const cells = root.selectAll('g.cell')
        .data(shown.filter(d => d !== tree))
        .join('g')
        .attr('class', 'cell')
        .attr('transform', d =>
          `translate(${x(d.x0)},${(d.depth - focus.depth) * ROW + strip})`);

      // Subtracting the gap from a sliver leaves nothing painted while it
      // still owns hover space, so the gap is only taken when there is room.
      const cellWidth = d => {
        const w = x(d.x1) - x(d.x0);
        return w >= 4 ? w - GAP : Math.max(w, 1);
      };

      cells.append('rect')
        .attr('class', 'frame')
        .attr('width', cellWidth)
        .attr('height', ROW - GAP)
        .attr('rx', d => (cellWidth(d) < 8 ? 1 : 3))
        .attr('fill', d => d.data.category
          ? familyColor(d.family)
          : cssVar('--neutral-mark'))
        // A query dims what it did not match rather than recolouring what it
        // did, so a matched frame still shows which kind of panic it is.
        .attr('fill-opacity', d => (!match || match(d) ? 1 : 0.16))
        // A cleanup frame runs only while an earlier panic unwinds. That is a
        // reachability condition, drawn as a gate, and deliberately unlike the
        // dispatch uncertainty carried by vtable and unresolved edges.
        .attr('stroke', d => d.data.cleanup ? cssVar('--gate') : 'none')
        .attr('stroke-dasharray', d => d.data.cleanup ? '3 2' : null)
        .attr('stroke-width', d => d.data.cleanup ? 1.5 : 0);

      // The mark sits in its own rect so a frame can carry both a search
      // outline and the dashed gate that means it runs while unwinding.
      // An inset outline has no room in a narrow cell, so below six pixels
      // it is drawn just outside the frame instead of inside it.
      if (match) {
        cells.filter(d => match(d) && cellWidth(d) >= 3)
          .append('rect')
          .attr('class', d =>
            'match' + (d.data.id === currentId ? ' current' : ''))
          .attr('x', d => (cellWidth(d) >= 6 ? 1 : -1.5))
          .attr('y', d => (cellWidth(d) >= 6 ? 1 : -1.5))
          .attr('width', d => (cellWidth(d) >= 6
            ? Math.max(cellWidth(d) - 2, 1) : cellWidth(d) + 3))
          .attr('height', d =>
            (cellWidth(d) >= 6 ? ROW - GAP - 2 : ROW - GAP + 3))
          .attr('rx', 2);
      }

      const secondary = cssVar('--text-secondary');
      cells.filter(d => cellWidth(d) > MIN_LABEL)
        .append('text')
        .attr('class', 'frame-label')
        .attr('fill', d => d.data.category
          ? inkOn(familyColor(d.family))
          : secondary)
        .attr('x', 6).attr('y', ROW / 2 + 1)
        .attr('dominant-baseline', 'middle')
        .attr('fill-opacity', d => (!match || match(d) ? 1 : 0.3))
        .text(d => label(d, Math.floor((cellWidth(d) - 12) / 5.7)));

      cells
        .style('cursor', 'pointer')
        .on('mousemove', (event, d) => showTip(event, d))
        .on('mouseleave', () => ensureTip().style('display', 'none'))
        .on('click', (event, d) => {
          ensureTip().style('display', 'none');
          emit('pick', pathOf(d));
          if (d.children) setFocus(d);
        });
    }

    /* Accepts a regular expression, and falls back to a literal search when
       the text is not one, so a query like `Vec<u8>` still works. */
    function matcher(text) {
      const needle = (text || '').trim();
      if (!needle) return null;
      let re;
      try {
        re = new RegExp(needle, 'i');
      } catch (err) {
        const literal = needle.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        re = new RegExp(literal, 'i');
      }
      return name => re.test(name);
    }

    /* Reports how much of the view a query covers. Nested matches are counted
       once, by skipping any frame that already sits inside a match, which is
       the same rule a flame graph uses for its matched percentage. */
    function report(focus, match) {
      let frames = 0;
      let covered = 0;
      focus.each(node => {
        if (node === focus || !match(node)) return;
        frames += 1;
        const nested = node.ancestors().slice(1)
          .some(a => a !== focus && match(a));
        if (!nested) covered += node.value;
      });
      const total = focus.value || 1;
      emit('matches', {
        frames,
        share: Math.round((100 * covered) / total),
        at: matchAt >= 0 ? matchAt + 1 : 0,
        total: matchIds.length,
      });
    }

    function dominant(node) {
      const counts = {};
      for (const leaf of node.leaves()) {
        const f = FAMILY_OF[leaf.data.category] || 'unsure';
        counts[f] = (counts[f] || 0) + leaf.value;
      }
      return Object.entries(counts).sort((a, b) => b[1] - a[1])[0]?.[0] || 'logic';
    }

    function pathOf(node) {
      const leaf = node.leaves()[0];
      // The function frame carries the full path; the frames above it are
      // module segments and the frames below it are calls.
      const fn = node.ancestors().find(n => n.data.kind === 'function')
        || node.descendants().find(n => n.data.kind === 'function');
      return {
        rootFn: fn ? fn.data.full : null,
        category: node.data.category || (leaf && leaf.data.category) || null,
      };
    }

    function showTip(event, d) {
      const t = ensureTip();
      const reach = d.value === 1 ? '1 reachable panic' : `${d.value} reachable panics`;
      let html = `<div class="t">${escapeHtml(d.data.name)}</div>${reach}`;
      const elided = d.data.elided || [];
      if (elided.length) {
        html += `<br><span class="k">through ${elided.length} more `
          + `${elided.length === 1 ? 'call' : 'calls'}:</span><br>`
          + elided.map(n => escapeHtml(tail(n, 46))).join('<br>');
      }
      if (d.data.category) {
        html += `<br>panic category: ${escapeHtml(d.data.category)}`;
      } else {
        html += `<br>edge: ${escapeHtml(d.data.kind)}`;
      }
      if (d.data.cleanup) {
        html += `<br><span class="gate">runs only while an earlier panic unwinds</span>`;
      }
      t.html(html).style('display', 'block')
        .style('left', Math.min(event.clientX + 14, window.innerWidth - 400) + 'px')
        .style('top', (event.clientY + 16) + 'px');
    }

    /* Steps to the next or previous match and zooms so it has room. Without
       this, search can prove a match exists and not say where it is. */
    function cycle(delta) {
      if (!matchIds.length || !tree) return;
      const count = matchIds.length;
      matchAt = ((matchAt + delta) % count + count) % count;
      const wanted = matchIds[matchAt];
      const node = tree.descendants().find(d => d.data.id === wanted);
      if (!node) return;
      const target = node.children ? node : (node.parent || node);
      setFocus(target);
    }

    function reset() {
      focusId = 0;
      matchAt = -1;
      build();
      render();
      emit('trail', []);
    }
    function zoomTo(id) {
      const node = tree && tree.descendants().find(d => d.data.id === id);
      if (node) setFocus(node);
    }

    onMounted(() => { build(); render(); });
    watch(() => props.flame, () => nextTick(reset), { deep: false });
    watch(() => props.theme, () => nextTick(render));
    watch(() => props.query, () => { matchAt = -1; nextTick(render); });
    window.addEventListener('resize', () => nextTick(render));
    return { svg, zoomTo, cycle };
  },
};

/* Truncation keeps the end of a path, not the start. Cutting
   `<std::vec::Vec<T> as core::ops::Index<I>>::index` from the front leaves
   `<std::vec::V...`, which identifies nothing; the tail `..index` does. */
function tail(text, max) {
  if (max <= 1) return '';
  if (text.length <= max) return text;
  const cut = text.lastIndexOf('::');
  if (cut > 0 && text.length - cut - 2 <= max - 2) {
    return '..' + text.slice(cut + 2);
  }
  return '..' + text.slice(text.length - Math.max(max - 2, 1));
}

/* A frame label, with a count of the calls folded into it. A two character
   stub identifies nothing, so a frame too narrow to carry a real tail is
   left blank and answers on hover instead. */
const MIN_USEFUL_LABEL = 5;

function label(node, max) {
  const folded = (node.data.elided || []).length;
  const badge = folded ? ` +${folded}` : '';
  const room = max - badge.length;
  if (room < MIN_USEFUL_LABEL) return folded ? badge.trim() : '';
  return tail(node.data.name, room) + badge;
}
function escapeHtml(text) {
  return String(text).replace(/[&<>"]/g, c =>
    ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);
}

/* ------------------------------------------------------------------- app */

createApp({
  components: { IcicleChart },
  setup() {
    const graph = ref(null);
    const solution = ref(null);
    const flame = ref(null);
    const previous = ref(null);
    const selected = ref(null);
    const witness = ref(null);
    const error = ref(null);
    const showTable = ref(false);
    const trail = ref([]);
    const icicle = ref(null);
    const theme = ref(startingTheme());
    const exclusive = ref(null);
    const query = ref('');
    const matches = ref(null);
    const search = ref(null);
    const busy = ref(0);
    const chartWarning = ref(null);
    const expand = ref(false);
    const showInert = ref(false);
    let latest = 0;

    /* An explicit theme beats a remembered one, which beats the system
       setting. The mode is always written to the document so both are a
       deliberate choice rather than an inversion of the other. */
    function startingTheme() {
      const asked = new URLSearchParams(location.search).get('theme');
      if (asked === 'dark' || asked === 'light') return asked;
      const saved = localStorage.getItem('panicgraph-theme');
      if (saved === 'dark' || saved === 'light') return saved;
      return window.matchMedia('(prefers-color-scheme: light)').matches
        ? 'light' : 'dark';
    }

    function applyTheme(next) {
      document.documentElement.dataset.theme = next;
      try {
        localStorage.setItem('panicgraph-theme', next);
      } catch (err) {
        // Storage can be unavailable; the theme still applies for this page.
      }
    }

    function toggleTheme() {
      theme.value = theme.value === 'dark' ? 'light' : 'dark';
      applyTheme(theme.value);
    }
    const suppressed = ref(new Set());
    const idByDisplay = new Map();

    const allNames = computed(() =>
      ((graph.value && graph.value.categories) || []).map(c => c.name));

    /* Locking to one category is expressed in the model the rest of the tool
       already uses: every other category is assumed impossible. That keeps
       the reachability honest, so the paths on screen are exactly the paths
       that reach the locked category, rather than a filtered picture of a
       policy nobody chose. */
    const activePolicy = computed(() => {
      if (!exclusive.value) return suppressed.value;
      return new Set(allNames.value.filter(n => n !== exclusive.value));
    });

    const config = computed(() => (graph.value && graph.value.config) || {});
    const categories = computed(() =>
      (graph.value && graph.value.categories) || []);
    const counterfactual = computed(() =>
      (solution.value && solution.value.counterfactual) || []);
    /* Categories that name where the analysis stopped seeing rather than a
       way the program fails. They are shown, not hidden: an unread call is
       not a clean one. Marking them lets a reader tell the two apart, and
       set them aside deliberately when that is what they want. */
    const assumedNames = computed(() =>
      new Set(categories.value.filter(c => c.assumed).map(c => c.name)));
    const isAssumed = name => assumedNames.value.has(name);
    const assumedHidden = computed(() => assumedNames.value.size > 0
      && [...assumedNames.value].every(n => suppressed.value.has(n)));

    /* Most categories reach nothing in a given crate, and a column of zeroes
       pushes the ones that matter off the screen. What decides the split is
       whether a category is reached at all, not whether assuming it away
       clears anybody: a category every one of whose functions also reaches
       something else clears nobody, and calling that "reaches nothing" would
       hide it while the flame graph is still drawing it. Rows that move the
       most come first; the inert ones stay reachable behind a disclosure. */
    const activeRows = computed(() => counterfactual.value
      .filter(c => c.functions_reaching > 0 || c.suppressed)
      .sort((a, b) => b.functions_cleared - a.functions_cleared
        || b.functions_reaching - a.functions_reaching
        || (a.category < b.category ? -1 : 1)));
    const inertRows = computed(() => counterfactual.value
      .filter(c => !c.functions_reaching && !c.suppressed));
    const shownRows = computed(() =>
      (showInert.value ? [...activeRows.value, ...inertRows.value]
        : activeRows.value));
    const hasCleanup = computed(() =>
      Boolean(flame.value && flame.value.nodes
        && flame.value.nodes.some(n => n.cleanup)));
    const maxCleared = computed(() =>
      Math.max(1, ...counterfactual.value.map(c => c.functions_cleared)));

    const summary = computed(() =>
      (solution.value && solution.value.summary) || {});
    const delta = computed(() => {
      if (!previous.value || !solution.value) return null;
      return solution.value.summary.can_panic - previous.value.can_panic;
    });

    const caption = computed(() => {
      const on = [...activePolicy.value];
      if (!on.length) return 'Every panic category is considered possible.';
      return on.join(', ');
    });

    /* The suppression policy, encoded for the endpoints. */
    function policyQuery() {
      const list = [...activePolicy.value].join(',');
      return list ? `suppress=${encodeURIComponent(list)}` : 'suppress=';
    }

    /* The tree is folded by the server, so asking for every call is a
       different request rather than a different rendering. */
    function flameQuery() {
      return policyQuery() + (expand.value ? '&expand=1' : '');
    }

    /* The solve runs on the server. It is heavy enough that doing it here
       would block the main thread and freeze the page, where a request only
       makes the answer arrive a little later while the view stays alive. */
    async function refresh() {
      const token = (latest += 1);
      busy.value += 1;
      error.value = null;
      try {
        if (solution.value) previous.value = solution.value.summary;
        const [sol, fl] = await Promise.all([
          getJson(`/api/solve?${policyQuery()}`),
          getJson(`/api/flame?${flameQuery()}`),
        ]);
        // A click during a request must not be undone by the reply to the
        // click before it.
        if (token !== latest) return;
        solution.value = sol;
        flame.value = fl;
        if (selected.value) await explain(selected.value);
      } catch (err) {
        if (token === latest) error.value = err.message;
      } finally {
        busy.value -= 1;
      }
    }

    function lockTo(name) {
      exclusive.value = exclusive.value === name ? null : name;
      refresh();
    }

    function focusSearch() {
      const box = search.value;
      if (!box) return;
      box.focus();
      box.select();
    }

    function clearSearch() {
      query.value = '';
      matches.value = null;
    }

    function clearLock() {
      if (!exclusive.value) return;
      exclusive.value = null;
      refresh();
    }

    function toggleAssumed() {
      if (exclusive.value) return;
      const next = new Set(suppressed.value);
      const hide = !assumedHidden.value;
      for (const name of assumedNames.value) {
        if (hide) next.add(name); else next.delete(name);
      }
      suppressed.value = next;
      refresh();
    }

    function toggle(name) {
      if (exclusive.value) return;
      const next = new Set(suppressed.value);
      if (next.has(name)) next.delete(name); else next.add(name);
      suppressed.value = next;
      refresh();
    }

    watch(expand, () => {
      refresh();
    });

    function resetDefaults() {
      exclusive.value = null;
      suppressed.value = new Set(
        ['capacity-overflow', 'alloc-failure', 'ub-check']);
      refresh();
    }

    /* Starts from the default policy, then applies a lock named in the URL so
       a locked view can be shared as a link. */
    function startPolicy() {
      const params = new URLSearchParams(location.search);
      query.value = params.get('q') || '';
      const asked = params.get('only');
      suppressed.value = new Set(
        ['capacity-overflow', 'alloc-failure', 'ub-check']);
      exclusive.value =
        asked && allNames.value.includes(asked) ? asked : null;
      refresh();
    }

    async function explain(pick) {
      selected.value = pick;
      witness.value = null;
      if (!pick || !pick.rootFn || !pick.category) return;
      const node = idByDisplay.get(pick.rootFn);
      if (node === undefined) return;
      busy.value += 1;
      try {
        witness.value = await getJson(
          `/api/why?node=${node}`
          + `&category=${encodeURIComponent(pick.category)}`
          + `&${policyQuery()}`);
      } catch (err) {
        error.value = err.message;
      } finally {
        busy.value -= 1;
      }
    }

    function familyOf(name) { return FAMILY_OF[name] || 'unsure'; }
    function familyStyle(name) {
      return { background: `var(--series-${familyOf(name) === 'logic' ? 'logic'
        : familyOf(name) === 'alloc' ? 'alloc' : 'unsure'})` };
    }

    onMounted(async () => {
      busy.value += 1;
      try {
        graph.value = await getJson('/api/graph');
        for (const node of graph.value.nodes) {
          if (!idByDisplay.has(node.display)) {
            idByDisplay.set(node.display, node.id);
          }
        }
        startPolicy();
      } catch (err) {
        error.value = err.message;
      } finally {
        busy.value -= 1;
      }
    });


    function zoomTo(id) {
      if (icicle.value) icicle.value.zoomTo(id);
    }

    /* Crumbs are narrow and a css ellipsis would eat the identifying tail. */
    function step(delta) {
      if (icicle.value) icicle.value.cycle(delta);
    }

    function crumbLabel(name) {
      return name.length > 30 ? `..${name.slice(name.length - 28)}` : name;
    }

    applyTheme(theme.value);

    onMounted(() => {
      window.addEventListener('keydown', event => {
        // Take over find, the way a flame graph does, so the query searches
        // frames rather than the page text that happens to be rendered.
        if ((event.ctrlKey || event.metaKey) && event.key === 'f') {
          event.preventDefault();
          focusSearch();
          return;
        }
        if (event.key !== 'Escape') return;
        if (query.value) {
          clearSearch();
        } else {
          clearLock();
        }
      });
    });

    return { graph, solution, flame, selected, witness, error, showTable,
             trail, icicle, zoomTo, theme, toggleTheme,
             exclusive, lockTo, clearLock, activePolicy,
             query, matches, search, clearSearch, focusSearch, busy, expand,
             activeRows, inertRows, shownRows, showInert, crumbLabel,
             hasCleanup, step, chartWarning,
             suppressed, config, categories, counterfactual, maxCleared,
             summary, delta, caption, toggle, resetDefaults, explain,
             isAssumed, assumedHidden, toggleAssumed,
             familyStyle, FAMILY_LABEL };
  },
  template: `
<header>
  <h1>panicgraph</h1>
  <span class="meta" v-if="config.rustc">
    <span><b>{{ config.rustc }}</b></span>
    <span class="sep">|</span>
    <span><b>{{ config.profile }}</b> profile</span>
    <span class="sep">|</span>
    <span>overflow checks <b>{{ config.overflow_checks ? 'on' : 'off' }}</b></span>
    <span class="sep">|</span>
    <span>std <b>{{ (config.std_mode || '').toLowerCase() }}</b></span>
  </span>
  <span class="spacer"></span>
  <button class="ghost" :aria-pressed="String(showTable)"
    @click="showTable = !showTable">Table view</button>
  <button class="ghost" :aria-pressed="String(assumedHidden)"
    :disabled="Boolean(exclusive)"
    @click="toggleAssumed"
    title="Assume impossible every category that names an unread call rather
than a panic">
    {{ assumedHidden ? 'Show unread' : 'Hide unread' }}</button>
  <button class="ghost" @click="resetDefaults">Reset policy</button>
  <button class="ghost" @click="toggleTheme"
    :title="'Switch to ' + (theme === 'dark' ? 'light' : 'dark') + ' mode'">
    {{ theme === 'dark' ? 'Light' : 'Dark' }}
  </button>
</header>

<div class="progress" :class="{ on: busy > 0 }" role="status"
  :aria-label="busy ? 'Working' : ''"><span></span></div>

<div class="policy-caption" :class="{ locked: exclusive }">
  <template v-if="exclusive">
    <span class="lock-badge">only</span>
    Locked to <strong>{{ exclusive }}</strong>. Every other category is
    assumed impossible, so the paths below are exactly the ones that reach it.
    <button class="ghost small" @click="clearLock">Clear lock</button>
    <span class="kbd-hint">esc</span>
  </template>
  <span v-else-if="activePolicy.size">Assuming impossible:
    <strong>{{ caption }}</strong>. Everything else is considered
    possible.</span>
  <span v-else>{{ caption }}</span>
</div>

<main>
  <aside>
    <h2>Result</h2>
    <div class="tiles">
      <div class="tile wide">
        <div class="n">
          {{ summary.can_panic ?? '-' }}
          <span class="of">of {{ summary.analysed ?? '-' }}</span>
          <span v-if="delta" class="delta">
            {{ delta > 0 ? '+' : '' }}{{ delta }}
          </span>
        </div>
        <div class="k">functions can panic</div>
      </div>
      <div class="tile wide">
        <div class="n">{{ summary.clean_by_suppression ?? '-' }}</div>
        <div class="k">clean only because of this policy</div>
      </div>
    </div>

    <h2>Assume impossible</h2>
    <p class="k" style="color:var(--text-muted);font-size:11px;margin:0 0 8px">
      The count is how many functions reach that category. The bar is how
      many stop being interesting if it alone is assumed impossible, which
      is fewer whenever those functions also reach something else.
    </p>
    <div v-for="c in shownRows" :key="c.category" class="cat"
      :class="{ off: activePolicy.has(c.category) && !exclusive,
                solo: exclusive === c.category,
                muted: exclusive && exclusive !== c.category }">
      <div class="cat-row">
        <input type="checkbox" :checked="activePolicy.has(c.category)"
          :disabled="Boolean(exclusive)"
          :aria-label="'Assume ' + c.category + ' impossible'"
          @change="toggle(c.category)">
        <span class="family-dot" :style="familyStyle(c.category)"></span>
        <span class="name" @click="toggle(c.category)">{{ c.category }}</span>
        <span v-if="isAssumed(c.category)" class="unread"
          title="Not a panic. The analysis could not read what this call
reaches, so it reports where it stopped seeing rather than a way to fail.">
          unread</span>
        <button class="only" @click="lockTo(c.category)"
          :aria-pressed="String(exclusive === c.category)"
          :title="exclusive === c.category
            ? 'Release the lock and return to the policy'
            : 'Show only ' + c.category + ', assuming every other category impossible'">
          only
        </button>
        <span class="n" :class="{ stale: busy > 0 }"
          :title="c.functions_reaching + ' functions reach ' + c.category
            + ', ' + c.functions_cleared + ' of them only through it'">
          {{ c.functions_reaching }}</span>
      </div>
      <span class="bar-track" :class="{ stale: busy > 0 }">
        <span class="bar" :style="{ width: (100 * c.functions_cleared / maxCleared) + '%' }"></span>
      </span>
    </div>

    <button v-if="inertRows.length" class="disclose"
      :aria-expanded="String(showInert)" @click="showInert = !showInert">
      {{ showInert ? 'Hide' : 'Show' }} {{ inertRows.length }} categories that
      reach nothing here
    </button>

    <p v-if="chartWarning" class="err">{{ chartWarning }}</p>
    <p v-if="error" class="err">{{ error }}</p>
  </aside>

  <section class="stage">
    <div class="legend">
      <span class="item" v-for="(label, key) in FAMILY_LABEL" :key="key">
        <span class="swatch" :style="{ background: 'var(--series-' + key + ')' }"></span>
        {{ label }}
      </span>
      <span class="item" v-if="hasCleanup">
        <span class="gate-key"></span> runs while unwinding</span>
      <span class="item note">width = reachable panics</span>
      <span class="spacer"></span>
      <button class="ghost small" :aria-pressed="String(expand)"
        @click="expand = !expand"
        title="Show every call in the path instead of folding runs of single calls">
        {{ expand ? 'Fold chains' : 'Expand chains' }}
      </button>
      <span class="search" :class="{ active: query }">
        <input ref="search" type="search" v-model="query"
          placeholder="Search frames"
          aria-label="Highlight matching frames, enter steps through them"
          spellcheck="false"
          @keydown.enter.prevent="step($event.shiftKey ? -1 : 1)">
        <span v-if="matches" class="tally" role="status" aria-live="polite">
          <template v-if="matches.at">{{ matches.at }} of </template>
          {{ matches.frames }} {{ matches.frames === 1 ? 'frame' : 'frames' }}
          <b>{{ matches.share }}%</b>
        </span>
        <button v-if="query" class="only" @click="clearSearch"
          title="Clear the search">clear</button>
        <span v-else class="kbd-hint">ctrl f</span>
      </span>
    </div>

    <nav class="crumbs" aria-label="Zoom level">
      <template v-if="trail.length > 1">
        <button v-for="(c, i) in trail" :key="c.id" class="crumb"
          :disabled="i === trail.length - 1" @click="zoomTo(c.id)">
          {{ c.name === 'crate' ? 'all functions' : crumbLabel(c.name) }}
        </button>
      </template>
      <template v-else>
        <span class="crumb rest">all functions</span>
        <span class="crumb-hint">click a frame to zoom in</span>
      </template>
    </nav>
    <div class="stage-body">
      <icicle-chart v-if="flame" ref="icicle"
        :flame="flame" :theme="theme"
        :query="query" @pick="explain" @trail="trail = $event"
        @matches="matches = $event" @warn="chartWarning = $event"></icicle-chart>
      <div v-if="busy === 0 && flame && flame.nodes
             && flame.nodes.length <= 1" class="veil quiet">
        <div>
          <p class="lead">Nothing can panic under this policy.</p>
          <p>Every category that reaches a panic here is assumed impossible.
            Untick one on the left, or
            <button class="linkish" @click="resetDefaults">reset the policy</button>.</p>
        </div>
      </div>
      <div v-if="busy > 0" class="veil">
        <span class="spinner" aria-hidden="true"></span>
        <span>{{ flame ? 'Resolving policy' : 'Loading analysis' }}</span>
      </div>
    </div>

    <div class="detail">
      <template v-if="showTable">
        <h2 style="margin-top:0">Panic categories</h2>
        <table class="data">
          <thead><tr><th>category</th><th>kind</th>
            <th>assumed impossible</th>
            <th class="n">direct sites</th><th class="n">functions reaching</th>
            <th class="n">functions cleared</th></tr></thead>
          <tbody>
            <tr v-for="c in counterfactual" :key="c.category">
              <td>{{ c.category }}</td>
              <td>{{ isAssumed(c.category) ? 'unread' : 'panic' }}</td>
              <td>{{ c.suppressed ? 'yes' : 'no' }}</td>
              <td class="n">{{ c.sites }}</td>
              <td class="n">{{ c.functions_reaching }}</td>
              <td class="n">{{ c.functions_cleared }}</td>
            </tr>
          </tbody>
        </table>
      </template>
      <template v-else-if="witness && witness.found">
        <h2 style="margin-top:0">
          {{ witness.root }} can panic with {{ witness.category }}
        </h2>
        <ul class="path">
          <li><span class="fn">{{ witness.root }}</span></li>
          <li v-for="(hop, i) in witness.hops" :key="i"
            :class="{ cleanup: hop.cleanup }">
            <span class="fn">{{ hop.to_display }}</span>
            <span class="tag" v-if="hop.cleanup">while unwinding</span>
            <div class="where">{{ hop.kind }} call at {{ hop.loc || 'unknown location' }}</div>
          </li>
          <li class="terminal">
            <span class="fn">{{ witness.terminal.reason || witness.terminal.display || witness.terminal.kind }}</span>
            <div class="where" v-if="witness.terminal.loc">{{ witness.terminal.loc }}</div>
            <div class="where" v-if="witness.terminal.sink">sink: {{ witness.terminal.sink }}</div>
          </li>
        </ul>
      </template>
      <template v-else-if="selected">
        <p class="empty">No path to a panic from here under the current policy.</p>
      </template>
      <template v-else>
        <p class="empty">
          Click any frame to see the call path from a local function to the
          panic it reaches.
        </p>
      </template>
    </div>
  </section>
</main>`,
}).mount('#app');

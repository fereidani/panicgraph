#!/usr/bin/env bash
# Runs panicgraph over a list of crate directories and prints one markdown
# table row per crate: functions analysed, findings, how many of those carry
# only assumed categories, how many distinct definition sites the rest come
# from, and the busiest categories.
#
# The distinct sites column is the one to watch on a crate that stamps out
# one function per array size or integer type with a macro: every copy
# reports the same line, so a single check the analysis cannot settle
# counts once there and many times in the findings column.
#
# Usage:
#   scripts/corpus.sh /path/to/crate [/path/to/another ...]
#   scripts/corpus.sh --suppress '' /path/to/crate
#
# Ground truth for false positives comes from crates that are known panic
# free by external proof, for example ones gated by the no-panic crate or
# shipped with panic = "abort" guarantees: every finding there, once the
# assumed categories are set aside, is a false positive to investigate.
# Tracking the table over time is what makes a precision change visible.

set -euo pipefail

SUPPRESS="default"
if [ "${1:-}" = "--suppress" ]; then
  SUPPRESS="$2"
  shift 2
fi

if [ "$#" -eq 0 ]; then
  echo "usage: $0 [--suppress LIST] <crate-dir> [crate-dir ...]" >&2
  exit 2
fi

PANICGRAPH="${PANICGRAPH:-panicgraph}"

echo "| crate | analysed | findings | assumed only | distinct sites | top categories |"
echo "|---|---:|---:|---:|---:|---|"

for dir in "$@"; do
  json="$("$PANICGRAPH" --manifest-dir "$dir" --suppress "$SUPPRESS" \
      --format json 2>/dev/null || true)"
  if [ -z "$json" ]; then
    echo "| $(basename "$dir") | build failed | | | | |"
    continue
  fi
  PG_NAME="$(basename "$dir")" PG_JSON="$json" python3 <<'PY'
import collections
import json
import os

name = os.environ["PG_NAME"]
report = json.loads(os.environ["PG_JSON"])
findings = report.get("findings", [])
assumed = {"unknown", "foreign", "dyn-call", "fn-pointer", "generic-bound"}
counts = collections.Counter()
assumed_only = 0
sites = set()
for finding in findings:
    categories = set(finding.get("categories", []))
    counts.update(categories)
    if categories and categories <= assumed:
        assumed_only += 1
    else:
        sites.add(finding.get("location"))
top = ", ".join(f"{c} {n}" for c, n in counts.most_common(5))
print(
    f"| {name} | {report.get('analysed', '?')} | {len(findings)} "
    f"| {assumed_only} | {len(sites)} | {top} |"
)
PY
done

#!/bin/bash
# status.sh [LOGDIR] : compact progress summary for probe.sh jobs (last events + latest kissat report per run).
# From kissat's verbose report line: secs, MB, conflicts, and remaining active variables (count, %).
L=${1:-$(cd "$(dirname "$0")/.." && pwd)/logs/probes}
tail -n 4 "$L/status.tsv" 2>/dev/null | cut -c1-140
for f in "$L"/*.log; do
  [ -e "$f" ] || continue
  grep -E '^c [^ ] +[0-9]+\.[0-9]+ ' "$f" | tail -1 | awk -v n="$(basename "$f" .log)" \
    '{printf "%s: t=%ss mem=%sMB conflicts=%s remaining=%s (%s)\n", n, $3, $4, $10, $(NF-1), $NF}'
done

#!/usr/bin/env bash
# leanslot.sh cmd [args...]
# Machine-wide semaphore for heavy jobs (Lean compiles ~3 GB each): at most $SLOTS run at once across ALL
# agents/sessions. Waits for a free slot, runs cmd under the memcap watchdog (6000 MB), then frees the slot.
# Usage:  tools/leanslot.sh lake env lean Erdos/E132Main43Charge.lean
set -u
SLOTS=${LEANSLOTS:-2}
DIR=/tmp/erdoslab-leanslots
mkdir -p "$DIR"
here=$(cd "$(dirname "$0")" && pwd)
slot=""
while [ -z "$slot" ]; do
  for i in $(seq 1 "$SLOTS"); do
    if mkdir "$DIR/slot$i" 2>/dev/null; then echo $$ > "$DIR/slot$i/pid"; slot=$i; break; fi
    # reclaim a slot whose owner died (e.g. after a crash)
    p=$(cat "$DIR/slot$i/pid" 2>/dev/null); if [ -n "$p" ] && ! kill -0 "$p" 2>/dev/null; then rm -rf "$DIR/slot$i"; fi
  done
  [ -z "$slot" ] && sleep 5
done
trap 'rm -rf "$DIR/slot$slot"' EXIT INT TERM
"$here/memcap.sh" "${LEANSLOT_MB:-6000}" "$@"

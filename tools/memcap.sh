#!/usr/bin/env bash
# memcap.sh LIMIT_MB cmd [args...]
# Run cmd; poll the total RSS of cmd and all its descendants every second; kill the whole tree if it
# exceeds LIMIT_MB. macOS ignores `ulimit -v` and RLIMIT_AS, so this is the real cap.
# Exit code: cmd's own, or 137 if killed for memory.
set -u
limit_kb=$(( ${1:?limit MB} * 1024 )); shift
"$@" &
root=$!
tree() { local p=$1; echo "$p"; for c in $(pgrep -P "$p" 2>/dev/null); do tree "$c"; done; }
killed=0
while kill -0 "$root" 2>/dev/null; do
  pids=$(tree "$root" | paste -sd, -)
  rss=$(ps -o rss= -p "$pids" 2>/dev/null | awk '{s+=$1} END{print s+0}')
  if [ "$rss" -gt "$limit_kb" ]; then
    echo "memcap: RSS $((rss/1024)) MB > $((limit_kb/1024)) MB — killing $* (pids $pids)" >&2
    for p in $(tree "$root"); do kill -9 "$p" 2>/dev/null; done
    killed=1; break
  fi
  sleep 1
done
wait "$root" 2>/dev/null; rc=$?
[ "$killed" = 1 ] && exit 137
exit "$rc"

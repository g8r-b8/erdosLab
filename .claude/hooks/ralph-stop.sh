#!/bin/bash
# Ralph loop Stop hook: re-feeds PROMPT.md until the completion promise appears
# or max iterations is hit. Disable by deleting .claude/ralph-loop.state
set -euo pipefail
DIR="$(cd "$(dirname "$0")/../.." && pwd)"
STATE="$DIR/.claude/ralph-loop.state"
PROMPT="$DIR/PROMPT.md"
MAX=${RALPH_MAX_ITERATIONS:-60}
PROMISE='<promise>ERDOS_DONE</promise>'

[ -f "$STATE" ] || exit 0
input=$(cat)
transcript=$(echo "$input" | jq -r '.transcript_path // empty')

if [ -n "$transcript" ] && [ -f "$transcript" ] && \
   tail -n 40 "$transcript" | jq -r 'select(.type=="assistant") | .message.content[]? | select(.type=="text") | .text' 2>/dev/null | grep -qF "$PROMISE"; then
  rm -f "$STATE"; exit 0
fi

iter=$(cat "$STATE" 2>/dev/null || echo 0)
iter=$((iter + 1))
if [ "$iter" -gt "$MAX" ]; then rm -f "$STATE"; exit 0; fi
echo "$iter" > "$STATE"

jq -n --arg r "Ralph loop iteration $iter/$MAX. $(cat "$PROMPT")" '{decision:"block", reason:$r}'

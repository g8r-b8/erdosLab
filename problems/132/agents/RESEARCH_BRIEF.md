# Shared brief for #132 research agents (durable copy; the scratchpad was wiped by kernel panics on 2026-09-25)

Repo: /Users/wingatejones/Projects/erdosLab. Read first: problems/132/README.md, NOVELTY.md, frontier.md, and the angle
files relevant to your task (angle_R1–R7.md, REFEREE2_R6.md). Proven Lean infrastructure: Erdos/Erdos/E132*.lean
(54/37 and 15/11 fully formalised; E132Main43* = 4/3 in progress).

## Rules
1. Mathematics first: rigorous proofs, or a counterexample, or a precise obstruction. Write every step; flag doubtful
   steps; never overclaim (e.g. "matches the lower bound", not "sharp", unless attainment is shown in that regime).
2. Verification: test every claimed lemma adversarially with exact arithmetic (sympy / fractions / mpmath intervals).
   Floats are sanity checks only, never proof.
3. Files you own: the file(s) named in your task plus problems/132/scripts/<your prefix>_*.py. Don't edit others' files.
4. Commit only your own files (`git add <paths>`, never -A); messages end with
   "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>".
5. REPORTS GO IN THE REPO, not the scratchpad: write your full report to problems/132/angle_R7_reports/<NAME>_report.md
   (or the directory your coordinator names) and commit it. Also put the full findings in your final reply, because
   file writes are sometimes blocked for subagents and a parent may not receive a child's final reply.
6. Agent per branch at every crossroad (user instruction): don't pick one route; launch one agent per branch,
   recursively (depth cap 4). STAGGER them: at most 2 running per coordinator. Checkpoint (commit) after each branch.

## Compute and memory (16 GB Mac shared by all erdosLab sessions; two kernel panics on 2026-09-25)
- At most 2–3 heavy processes MACHINE-WIDE. Before any Lean compile, SAT run or large search: check
  `ps -Ao pid,rss,comm -m | head` and `sysctl vm.swapusage`; wait if another heavy job is running.
- macOS IGNORES `ulimit -v` and RLIMIT_AS. Cap memory with the RSS watchdog:
  `/Users/wingatejones/Projects/erdosLab/tools/memcap.sh 4000 <cmd...>` (kills the process tree above 4000 MB; exit 137).
- Lean: ONE `lake env lean` at a time per workstream (≈3 GB each); never `lake exe cache get` / `lake update`;
  no new axioms, no native_decide / bv_decide.
- Disk: stop if `df -h /System/Volumes/Data` shows < 3 GB free. Nothing > 1 GB on disk.
- Never run parallel batches (no N-way anything).

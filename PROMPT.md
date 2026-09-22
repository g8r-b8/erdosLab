# Ralph loop prompt — erdosLab

Goal: find an **open** Erdős problem that we can plausibly resolve (prove or disprove) and
**formally verify in Lean 4 + Mathlib**, as fast as possible.

Every iteration: read `NOTES.md` first (create it if missing), do the next concrete step,
update `NOTES.md` (status, candidates, what was tried, next step), and commit.

## Hard rule: the problem must be genuinely UNSOLVED
Before committing effort to a candidate, and again before claiming success:
1. Check its page on https://www.erdosproblems.com/<N> — status must be **open**
   (not "proved", "disproved", "solved", "falsifiable-resolved", or "Lean-verified").
   Read the comments/notes section on the page too — recent resolutions show up there first.
2. Check https://github.com/google-deepmind/formal-conjectures (ErdosProblems/) — if a
   solved/proved statement exists, drop it.
3. Search arXiv / the web for "Erdős problem <N>" in the last ~2 years (lots were closed
   by AI-assisted work in 2025–2026). Any claimed resolution → drop it.
4. Check EVERY cross-referenced / "See also" / duplicate problem page AND its forum thread
   (e.g. #468 ↔ #1054): comments get MOVED between threads and resolutions are often recorded
   only on the sibling page. Also read Tao's AI-contributions wiki and the OEIS entries' links.
5. Record the evidence (URLs + date checked) in `NOTES.md` under the candidate.
If you can't confirm it's open, it's not a candidate.

## Candidate selection
Prefer problems that are: finite/computational in flavour, have a small decidable core,
or a clean elementary statement where Mathlib already has the needed API. Avoid problems
needing heavy analytic number theory not in Mathlib. Keep a ranked shortlist in NOTES.md.

## Lean setup
- Toolchain via elan; project via `lake new erdos math` (Mathlib). Use `lake exe cache get`.
- Long commands (installs, `lake build`, cache get) → run in background, don't block.
- Scaffold-then-fill: state theorems first with `sorry`, commit, then fill proofs one lemma
  at a time, committing each.
- Never claim a result that has `sorry`, `admit`, `native_decide` without noting it, or new
  `axiom`s. Check with `#print axioms`.

## Done
Only when there is a sorry-free, axiom-clean Lean proof of an open-verified Erdős problem
(or a disproof by verified counterexample), with the verification evidence in NOTES.md,
output exactly: <promise>ERDOS_DONE</promise>
If genuinely stuck after exhausting candidates, write a summary in NOTES.md and output
<promise>ERDOS_DONE</promise> with an honest "not solved" report. Never fake completion.

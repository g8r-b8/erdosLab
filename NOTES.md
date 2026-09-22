# erdosLab notes

## Status (iteration 1, 2026-09-22)
- Lean: elan installed (~/.elan/bin). Mathlib project `Erdos/` being created + cache fetched (background).
- Data: cloned teorth/erdosproblems (data/problems.yaml, updated 2026-09-22) and
  google-deepmind/formal-conjectures into the session scratchpad.
- Site stats: 1221 problems; 593 with status exactly "open".

## Observations
- "decidable" status (19, 475, 506, 551, 556, 580, 742, 848) = proven for large n with
  ineffective/huge thresholds → finite check not feasible. Skip.
- erdosproblems.com pages show community "looks tractable" votes and proof-claim counts —
  use these to rank candidates.
- Recent problems (1050–1221) have had less attention → triage there first.

## Candidates (ranked; each needs open-verification evidence before work)
- 1210 — pairwise coprime A ⊆ [1,n), is Σ 1/(n−a) ≤ Σ_{p<n} 1/p + O(1)? 3 "looks tractable"
  votes. Open per site (checked 2026-09-22, last update 2026-04-08). Concern: needs sharp
  constant 1 on loglog n → sieve/parity issues. Not yet in Lean.
  Own analysis (iter 3): write b = n−a. gcd(n−b, n−b') | (b−b'), so CRT constructions
  (n ≡ c_q mod small q) reduce to: S ⊆ [1,k] missing one residue class mod each prime q<k;
  best Σ1/b ≈ loglog k while n ≳ e^k, so constructions only give ~logloglog-scale vs loglog n
  → no easy counterexample. Upper bound via dyadic blocks (π(2B) small-factor elements +
  Brun–Titchmarsh count of rough ones) gives O(loglog n) but constant ≈ 2/log 2-ish, not 1.
  Getting constant 1 looks like genuine sieve work → probably NOT an ASAP target.
- 1209 — mostly resolved (counterexamples); only residual variants left. Low priority.

## Tried / dropped
- 19, 475, 506, 551: decidable-but-infeasible finite checks.
- 1218, 1220: large-cardinal set theory, not Mathlib-friendly.
- 1221: asymptotic analysis on circle, no obvious handle.

## Next step
- Parallel triage of open problems 1050–1221 for tractability + open-status evidence.

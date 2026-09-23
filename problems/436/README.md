# Erdős Problem #436: consecutive k-th power residues (triples, k = 5)

**Status (ours):** computational attack on the smallest open case Λ(5,3). No resolution.
New: **Λ(5,3) ≥ 2,000,028,671** (warm-start local search + small-prime smooth fix; witness in `logs/warmstart/`, independently verified); brute-force
finiteness certificate estimated at ~1e18 nodes (infeasible; see THEORY.md).
**Site status:** OPEN (erdosproblems.com/436, rechecked 2026-09-23).

## Statement (erdosproblems.com/436, verbatim in substance)
For a prime p and k, m ≥ 2 let r(k,m,p) be the least r ≥ 1 such that r, r+1, …, r+m−1 are all
k-th power residues mod p, and Λ(k,m) = limsup_{p→∞} r(k,m,p).
Is Λ(k,2) finite for all k? Is Λ(k,3) finite for all odd k? How large are they?

Known (site / OEIS A000445): Λ(k,2) < ∞ for all k (Hildebrand 1991); Λ(2,2)=9, Λ(3,2)=77,
Λ(4,2)=1224, Λ(5,2)=7888, Λ(6,2)=202124, Λ(7,2)=1649375; Λ(3,3)=23532 (Lehmer–Lehmer–Mills–Selfridge
1962, "Machine proof of a theorem on cubic residues"); Λ(k,3)=∞ for even k; Λ(k,l)=∞ for l ≥ 4
(Graham 1964). Open: Λ(k,3) for odd k ≥ 5. Smallest open case: **Λ(5,3)**.
Note: answering "finite for all odd k" needs more than k = 5, but Λ(5,3) = ∞ would disprove it,
and Λ(5,3) < ∞ would be the first new case.

## Openness evidence (copied from NOTES.md triage, rechecked 2026-09-23)
- erdosproblems.com/436: OPEN; forum thread: 3 comments (Adenwalla 24–25 Oct 2025, Bloom 25 Oct
  2025) — notation fix, LLMS 1962 reference, a literature compilation; no claims, no computations.
  No see-also / duplicate links.
- teorth/erdosproblems problems.yaml: 436 open, formal_status "unformalized".
- formal-conjectures: no ErdosProblems/436 file; issue #731 "Erdős Problem 436" open ("up for
  grabs", 0 comments).
- Tao's AI-contributions wiki (clone, last commit 2026-06-30): no mention of 436.
- arXiv/web: Dietzel 1309.7506, 1810.01518 (pairs / Hildebrand) only; nothing on triples for k ≥ 5.
  (Williams 1976 "Explicit criteria for quintic residuacity" is about which small q are quintic
  residues, not runs.)

## Definition ↔ combinatorial model (the reduction)
Λ_comb(k,l) := sup over completely additive f: Z_{>0} → Z/k of the least r with
f(r) = … = f(r+l−1) = 0.

**Upper bound (elementary, what "finite" needs): Λ(k,l) ≤ Λ_comb(k,l).**
Given p, let d = gcd(k, p−1), g a primitive root, and f_p(n) = (k/d)·(ind_g n mod d) ∈ Z/k for
p ∤ n. f_p is a homomorphism (Z/p)^* → Z/k with f_p(n) = 0 ⇔ n is a k-th power residue (for p ∤ n,
n is a k-th power ⇔ d | ind n). Extend to all positive integers by F(q) = f_p(q) for primes q < p,
F(q) = 1 otherwise; then F is completely additive and F(n) = f_p(n) for 1 ≤ n < p. If
Λ_comb = L < ∞, F has a zero run at some r ≤ L, and for p > L+l−1 these are k-th power residues:
r(k,l,p) ≤ L for all p > L+l−1. (This covers all p, not only p ≡ 1 mod k.)
Moreover S(R) := "∃ f with no zero run at r ≤ R" only involves f on primes ≤ R+l−1, so
Λ_comb ≤ R ⇔ the finite SAT instance S(R) is UNSAT. By compactness (König), Λ_comb = ∞ ⇔ some f
has no zero run at all.

**Lower bound (needs Chebotarev; only needed for exact values / for Λ = ∞):** for odd k the primes
q_1 < … < q_m are independent in Q(ζ_k)^*/(Q(ζ_k)^*)^k, so by Chebotarev in
Q(ζ_k, q_1^{1/k}, …, q_m^{1/k}) every assignment of the q_i's k-th power characters (up to a unit of
Z/k) occurs for infinitely many p ≡ 1 mod k. Hence Λ(k,l) = Λ_comb(k,l) for odd k (also a model with
no zero run up to R gives Λ(k,l) ≥ R). For even k there can be Kummer obstructions (e.g. √2 ∈ Q(ζ_8)),
so the model is only an upper bound there — but it still reproduces the known values for k = 2, 4.

## Results
1. **Validation** (`scripts/lam_sat.py` incremental pysat/CaDiCaL; `scripts/lamenc.c` + kissat via
   `scripts/drive.py`): exact search reproduces Λ_comb = 9, 77, 1224, 7888 for (k,2), k = 2..5, and
   Λ_comb(3,3) = 23532 (kissat 2 s; final UNSAT DRAT proof checked by drat-trim, 1.2 MB LRAT).
   So the model matches all literature values tested.
2. **k = 5, l = 3:** Λ(5,3) ≥ 5,062,794 (new lower bound, via SAT model + Chebotarev); no
   finiteness certificate yet (see Log).

## Files
- `scripts/lam_sat.py` — reference incremental encoder + exact search (pysat Cadical153).
- `scripts/lamenc.c` — compact DIMACS encoder (dominance for primes > N/2; z-only composites) and
  model decoder; `scripts/drive.py` — exact / geometric search with kissat.
- `scripts/smoothruns.c` — segmented sieve listing runs of l consecutive y-smooth numbers ≤ X.
- `scripts/smooth_sat.py` — weakened instance F_y(X) (only primes ≤ y, only smooth runs).
- `scripts/smooth_cnf.py` — compact streaming DIMACS for F_y(X) (+ cubes); `scripts/run_cubes.sh`,
  `scripts/cubes.py` — cube-and-conquer; `scripts/sdfs.c` — direct DFS / Knuth tree-size estimator.
- `logs/` — solver logs.

## Log (2026-09-23)
- **Full instance S(R), k=5, l=3** (`drive.py --grow 1.5`, kissat): SAT at R = 1.07e6, 1.5e6,
  2.25e6, 3.375e6, 5.0625e6 (solve 10 s → 64 s), with model first-run 5,062,794.
  ⇒ **Λ_comb(5,3) ≥ 5,062,794**, hence (Chebotarev, k odd) Λ(5,3) ≥ 5,062,794. Hardness jumps at
  R = 7,593,750 (kissat > 1 h, running). Even f = Ω(n) mod 5 already has its first zero triple at
  r = 1,073,149.
- **Structure of models:** both the full-instance model (R=2.25e6) and the F_500 model have
  f(2)=0, f(3)=1 (up to units) and f = 0 on most small primes (5,7,11,13,17,23,29,31,41,43,47,53,
  59,71,83), nonzero on 19,37,61,67,73,79,89,97,… and value 1 on most larger primes — i.e.
  "v_3(n) mod 5 plus an Ω-like count of large primes". Every branch f(2)=f(3)=0 is UNSAT at once.
  Finitely supported f always fail (CRT: r+1 ≡ 0 mod (∏p)^5 exactly); likewise any finite sum of
  local characters / Dirichlet characters (odd order ⇒ χ(−1)=1). So an infinite construction
  would need a genuinely global f; none found.
- **Smooth weakening F_y(X)** (only primes ≤ y; only runs of 3 consecutive y-smooth numbers ≤ X):
  sound for UNSAT (subset of constraints) and F_y(∞) is finite (Størmer). Calibration on k=3:
  F_200(1e8) SAT (a unique model up to units!), F_300(1e8) UNSAT (kissat 2 s) ⇒ Λ(3,3) ≤ 1e8.
  For k=5: F_200(1e9) SAT, F_300(1e9) SAT, F_500(1e9) SAT (cube f(2)=0,f(3)=1,f(5)=0; 7 min).
  F_1000(1e9) (168 primes, 247,734 triples, 12.4M clauses): cube-and-conquer on f(2),f(3),f(5)
  running; f(2)=f(3)=0 cubes UNSAT in 4 s; f(2)=0,f(3)=1 cubes > 30 min each.
  Naive first-moment counts are useless here (they predict UNSAT for k=3, y=200, which is SAT).
- **Direct DFS on F_y(X)** (`scripts/sdfs.c`: assign f(p) in increasing p, each smooth run forbids
  ≤ 1 value of its largest prime): k=3, F_300(1e8) refuted with 31,538 nodes in 0.03 s (vs kissat
  2 s) — a trivially checkable case tree. For k=5 Knuth's random-probe estimator
  (`logs/knuth_estimates.log`) gives ≈ 1e18 nodes for every y ∈ {200,…,1000}, X ∈ {1e9,1e10}; the
  tree is ≈1e14 wide already at depth 25 (primes ≤ 100), because the only constraints on the first
  25 primes are the ~787 runs of 100-smooth numbers (a finite set, Størmer), each killing ≤ 1/125 of
  assignments: 5^25·(124/125)^787 ≈ 1e14. Every probe dies by depth ≈ 47 (primes ≤ ~210) at
  y=1000, so F_1000(1e10) may well be UNSAT, but any case-split proof that branches on small primes
  needs ~1e14–1e18 leaves. **Verdict: a brute-force finiteness certificate for Λ(5,3) is out of
  reach** (k=3 is 31k nodes; k=5 is ~13 orders of magnitude larger). CDCL cubes (f(2)=0, f(3)=1)
  on F_1000(1e9) ran > 45 min each without result.
- Counts of consecutive smooth triples: y=1000: 247,734 (X=1e9), 343,634 (X=1e10);
  y=2000: 1,031,687 (X=1e9).

## Next steps
Background jobs ended: all were killed by SIGTERM (rc=143, not by us) after ~2.2 h —
full S(7,593,750) with no answer after >80 min of kissat; F_1000(1e9) cubes with f(2)=0, f(3)=1
UNKNOWN after ~7,850 s each (`logs/cubes_y1000_1e9.log`). Not restarted, given the ~1e18 estimate.
1. Theory, not search: the obstruction is the huge solution space on small primes. Ideas: prove
   f(2)=0 ⇒ … structural lemmas (models all have f(2)=0, f(3)≠0, f=0 on most p ≤ 100) to collapse
   the top of the tree; or an algebraic (F_5-linear) refutation instead of case splits.
2. Hybrid instance full S(N0) ∪ F_y(X) (sound) with cube-and-conquer on many cores/cloud;
   Knuth-estimate first.
3. If an UNSAT certificate ever appears: re-run cubes with `kissat --no-binary` proofs, drat-trim
   → LRAT, record hashes.
4. Lean route (only if UNSAT): (a) elementary reduction (k-th power character ⇒ completely
   additive F, as above) — Mathlib has ZMod units cyclic + orderOf; (b) a Lean function generating
   the same CNF from the list of smooth runs, with a soundness lemma (any f ⇒ satisfying
   assignment); the list of runs itself needs no completeness proof, only that each listed r has
   r, r+1, r+2 ≤ X and the factorizations are correct (checkable); (c) LRAT check via Lean core's
   `Std.Tactic.BVDecide.LRAT` checker. With ~10^7 clauses the check needs compiled evaluation
   (`native_decide` / `ofReduceBool`, as `bv_decide` itself uses) — must be disclosed per PROMPT.md;
   a kernel-only check is not realistic at this size.

## Verbose probes (2026-09-23, parent session)
The earlier `-q` runs gave no progress information, so they were stopped (S(7,593,750) after 3 h, and the y=1000 cubes after 2.2 h).
Relaunched with `scripts/probe.sh` (kissat `-v`). Output goes to files only:
- `logs/probes/<tag>.log`: the full kissat report.
- `logs/probes/status.tsv`: one line per event.

`scripts/status.sh` prints a compact summary: time, memory, conflicts, and remaining variables.
Runs:
- R = 7,593,750: the stalled instance.
- R = 6,634,000 and R = 5,795,000: bisection probes, geometric between the last SAT R and 7.59M.

Purpose: locate the SAT→hard transition. A quick SAT result raises the lower bound. A stall localises the smallest hard instance, which is the best target for an UNSAT proof. No proof is logged: an UNSAT result would be re-run with proof output (disk: about 10 GB free).

- 2026-09-23 12:40: probe R=5,420,000 SAT in 27 s, first run 5,420,007 ⇒ **Λ(5,3) ≥ 5,420,007** (new best lower bound, via Chebotarev as before).
  R=5,795,000 had not returned after 17+ CPU-min (trend predicted ~75 s), so the transition lies in (5.42M, 5.795M]. Probe R=5,605,000: SAT in 23 s, first run 5,605,389 ⇒ **Λ(5,3) ≥ 5,605,389**. Bracket (5.605M, 5.795M]; probe R=5,700,000: SAT in 26 s ⇒ **Λ(5,3) ≥ 5,700,375**. Bracket (5.70M, 5.795M]; probes: R=5,750,000 and R=5,795,000 re-run with seed 7 (checking whether the 5.795M stall is a threshold or bad luck). R=5,750,000: SAT in 96 s (4× slower) ⇒ **Λ(5,3) ≥ 5,750,107**. Bracket (5.75M, 5.795M].
- 2026-09-23 13:20 — **Caveat: the "transition" is a solver-heuristic artifact, not a hardness threshold.** Every SAT probe up to 5.75M
  was solved by kissat's *lucky* phase ("lucky in forward setting literals to true") with **0 conflicts**: profiling shows 0.00 s in
  search. The greedy forward-true assignment happens to satisfy S(R) for R ≤ 5.75M and fails just above that. Past that point, kissat spends
  ~1050 s in the remaining lucky strategies ("inconsistency after 68715 conflicts backward assigning ... to true"). It then stalls in
  preprocessing/probing on 6.8M variables and still has 0 search conflicts after 45 CPU-min (5.795M, 6.634M). So "SAT at 5.75M, stall at 5.795M"
  says nothing about whether S(5.795M) is SAT or UNSAT. It is also not evidence that the smallest UNSAT R is near here. The seed
  twins were exact duplicates (the lucky phase ignores the seed), so they were killed. Relaunched 5.7725M and 5.795M with
  `KOPTS="--lucky=false --preprocess=false --sat"` (new `probe.sh` KOPTS/KTAG env, tag suffix `cd`) to get real CDCL search.
- 2026-09-23 13:55–16:34 — **Warm-start local search** (`scripts/warmls.c`, `warmchain.sh`, `smoothfix.py`; details in WARMSTART.md)
  starting from the 5.75M kissat model. It repairs zero triples above the old bound by changing f on large primes, and moves f on a few small
  primes when 1000- or 3000-smooth triples block it. Steps take seconds to minutes. Verified bounds:
  6,000,730 · 7,000,020 · 10,000,150 · 20,000,330 · 30,000,887 · 45,000,953 · 70,005,949 · 100,009,485 · 150,005,898 · 200,011,716 ·
  300,001,271 · 400,006,178 · 500,003,685 · 700,026,741 · **1,000,007,372**. So **Λ(5,3) ≥ 1,000,007,372** (Chebotarev, k odd).
  Every bound was decoded by `lamenc run` and `checkf.py` (agent). The parent session also checked each bound from 15M on (the 1e9 bound included)
  with its own code: a prime-power accumulation checker up to 5e8 and `scripts/verify_pp.py` (segmented, 500M/700M/1e9). The 1e9 witness is
  superseded by the 2e9 witness below
  Interpretation: the full-instance "threshold" was a solver artifact. Nothing in the computations so far points toward finiteness.
- 2026-09-23 — **Theory route** (THEORY.md): no finiteness certificate. "f(2)=0 forced" is false (models with f(2)=1 up to ~1e6). Tree
  estimates stay ~1e18 under every branching order: the primes ≤ 97 alone leave ~2e14 consistent assignments. The F_5 Nullstellensatz route
  looks like a dead end at this scale. Best idea: a conditional reduction to three-point logarithmic Elliott correlations.
- 2026-09-23 16:50 — **Λ(5,3) ≥ 2,000,028,671.** Checks: agent's `segcheck.c` + `checkf.py`, and the parent's
  `scripts/verify_pp.py` (1.5e9: 1,500,097,130 ✓; 2e9: 2,000,028,671 ✓, 377 s). Witness `logs/warmstart/k5l3_first2000028671.{map,model}.gz`,
  SHA-256 of the uncompressed files: map 85e3c19a…, model 1bfef1c5… Method: WARMSTART.md. Every stall above 1.5e8 was a triple of 3000-smooth
  numbers. These were resolved by re-solving f on primes ≤ 3000 against all smooth triples up to X (`smoothfix.py`). **Open computational question for
  finiteness:** is F_y(∞) satisfiable for every y? A single UNSAT y proves Λ(5,3) < ∞. Local search cannot give an upper bound.
- 2026-09-23 17:50 (corrected 18:45) — **F_100(∞) is satisfiable.** Luca–Najman (Math. Comp. 80 (2011), doi:10.1090/S0025-5718-2010-02381-6,
  Corollary 6) give the largest x with P(x(x+1)…(x+n)) < 100. For n = 2 (triples) it is **x = 407,498,958** (checked: largest prime factors 83, 41, 89).
  The row x = 97,524 is n = 3, i.e. runs of four (matches OEIS A193945). An earlier version of this note misread it as the triple bound.
  Their erratum (Math. Comp. 83 (2014) 337, doi:10.1090/S0025-5718-2013-02696-8; copy in novelty_sources/) adds 56 missed solutions of
  P(x²−1) < 100 and states that the other numerical results are unchanged. Checked here: exactly one missed x is itself 100-smooth, x = 43,184,401,
  giving the triple 43,184,400 = 2⁴·3·5²·7·53·97, 43,184,401 = 13²·59·61·71, 43,184,402 = 2·37·79·83·89. It lies below 407,498,958, so the
  maximum stands. The 2e9 witness restricted to primes ≤ 100 avoids zeros on all triples up to 2e9 ⊇ all 100-smooth triples, so F_100(∞) is SAT.
  This assumes the corrected Luca–Najman list is complete (Conrey–Holmstrom–McLaughlin's independent computation is what led to the erratum).
  Consequence: a finiteness certificate via F_y(∞) needs y well above 100. Complete smooth-triple lists at that size need ~2^π(y) Pell equations
  (y ≈ 500: ~2^95), which is infeasible.
- References (DOIs checked on Crossref): Tschebotareff, Math. Ann. 95 (1926) 191–228, doi:10.1007/BF01206606 (GDZ scan in
  novelty_sources/); Neukirch, ANT, doi:10.1007/978-3-662-03983-0; Lang, Algebra, doi:10.1007/978-1-4613-0041-0; LLMS 1962,
  doi:10.1090/S0025-5718-1962-0162379-2; Conrey–Holmstrom–McLaughlin, "Smooth neighbors", Exp. Math. (2013), doi:10.1080/10586458.2013.768483.

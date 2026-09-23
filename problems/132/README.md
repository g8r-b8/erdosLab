# Erdős Problem #132: two distances occurring at most n times

**Status (ours):** all 5 angles reported 2026-09-22. Partial results only; novelty NOT yet
checked against sibling problems/threads (see PROMPT.md rule 4 — lesson from #468).
**Prize:** $100 for "any nontrivial result" (Erdős, [Er97e]).
**Site status:** OPEN.

## Statement
A ⊂ ℝ², |A| = n. Must there be two distances that each occur at least once and between at most
n pairs? Must the number of such distances → ∞ (perhaps ≥ n^{1−o(1)})?

## Prior work (initial; full map in `frontier.md` from the literature agent)
- Hopf–Pannowitz 1934: the diameter occurs ≤ n times.
- False for n = 4 (two equilateral triangles glued). Erdős–Fishburn [ErFi95]: true for n = 5, 6.
- Clemen–Dumitrescu–Liu, arXiv 2505.04283 (2025):
  - Thm 1.2: true for convex position.
  - Thm 1.3: Δ₂ (second-largest distance) occurs ≤ n times if
    min{3/2(|L₁|+|L₂|), 4/3|L₁|+2|L₂|, 2|L₁|+|L₂|} ≤ n (L₁, L₂ the first two convex layers).
  - Problem 1.6: limsup min{μ(Δ₂), μ(δ)}/n = ?  (δ = minimum distance.)
- Forum: ienjoymath, lower bound 9/7 for Problem 1.6 (upper 3/2). Proof claims for small n
  (Beller n=8, Lean but conditional; Marche 7–13; Chojecki n=8, flawed per ienjoymath).

## Frontier summary (literature agent, 2026-09-22 — details in `frontier.md`)
- No refereed progress beyond CDL; 0 citations of CDL. No statement by Bloom about what counts
  for the prize; only Erdős's "any nontrivial result". Prize requires journal publication.
- Small n: Rafik n=7 (+ n=8 reduced), Marchetto 7≤n≤13 (11,12 rely on Wei 2011), Beller n=8
  (Lean, conditional). n=14 needs classification of 14-pt 7-distance sets (unknown).
- Problem 1.6: lower 9/7 − 5√n/n (ienjoymath, 25 Jul 2026, conjectured optimal), upper 3/2.
- Ranked open sub-questions: (1) count of ≤n distances → ∞ (or ≥3) for CONVEX sets — reduces to
  stability of Altman/Fishburn: D = ⌊n/2⌋+K gives s ≥ K+1; (2) widen not-too-convex class;
  (3) full two-distance for n ≥ n₀ via Vesztergombi rigidity; (4) 1.6 upper < 3/2;
  (5) n ≥ 14 computational; (6) n^{1−o(1)} — out of reach.
- Key tools: Vesztergombi 1985/87/96 (Δ₂ ≤ 3n/2 general, 4n/3 convex, m_k ≤ kn convex,
  m₁+m₂ ≤ 2n convex), Morić–Pritchard levels lemma, Altman, Fishburn, Harborth penny bound,
  Dumitrescu μ(δ)μ(Δ) ≤ 9n²/8+O(n).

## Attack angles (agents)
- A: Problem 1.6 upper bound < 3/2  → `angle_A.md` (DONE, conditional/partial)
  - Theorem A (rigorous modulo CDL's Vesztergombi Props 1–8 as black boxes): if Δ ≤ (2−κ)Δ₂ and
    t = Δ−Δ₂ ∉ (√3/2 − 2β, 1]·δ, then min{μ(Δ₂), μ(δ)} ≤ 16n/11 + C.
    Via LP (multipliers 10/33, 15/33, 8/33) + "Ring Lemma" e_δ(S) ≤ |S| + C.
  - Open window √3/2 < t/δ ≤ 1: Ring Lemma FALSE there (rhombic strip, avg degree 3 = the 3/2
    barrier); would need weighted bound e(S) ≤ |S∖P| + α|P|, α<3. Also degenerate Δ > (2−κ)Δ₂.
  - Some steps (lens-corner) sketched without explicit constants. 32/23 for t>1 sketched.
- B: convex position, count of ≤n distances → ∞  → `angle_B.md` (DONE, partial)
  - Proved: counting k ≥ D − ⌊n/2⌋ + 1 (convex); slack versions (≥ ~n/2 distances occur ≤ λn times
    for λ>1); cocircular / max-equidistance-degree-2 ⇒ k = D ≥ ⌊n/2⌋.
  - NEW Cap Lemma: regular a-gon (a ≥ 6) + one point q in strictly convex position ⇒ any chord
    distance |q−x| is the longest (or one of two longest) chords. (Exact check a < 600.)
  - NEW Theorem E: convex n-set containing a regular a-gon (a ≥ 6) has k ≥ a − (n+1)/2.
  - Open: stability of Altman (D ≤ ⌊n/2⌋+K ⇒ all but f(K) points on one regular N-gon,
    N ≤ n+f(K)); Fishburn = K=0. Naive "contains regular (n−f(K))-gon" is FALSE.
    Plus extended Cap Lemma for gapped vertex subsets. Together ⇒ k ≥ n/2 − O_K(1).
  - Elementary; agent judges not prize-worthy alone. Next: stability for K = 1.
- C: new classes beyond Thm 1.2/1.3  → `angle_C.md` (DONE, partial)
  - Reformulation: CDL's 2|L1|+|L2| ≤ n ⇔ |L1| ≤ m₃ (#points at depth ≥ 3).
  - Theorem A: μ(Δ₂) ≤ |L1|+|L2| + ½Σ_{p∈L1'}(deg_{G'}(p)−2) (G' = 2-core of Δ₂-graph; uses
    Vesztergombi Prop 3 as cited by CDL).
  - NEW Cor A1: if no hull vertex has 4 points at distance Δ₂ (e.g. no 4 concyclic) then
    μ(Δ₂) ≤ (3/2)|L1|+|L2|, so the conjecture holds when |L1| ≤ 2m₃. Sharp; beats CDL e.g. at
    |L1|=|L2|=0.4n.
  - Lemma T: |ab|=|cd|=Δ, |ac|=|bd|=Δ₂ ⇒ a,b,c,d concyclic (extremal cores need concyclic quads).
  - B1–B4 via counting lemma s' ≥ (n+1)(2D−n)/(2n): line with ≥⌊n/2⌋+2 pts; a point seeing
    ≥⌊n/2⌋+1 distances; few isosceles triangles; B2 via Pach–de Zeeuw for points on algebraic
    curves (≥ C_d n^{3/4} points on a curve ⇒ s' ≥ n/2).
  - Negative: N1 triangle-free δ-graph still gives μ(Δ₂), μ(δ) ≈ 6n/5; N2 general position
    doesn't force μ(Δ₂) ≤ n (n=6, μ(Δ₂)=7).
  - Conjecture C1: no 4 concyclic ⇒ μ(Δ₂) ≤ n + O(1). Unproved.
  - Checks were floating point (1e-9), not exact.
- D: adversarial constructions / computation  → `angle_D.md` (DONE; code in `scripts/`)
  - No counterexample for n ≥ 5 (lattices Z[ω], Z[i], cyclotomic pools, n ≤ 60). Max of
    min non-diameter multiplicity M(X) equals n exactly, attained by the regular n-gon (and a
    sporadic 12-pt lattice set). Refined conjecture: M(X) ≤ n, equality only for R_n + sporadics.
  - # rare (≤n) distances min found: 2 (n=5–7, also an n=8 Z[ζ₁₂] patch), 3 (8–16), 5 (20),
    7 (30), 12 (40) — consistent with → ∞.
  - Problem 1.6: nothing beats 9/7. Key reduction: 9/7 ⇔ μ(δ) + (4/3)μ(Δ₂) ≤ 3n + o(n);
    ienjoymath's even-m ring is tight (= 3n exactly). Heuristic proof via Δ₂-points on thin
    convex curve + Euler face-length deficit of the min-distance graph (2 per Δ₂ point).
- E: literature and claim audit  → `frontier.md` (DONE)

## Follow-up (2026-09-23)
- A2 → `angle_A2.md`: unconditional (54/37)n + C₀ for CDL Problem 1.6 (beats 3/2; lower bound 9/7).
  Referee `REFEREE_A2.md`: CORRECT WITH FIXABLE GAPS (symmetric R2, (c2) angle bound, KK constant,
  Vesztergombi citation, lens-corner length). Not yet novelty-audited.
- A1 check → `VERIFY_A1.md`: Cor A1 holds, conditional on Vesztergombi Prop 3 (same dependence as CDL).
- B2 → `angle_B2.md`: convex even n ≥ 6 has ≥ 3 rare distances (Thm A, via Fishburn); convex n = 9 too
  (Thm B); odd n reduces to one configuration (Prop B, C1–C5); Kneser cocircular stability (Lemma K).
- B2 check → `VERIFY_B2.md`: all proved items VERIFIED; small gaps (Fishburn original, Cap Lemma on-circle
  case, Theorem D step 2).

## Iteration 8 (2026-09-23): 3 agents running
- Novelty audit of A2 + B2 Thm A → NOVELTY.md "Audit 2" — DONE (b8bb2ec): 54/37 NEW (still 3/2 everywhere);
  B2 Thm A NEW as a statement but a parity-sharpened CDL Thm 1.2, so present it as a corollary. Risks: ienjoymath's
  announced "LP analysis" note, which hasn't appeared yet (re-check before posting), and paywalled Erdős–Fishburn 1995 / Fishburn papers
  that might cover convex n=6.
  RESOLVED (Audit 3 in NOVELTY.md): r₂ ≤ n for convex n ≤ 8 [EF95b §3] ⇒ convex n=6,7,8 have ≥3 rare distances
  from published results; B2 Thm A new only for even n ≥ 10, Thm B (n=9) unaffected.
  (was) TODO (user): save these PDFs into novelty_sources/. ScienceDirect blocks automated access from
  here; the papers are likely in Elsevier's free open archive, so use a normal browser:
  Erdős–Fishburn DAM 60 (1995) 141–147 https://www.sciencedirect.com/science/article/pii/0166218X9400046G ;
  Erdős–Fishburn "Intervertex distances in convex polygons" DAM 60 https://www.sciencedirect.com/science/article/pii/0166218X9400047H ;
  Fishburn "Convex polygons with few intervertex distances" CGTA 5 (1995) 65–93 https://www.sciencedirect.com/science/article/pii/092577219400020V
- Referee gaps closed → WRITEUP_A2.md + scripts/writeup_a2_checks.py — DONE (e76d1a7): all gaps closed, 58 exact
  interval checks pass, ~90% confidence; weakest spots §7.2 pairing and §8 Step 4. Referee's citation complaint was
  wrong (CDL [23] = Ve87). Second independent referee (REFEREE2_A2.md, 5b87a82): CORRECT — §7.2 exhaustively
  checked (max exactly 4/3), §8 Step 4 adversarially tight (max μ(Δ₂)−n = 0), assembly exact. Ve87's 3n/2 corroborated
  by Pach's Handbook ch. 1; original READ (NOVELTY Audit 5): n₂ ≤ (3/2)n exactly, for all n, with no constant. 54/37 now has no unread dependencies.
  Cor A1 now UNCONDITIONAL (VERIFY_A1b.md): Prop 3 proved directly from Ve87 Cases 1–3 applied in the 2-core
  (no point deletion). All cases now exact (sympy + hand proofs + interval check, va1b_exact.py).
  Unconditional min(h,4) form also PROVED (VERIFY_A1c.md, 007b648): deg_{G′}(p) ≤ 4 on L₁′ via Lemma M/F
  (a short exact proof; no point deletion), with sympy identities + ~3.2M exact lattice configs + ~81k sets, 0 violations.
  Side effect: the Vesztergombi inputs to CDL Thm 1.3 are now independently proved.
- Convex n = 7 (and maybe 11) → angle_B3.md — DONE (f8b09f7). Convex n = 7 ⇒ k ≥ 3 (k = number of rare distances), proved two ways: from the literature
  ([EF95b] r₂ ≤ n plus Altman), and self-contained. **n = 11 ⇒ k ≥ 3: NEW, computer-assisted** — a SAT refutation of ordinal
  distance-rank colourings under the convex-quadrilateral inequality only, with the DRUP proof checked by our own RUP checker.
  n = 13: now fully certified (drat-trim + lrat-check, incl. (13,7,5)). n = 15: hard case unresolved.
  Conjecture Q-ORD: for n ≥ 7, the ordinal quadrilateral inequality alone forces k ≥ 3.
  Why it matters for PROMPT.md's Lean goal: the n = 11 statement is purely finite, so it is a candidate
  for a Lean-verified certificate (LRAT via Lean's bv_decide/LRAT checker), plus a small Lean lemma deriving the ordinal
  constraints from geometry (diagonals of a convex quadrilateral beat the opposite sides).

## Next steps
0. B3: n=7,11,13 certified by drat-trim + lrat-check (DONE). Lean: convex n=7 and n=11 sorry-free in
   Erdos/Erdos/E132Convex.lean (Lemma Q, ordinal reduction and BitVec encoding proved in Lean; the core is closed by bv_decide.
   Axioms: std 3 + one bv_decide certificate axiom each, to be disclosed like native_decide). Remaining: unordered-Finset form
   (angular-sort lemma), n=13 in Lean, LRAT replay via bv_check, add the file to Erdos.lean. See lean/README.md.
1. Rule-4 novelty audit of the 54/37 bound (A2) and B2 Theorem A.
2. Close the REFEREE_A2 gaps → write-up of 54/37 (the strongest "nontrivial result" candidate for the prize).
3. n = 7 convex k ≥ 3 by exact classification of 7-point convex 4-distance sets.

# Erdős Problem #132: two distances occurring at most n times

**Status (ours):** IN PROGRESS. Five parallel agents launched 2026-09-22.
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
- A: Problem 1.6 upper bound < 3/2  → `angle_A.md`
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

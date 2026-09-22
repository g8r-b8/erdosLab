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
- B: convex position, count of ≤n distances → ∞  → `angle_B.md`
- C: new classes beyond Thm 1.2/1.3  → `angle_C.md`
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

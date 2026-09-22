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

## Attack angles (agents)
- A: Problem 1.6 upper bound < 3/2  → `angle_A.md`
- B: convex position, count of ≤n distances → ∞  → `angle_B.md`
- C: new classes beyond Thm 1.2/1.3  → `angle_C.md`
- D: adversarial constructions / computation  → `angle_D.md`
- E: literature and claim audit  → `frontier.md`

# Erdős #132: adversarial check of angle_C.md (Theorem A, Cor A1, Lemma T, B1–B4, N1, N2)

Date: 2026-09-23. Scripts (new, all in `scripts/`): `va1_common.py`, `va1_clique.py`, `va1_cyclo.py`, `va1_sharp.py`.

## Summary

| Claim | Verdict |
|---|---|
| Thm A step 1 (all Δ₂ pairs in L₁∪L₂; depth ≥ 3 has no Δ₂ partner) | VERIFIED. I re-proved it (see below). |
| Thm A step 2 (pruning; how pruned vertices are counted) | VERIFIED |
| Thm A step 3 ([Ve96, Prop 3]: every L₂' vertex has degree exactly 2 in G') | GAP (citation only). I could not get Ve96 or prove Prop 3 myself. Exhaustive searches over lattice and cyclotomic pools found no counterexample. The dependence is the same as CDL's. |
| Theorem A (as a whole) | VERIFIED conditional on Prop 3. The algebra is correct. |
| Corollary A1 | VERIFIED conditional on Prop 3. The degree cap is sound, and no counterexample was found. |
| "No 4 concyclic ⇒ (H3)" | VERIFIED |
| Unconditional form | VERIFIED conditional on Prop 3 and Props 5–8 (Props 5–8 are needed only for the min(·,4)). |
| "Why new" arithmetic | VERIFIED |
| Sharpness example | VERIFIED numerically for m = 6, 8, …, 20. It is tight for A1 and for Thm A. |
| Lemma T | VERIFIED. The degenerate cases the proof omits are closed below. |
| Lemma B, B1, B2, B3, B4(i), B4(ii) | VERIFIED. There are small wording caveats. |
| N1 | VERIFIED numerically (n = 264). Its parametrisation is loosely stated. |
| N2 | VERIFIED numerically (n = 6, μ(Δ₂) = 7, H3 holds, no collinear triples, no concyclic quadruples). The phrase "capped at n = 6" was not checked. |

No claim was found FALSE.

## (a) Degree cap in Corollary A1

- G' is a subgraph of the Δ₂-graph on X. So deg_{G'}(p) ≤ h(p) := #{x ∈ X : |px| = Δ₂}.
- (H3) says h(p) ≤ 3 for every hull vertex p.
- In the 2-core, deg' ≥ 2. So deg'(p) − 2 ∈ {0, 1} on L₁'.
- Therefore ½Σ_{L₁'}(deg' − 2) = ½·#{deg' = 3} ≤ ½|L₁|. **Sound.**
- (H3) counts partners in all of X. That is the right quantity: by step 1, partners never lie at depth ≥ 3 anyway.
- If four points of X lie on the circle of radius Δ₂ about p, they are concyclic. So "no 4 concyclic ⇒ (H3)" holds.
- Equivalence check: (3/2)|L₁| + |L₂| ≤ n ⇔ |L₁| ≤ 2m₃.
- The bold sentence "Δ₂ occurs at most n times whenever |L₁| ≤ 2m₃" holds **only under (H3)**. The file places it inside the corollary, but it reads as if it were unconditional. The wording should be tightened.

## (b) Pruning and accounting

- G has vertex set L₁ ∪ L₂, including isolated vertices.
- Deleting a vertex of current degree 0 or 1 removes at most one edge. So e(G) ≤ e(G') + |V(G) \ V(G')|. This is CDL's inequality verbatim.
- Adding e(G') = |V(G')| + ½Σ_{L₁'}(deg' − 2) gives |V(G)| + ½Σ = |L₁| + |L₂| + ½Σ.
  - Every pruned vertex is counted once in |L₁| + |L₂|.
  - Surviving vertices are counted in |V(G')|.
- Points of depth ≥ 3 carry no Δ₂-edges. Self-contained proof:
  - If |pq| = Δ, then X ⊂ D(q, Δ) with p on its boundary circle. So p is an extreme point, and p ∈ L₁.
  - If |pq| = Δ₂ and p ∉ L₁, then p has no Δ-partner. So X ⊂ D(p, Δ₂), q lies on its boundary circle, and q ∈ L₁. Hence every Δ₂-edge has an L₁ endpoint.
  - If p ∈ L₁, then every point outside the circle C(p, Δ₂) is a Δ-partner of p, so it lies in L₁. Then q is extreme in X \ L₁, so q ∈ L₂. This is CDL obs. (2).
- The exact checker (`va1_common.analyze`) tests obs. (1)–(3) on every set searched. There were 0 violations.

## (c) Use of the CDL/Vesztergombi propositions

- Theorem A uses only obs. (1), (2) and (4), i.e. Prop 3. That is a **subset** of what CDL's proof of Thm 1.3 uses: CDL need (4) for e(L₁', L₂') = 2|L₂'|. Theorem A does not use Props 5–8 at all.
- G, G' and the pruning are exactly CDL's objects: the Δ₂-graph on L₁∪L₂, with vertices of degree < 2 removed iteratively. So Prop 3 is used within CDL's own reading of the hypotheses.
- **Residual gap.**
  - I could not obtain Vesztergombi 1985/1987/1996. The ScienceDirect PDFs return 403 or a Cloudflare block, and I found no preprint copy.
  - So I cannot confirm that [Ve96, Prop 3] is stated for this exact 2-core (and not for some differently reduced graph).
  - Theorem A and A1 are therefore exactly as reliable as CDL Thm 1.3's second and third bounds. That is fixable only by reading Ve96 or by re-proving Prop 3.
- The degree is exactly 2 in G' only, not in G.
  - A point q ∈ L₂ can have deg_G(q) = 3.
  - Example: an equilateral triangle of side Δ with its centre, so Δ₂ = Δ/√3.
  - Another example: partners at angles 0°, 160°, 200° in Z[ζ₁₈].
  - In every such case found, the third partner is pruned. The pruning in Theorem A is essential, and the file uses it correctly.

### Counterexample search for Prop 3, Thm A and A1 (`va1_clique.py`, `va1_cyclo.py`)

Reduction:
- If q ∉ L₁, then X ⊂ D(q, r) with r = Δ₂.
- Every pair in X has distance ≤ r or = Δ.
- So candidate sets are cliques of a compatibility graph on pool ∩ D(q, r).
- The target property (q not a hull vertex and deg_{G'}(q) ≥ 3) is monotone under adding compatible points. So checking all maximal cliques (Bron–Kerbosch) is exhaustive within the pool.

Each clique was also run through the full checker: Prop 3, Props 5–8, obs. (1)–(3), Thm A, A1, the unconditional form, CDL Thm 1.3, and 3n/2.

Pools searched:
- **Exact integer arithmetic:**
  - Z[ω]: every r² ≤ 49 and every Δ² ∈ (r², 4r²]. The job was stopped partway through r² = 49.
  - Z[i]: every r² ≤ 58. The job was stopped partway through r² = 58.
- **Float with 1e-8 quantisation:** Z[ζ_N], sums of ≤ 3 roots of unity, for N = 5, 7, 8, 9, 10, 12, 14, 18 (N = 16, 20, 24 were run partially and stopped, with no violation seen so far). Also r ≤ 2 for N = 12, and weight 4 for N = 6 and N = 8.

Results:
- More than 800,000 maximal sets were checked, counting both lattice and cyclotomic pools, with **0 violations of any claim**.
- Hundreds of sets have an interior q with deg_G(q) = 3. None has deg_{G'}(q) = 3.
- When q is surrounded, with angular gaps (θ, θ, 360° − 2θ) and θ ≥ 150° or θ = 120°, the maximal compatible sets are tiny (n = 4), or the triangle's third vertex is pruned.
- I also showed by hand that the 60°-rhombus configuration (partners at 0°, 60°, 120°) cannot have q interior. The middle partner has no admissible Δ-partner.

## (d) Sharpness example (`va1_sharp.py`)

Construction: a regular even m-gon with servers on alternate edges.

For m = 6, 8, 10, 12, 14, 16, 20:
- Every hull vertex has h = 3.
- Every L₂' vertex has core degree 2.
- μ(Δ₂) = 2m = Thm A bound = A1 bound = 1.5|L₁| + |L₂|.
- CDL gives 2.25m.

The gap from Δ₂ to the next distance is at least 1.2e-2, so float error cannot matter. The equalities are exact by construction, from the polygon's symmetry and the definition of the servers. The file lists m = 8, 12, 16; m = 6 and all other even m ≥ 6 in the range also work.

As the file says, the example shows only "sharp under (H3)". It has 95 concyclic quadruples at m = 8, so it says nothing about C1 (the no-4-concyclic version).

## (e) Lemma T

- The isometries swapping b and c are exactly the half-turn about the midpoint of bc and the reflection in its perpendicular bisector.
- **Half-turn case:** the parallelogram law gives |ad|² + |bc|² = 2Δ² + 2Δ₂² > 2Δ², so one diagonal exceeds Δ. Correct.
- **Reflection case:** the proof omits two degenerate cases. Both are impossible:
  - (i) a on the axis, so d = a. Then |ab| = |ac|, which contradicts Δ ≠ Δ₂.
  - (ii) all four points collinear. With b = −t, c = t, a = s and d = −s, we get s + t = Δ and |s − t| = Δ₂. Then |ad| or |bc| equals Δ + Δ₂ > Δ.
- So a, b, c, d form a genuine isosceles trapezoid or rectangle, which is concyclic. **VERIFIED.**

## (f) Lemma B and B1–B4

- **Lemma B:** C(n,2) ≥ 1 + s' + (D − 1 − s')(n + 1) ⇒ n·s' ≥ (n + 1)(D − n/2). Correct. D ≥ ⌊n/2⌋ + 1 gives 2D − n ≥ 1, so s' ≥ 1.
- **B1:** k collinear points give at least k − 1 distinct distances.
- **B3:** immediate from D ≥ the number of distances seen from p.
- **B2:** Pach–de Zeeuw (arXiv 1308.0177) is stated for a degree-d curve containing no line and no circle. Irreducibility is not needed. With D ≥ c_d·k^{4/3} ≥ n, Lemma B gives s' ≥ D/2.
  - The result is only meaningful for large n, since C_d·n^{3/4} ≤ n is required.
  - Condition "(b)" is not defined anywhere in angle_C.md.
- **B4(i):**
  - Σ deg = 2μ ≥ 2n + 2 over n vertices gives Σ C(d, 2) ≥ (n − 2)·1 + 2·3 = n + 4. Correct.
  - Wording caveat: the count is of apex-counted triples (p; x, y) with |px| = |py| = r. It includes collinear triples where p is the midpoint of xy, and it counts equilateral triangles 3 times.
- **B4(ii):**
  - By Hopf–Pannwitz, μ(Δ) ≤ n, so Σ_{r≠Δ} μ(r) ≥ n(n − 3)/2.
  - Real Jensen gives Σ_p C(d_p, 2) ≥ e(2e − n)/n ≥ e(n + 2)/n when e ≥ n + 1.
  - The sum is therefore at least (n + 2)(n − 3)/2. Correct, with the same wording caveat as B4(i).

## N1, N2

- **N1:** `tf_construct.py 100 8` gives n = 264, μ(Δ₂) = 300, μ(δ) = 312 and 0 δ-triangles. I also checked separately that the δ-graph is bipartite; the margin to the next distance is 0.013.
  - Note that n = 264 uses m = 100 and a 64-point patch, not m = 2n/5 and a patch of n/5. The "6n/5" figure is asymptotic.
- **N2:** I reconstructed the family (rhombus with side 1 and Δ = √3, plus e ∈ C(a, 1) and f ∈ C(b, 1)).
  - It gives n = 6 and μ(Δ₂) = 7, with 0 collinear triples and 0 concyclic quadruples.
  - (H3) holds, and μ(Δ₂) = 7 = Thm A bound < A1 bound 8. This is consistent with both.
  - The claim "capped at n = 6 under (H3)" is vague, and I did not check it.

## What would close the gap

Either obtain Ve96 and check that the statement and hypotheses of Prop 3 match CDL's 2-core, or prove Prop 3 directly. Useful facts for a direct proof:
- Normalise q = 0 and Δ₂ = 1. Then X lies in the unit disk and all distances are in [0,1] ∪ {Δ}.
- Every x ∈ X \ {q} with x·p ≤ 0 is a Δ-partner of p, for each partner p of q.
- q's partners either lie in an arc of at most 60°, or two of them are at angle θ_Δ, where θ_Δ is the angle subtending a chord of length Δ.

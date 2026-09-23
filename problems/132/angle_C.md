# Erdős #132, angle C: making the class of proved point sets larger

Date: 2026-09-22. Scripts are in `scratchpad/p132/angleC/`.

## Notation

- X ⊂ R², |X| = n.
- Δ > Δ₂ are the two largest distances. δ is the smallest distance.
- μ(r) is the multiplicity of distance r. D = D(X) is the number of distinct distances.
- L₁, L₂ are the first two convex layers. m₃ := n − |L₁| − |L₂| is the number of points of depth ≥ 3.
- s'(X) := #{r ≠ Δ : 1 ≤ μ(r) ≤ n}. Conjecture (a) says s' ≥ 1 for n ≥ 5.
- G is the Δ₂-graph on L₁ ∪ L₂. G' = L₁' ∪ L₂' is its 2-core (repeatedly delete vertices of degree < 2).

A reformulation that is useful: CDL's condition 2|L₁| + |L₂| ≤ n is the same as **|L₁| ≤ m₃**. So "mostly interior" sets, in the sense of having at least as many points of depth ≥ 3 as hull vertices, are already covered by CDL Theorem 1.3.

---

## Theorem A: layer bound with explicit degree excess (rigorous, given Vesztergombi's facts)

**Theorem A.** For every finite X,

  μ(Δ₂) ≤ |L₁| + |L₂| + ½ Σ_{p∈L₁'} (deg_{G'}(p) − 2).

**Proof.**
1. All Δ₂-pairs lie in L₁ ∪ L₂ (CDL observations (1) and (2)).
2. Each deletion made while pruning to the 2-core removes at most one edge. So e(G) ≤ e(G') + |V(G) \ V(G')|.
3. Every q ∈ L₂' has degree exactly 2 in G' ([Ve96, Prop 3] per CDL obs. (4); now proved directly in VERIFY_A1b.md from Ve87's inner-point argument). Hence
   e(G') = ½ Σ_{v∈G'} deg' = |V(G')| + ½ Σ_{p∈L₁'} (deg'(p) − 2).
4. Adding the two estimates gives the bound. ∎

Using deg' ≤ 4 on L₁' ([Ve96, Props 5–8]; now proved directly in VERIFY_A1c.md) recovers CDL's bound 2|L₁| + |L₂|.

**Corollary A1 (new class).** Assume hypothesis (H3): no hull vertex has 4 or more points of X at distance Δ₂. This holds in particular when **no four points of X are concyclic**. Then
  μ(Δ₂) ≤ |L₁| + |L₂| + ½·#{p ∈ L₁' : deg'(p) = 3} ≤ (3/2)|L₁| + |L₂|.
So Δ₂ occurs at most n times whenever **|L₁| ≤ 2m₃**, i.e. (3/2)|L₁| + |L₂| ≤ n.

**Why this is new.** Take |L₁| = |L₂| = 0.4n and m₃ = 0.2n. CDL's three quantities are 1.2n, 1.33n and 1.2n, all larger than n, so CDL does not apply. Corollary A1 gives exactly n.

**Unconditional form (proved; VERIFY_A1c.md, 2026-09-23).** Let h(p) be the number of points at distance Δ₂ from p. The conjecture holds whenever
  Σ_{p∈L₁} (min(h(p), 4) − 2)⁺ ≤ 2m₃.
The input deg' ≤ 4 on L₁' ([Ve96, Props 5–8] via CDL) is now proved directly in the 2-core, without deleting points. If p is extreme with Δ₂-neighbours w₁, …, w_k in angular order, then deg_G(wᵢ) = 1 for 3 ≤ i ≤ k − 2. Also, at most 2 of p's G'-neighbours are non-extreme.

**Sharpness (numerically verified with `checkA.py`).** Take a regular even m-gon and put CDL "servers" on alternate edges.
- Every vertex has 3 Δ₂-neighbours, so (H3) holds.
- n = 3m/2 and μ(Δ₂) = 2m = |L₁| + |L₂| + |L₁|/2. For m = 8, 12, 16 this gives 16, 24, 32, where CDL gives 18, 27, 36.
- So A1 is best possible under (H3) alone.
- However, this configuration is **forced** to contain concyclic quadruples, by Lemma T below.

## Lemma T: alternating 4-cycles force concyclicity (rigorous)

**Lemma T.** Suppose |ab| = |cd| = Δ and |ac| = |bd| = Δ₂. Then a, b, c, d are concyclic.

**Proof.**
- Triangles abc and dcb are congruent (SSS). So d is the image of a under either the reflection in the perpendicular bisector of bc, or the half-turn about the midpoint of bc.
- In the half-turn case, a + d = b + c, so abdc is a parallelogram. Its diagonals then satisfy |ad|² + |bc|² = 2(Δ² + Δ₂²) > 2Δ², which is impossible because no distance exceeds Δ.
- So the reflection case holds, abdc is an isosceles trapezoid, and an isosceles trapezoid is concyclic. ∎

Consequences:
- The CDL, Vesztergombi and ienjoymath extremal cores (a Δ-cycle interleaved with a Δ₂-cycle) all contain such 4-cycles. For example, in the even case i, i+h, i+1, i+1+h is one. So these cores are non-generic.
- Numerically, every deformation we solved for kept these concyclic quadruples (`gp_delta2.py`, `gp2.py`).

## Theorem B: counting criterion and its consequences (rigorous; B2 relies on a cited theorem)

**Lemma B.** s' ≥ (n+1)(2D − n)/(2n). In particular, D ≥ ⌊n/2⌋ + 1 implies (a).

**Proof.** C(n,2) ≥ 1 + s' + (D − 1 − s')(n+1). Rearrange. ∎

CDL use the bare case of this implicitly in the proof of their Theorem 1.2. Since D(X) ≥ D(Y) for every Y ⊆ X, any distinct-distance theorem for a subset Y gives a corollary:

- **B1.** If some line contains ≥ ⌊n/2⌋ + 2 points of X, then (a) holds.
- **B2 (Pach–de Zeeuw).** Let γ be an algebraic curve of degree d that contains no line and no circle. If |X ∩ γ| = k ≥ C_d n^{3/4}, then s' ≥ (c_d/2)k^{4/3} ≥ n/2. The other points of X are arbitrary.
  - So (a) holds, and so does the strong form of (b) (s' ≥ n^{1−o(1)}).
  - If X ⊂ γ, then s' = Ω(n^{4/3}).
  - This is not covered by CDL. Points on a cubic can have many hull vertices, and the remaining points of X are unrestricted.
- **B3.** If some point p ∈ X sees at least ⌊n/2⌋ + 1 distinct distances, then (a) holds.
- **B4 (isosceles criterion).**
  - (i) A realized distance r with at most n + 3 isosceles triangles whose legs have length r satisfies μ(r) ≤ n. Reason: μ ≥ n+1 forces Σ_p C(deg_r(p), 2) ≥ n + 4.
  - (ii) If X spans fewer than (n+2)(n−3)/2 apex-counted isosceles triangles, then (a) holds. This follows from Jensen's inequality applied to each G_r.

## Negative results (numerically verified constructions)

**N1. Neither a triangle-free nor a bipartite δ-graph makes Δ₂ or δ rare** (`tf_construct.py`).
- Construction:
  - L₁ is a regular m-gon with m even.
  - One server per edge, placed on the bisector of v_i v_{i+1} at distance Δ₂ from both. Each server lands at distance g ≈ s/2 from the two endpoints of the antipodal edge.
  - A square-lattice patch with mesh g sits at the centre.
- The δ-graph is then an alternating 2m-cycle plus a square grid, so it is bipartite and triangle-free.
- With m = 2n/5 servers and n/5 patch points: μ(Δ₂) = 6n/5 and μ(δ) = 6n/5 − O(√n).
- Example: n = 264 gives μ(Δ₂) = 300, μ(δ) = 312, and zero δ-triangles.
- This rules out candidate (ii).

**N2. General position does not force μ(Δ₂) ≤ n** (`gp6.py`).
- Take a 60° rhombus a c b d with side 1 and Δ = √3.
- Add e on circle(a, 1) inside the lens and f on circle(b, 1) inside the lens.
- Result: n = 6, μ(Δ₂) = 7, no 3 collinear, no 4 concyclic.
- Under (H3), this lens family is capped at n = 6.

## Conjectures and gaps

- **Conjecture C1.** If no four points of X are concyclic, then μ(Δ₂) ≤ n + O(1). Stronger: #{deg-3 vertices of G'} = O(1).
  - Given the conjecture's stronger form (O(1) degree-3 core vertices), Theorem A proves (a) for general-position sets with at least a constant number of points of depth ≥ 3.
  - Lemma T is the intended tool. A proof needs Vesztergombi's case analysis redone, and I have not done it.
- **C1 evidence (iter 8, `scripts/c1_greedy.py`, floating point, tolerance 1e-9).** Greedy constructive search: Δ₂ = 1, Δ ∈ [1.02, 1.9]. New points go at unit ∩ unit, unit ∩ Δ, or random unit/Δ placements. Every candidate is rejected if it makes 4 points concyclic or creates a distance in (1, Δ). Over 7 seeds × 300 trials the best μ(Δ₂) − n was +1 (n = 8–11), dropping to ≤ 0 for n ≥ 12 and to −5 at n = 21. This is consistent with C1 but weak, because greedy search is myopic.
- Theorem A relied on [Ve96, Prop 3], cited via CDL; now proved directly (VERIFY_A1b.md, 2026-09-23), so Theorem A and Cor A1 are unconditional. B2 relies on Pach–de Zeeuw, whose constants are not explicit.
- Convex layers in the scripts are computed with scipy in floating point; the equalities were checked with tolerance 1e-9.

## Novelty evidence

- CDL (arXiv v5, Feb 2026) contains only Theorem 1.2, Theorem 1.3 and Corollary 1.4 for (a).
- The forum thread has only finite-n results (n ≤ 13) plus ienjoymath's 9/7 lower bound.
- The frontier audit found no other literature.
- None of A1, B1–B4, N1, N2 or Lemma T appears in these sources. That said, B1, B3 and B4 are one-line consequences of Lemma B.

# Degree ≤ 4 on L₁′ in the 2-core: a proof of "[Ve96, Props 5–8]" as used by the Unconditional form

Date: 2026-09-23. Scripts: `scripts/va1c_sympy.py`, `scripts/va1c_local.py`, `scripts/va1c_random.py`.

## Claim

Let G be the Δ₂-graph of X and G′ its 2-core. L₁ is the set of hull vertices (extreme points), which is the convention in `va1_common.py`, and L₁′ = L₁ ∩ V(G′).
**Then every p ∈ L₁′ has deg_{G′}(p) ≤ 4.**

This is the input that the "Unconditional form" of Cor A1 and CDL's bound 2|L₁| + |L₂| cite as [Ve96, Props 5–8]. The proof below is self-contained. Like VERIFY_A1b, it deletes no points. Every witness stays in X, and the contradictions are with 2-core membership via deg_G ≥ deg_{G′}.

## Setup and two facts

Normalise Δ₂ = 1. Every distance in X is either ≤ 1 or equal to Δ.
- **Prop 1.** A Δ-pair has both endpoints extreme.
- **Half-plane fact.** Take p extreme. Some line through p has X \ {p} strictly on one side. So p's Δ₂-neighbours w₁, …, w_k have distinct directions inside an open half-plane. Order them by angle. Any two directions differ by less than 180°. For j < i < l, the points w_j and w_l lie strictly on opposite sides of the line pwᵢ.

**Lemma M (opposite-side lemma).** Suppose |pa| = |pb| = |br| = 1 and r ≠ p. Suppose also that a lies strictly on one side of the line pb and r does not lie strictly on that side. Then |ar| > 1, so |ar| = Δ.

*Proof.* Put p = 0, b = (1, 0), a = (cos A, −sin A) with 0 < A < π, and r = b + (cos F, sin F) with 0 ≤ F < π. Here F ≠ π because r ≠ p. Then
  |r − a|² − 1 = 2(1 + cos F)(1 − cos A) + 2 sin F sin A.
The first term is > 0 and the second is ≥ 0. (The identity is checked symbolically in `va1c_sympy.py`.) ∎

## Lemma F (the core step; this is Ve87 Prop 8 for total degree)

Let p be extreme with Δ₂-neighbours w₁, …, w_k in angular order. **Then deg_G(wᵢ) = 1 for every 3 ≤ i ≤ k − 2.**

*Proof.*
1. Suppose r ≠ p and |rwᵢ| = 1. Put p = 0 and wᵢ = (1, 0). Then w_{i−2} and w_{i−1} lie strictly below the x-axis, and w_{i+1} and w_{i+2} lie strictly above it. By symmetry, assume r is not strictly below; the other case swaps the two pairs.
2. Write w_{i−2} = e(−α₁) and w_{i−1} = e(−α₂) with 0 < α₂ < α₁ < 180°.
3. By Lemma M, |rw_{i−2}| = |rw_{i−1}| = Δ.
4. So r and p both lie on the perpendicular bisector of w_{i−2}w_{i−1}. That bisector is the line through 0 in direction −γ, where γ = (α₁ + α₂)/2 ∈ (0°, 180°).
5. Since r ≠ 0 and r is not below the axis, r = t·e(180° − γ) with t > 0.
6. From |r − wᵢ| = 1 we get t(t + 2cos γ) = 0, so t = −2cos γ (sympy). Since t > 0, γ > 90°, and therefore α₁ > γ > 90°.
7. Now |w_{i−2}wᵢ| = 2 sin(α₁/2) > √2 > 1, so this distance is Δ.
8. Let θ > 0 be the direction of w_{i+1}. By the half-plane fact, α₁ + θ < 180°. The chord length 2 sin(x/2) is strictly increasing on [0°, 180°]. So
   |w_{i−2}w_{i+1}| = 2 sin((α₁ + θ)/2) > 2 sin(α₁/2) = Δ.
   This contradicts the maximality of Δ. ∎

In Ve87, Prop 8 says that middle neighbours with ≥ 2 neighbours on each side have outer degree 1, and Prop 5 gives inner degree 0. Ve87 states this only for outer neighbours; the argument above bounds the total degree at once.

## Theorem (deg_{G′} ≤ 4 on L₁′)

Suppose p ∈ L₁′ has five G′-neighbours u₁, …, u₅ in angular order.
- Among p's G-neighbours, u₃ has at least two on each side (u₁, u₂ and u₄, u₅). So u₃ = wᵢ for some 3 ≤ i ≤ k − 2.
- By Lemma F, deg_G(u₃) = 1.
- But u₃ ∈ G′, so deg_G(u₃) ≥ deg_{G′}(u₃) ≥ 2. Contradiction. ∎

If one used a layer convention in which L₁ contains non-extreme boundary points, those points have deg_{G′} = 2 by VERIFY_A1b. The Case 1–3 argument there uses only that the point is not extreme.

## The rest of Ve87 Props 5–8, in G′ form (all hold)

Write out(p) and in(p) for the number of G′-neighbours of p that are extreme and non-extreme, respectively.

- **Prop 5 (strengthened, G-level).** Suppose v is a Δ₂-neighbour of an extreme point u, and u has Δ₂-neighbours strictly on both sides of the line uv. Then every Δ₂-neighbour r ≠ u of v is at distance Δ from one of those neighbours (Lemma M), so r is extreme (Prop 1). No inner edge starts at a middle neighbour. This is Ve87's proof; it needs no degree assumption.
- **Implicit claim "outer ≤ 2 ⇒ inner ≤ 2".** Stronger: **in(p) ≤ 2 always.**
  - Suppose r₁, r₂, r₃ are non-extreme G′-neighbours of p in angular order.
  - By Lemma M, any Δ₂-neighbour s ≠ p of r₂ is at distance Δ from r₁ or from r₃.
  - That contradicts Prop 1. So deg_G(r₂) = 1, which contradicts r₂ ∈ G′.
- **Prop 6** (out = 3 ⇒ in ≤ 1), **Prop 7** (out = 4 ⇒ in = 0) and **Prop 8** (out ≤ 4) all follow from out + in = deg_{G′}(p) ≤ 4.

Ve87's own proofs of Props 6–7 use forbidden-N / quadrilateral-inequality arguments together with deletion ("could be omitted and proceed by induction"). Those do not transfer verbatim to the 2-core. The route above avoids them: it needs only Lemma M, the bisector computation and chord monotonicity. **No claim was found false in the 2-core setting.** So these inputs to CDL Thm 1.3 (deg′ ≤ 4 on L₁′, and Prop 3 via VERIFY_A1b) stand.

## Verification

- **Exact:** `va1c_sympy.py` (sympy) checks four things symbolically: the Lemma M identity, t(t + 2cos γ) = 0, the chord formula, and that the bisector passes through 0 in direction −γ. Every inequality in the proof is then elementary: sign of a sum of nonnegative terms, and monotonicity of sin on [0°, 90°]. No numerical step remains.
- **Local exhaustive search** (`va1c_local.py`). It searches the Lemma F configuration in its 4-neighbour form: p, a₁, a₂, w, c, r, with a₁ and a₂ opposite r and c on r's side. It uses every choice of unit vectors from:
  - Z[ω] with norm ≤ 147 (exact): 268,128 configurations;
  - Z[i] with norm ≤ 325 (exact): 235,424 configurations;
  - N-th roots of unity for 5 ≤ N ≤ 60: 2,718,576 configurations.
  - **0 hits.** A control run that drops a₂ and c finds hits (240 cyclotomic for N ≤ 24, 1308 for Z[ω], 504 for Z[i]), so the search is live.
  - Side observation: a first control that dropped only c (keeping a₁, a₂) also gave 0 hits (roots of unity with N ≤ 24, Z[ω] with norm ≤ 49, Z[i] with norm ≤ 65). So even without c, the configuration with two neighbours on the far side never occurred. This suggests that a neighbour with ≥ 2 of p's neighbours on one side sends its other edges to that same side (Ve87 Prop 4 flavour). It is not needed here.
- **Global adversarial search** (`va1c_random.py`). Every set is run through `va1_common.analyze` (Thm A, A1, Unconditional form, Props 3, 5–8, CDL, 3n/2) plus two new checks: `deg4` and the G-level Lemma F for every hull vertex.
  - *Exhaustive pools* (maximal cliques in a half-plane pool, so p = 0 is extreme): Z[ω] with r² ≤ 49, Z[i] with r² ≤ 50, and cyclotomic pools. A Lemma F failure at 0 is monotone under adding compatible points, so this is exhaustive for Lemma F within each pool. **0 violations** (counts below).
  - *Greedy float constructions:* p with 5–7 neighbours in a 60° arc or in two θ_Δ-separated clusters, then up to 40 circle-intersection additions biased towards the middle neighbours. 3000 seeds (1551 pass the separation filter), and 1349 of them have a hull vertex with h ≥ 5; **0 violations**.
  - One early float artefact (points 3·10⁻⁵ apart on an arc, read as collinear by the hull code) was removed by imposing a minimum separation of 10⁻³.

Counts ("h ≥ 5" is the number of sets with a hull vertex having ≥ 5 Δ₂-neighbours, where Lemma F is non-vacuous):

| search | sets checked | h ≥ 5 | violations |
|---|---|---|---|
| pool Z[ω], r² ≤ 49 (exact) | 54,728 | 24 | 0 |
| pool Z[i], r² ≤ 50 (exact) | 15,914 | 0 | 0 |
| pool Z[ζ₁₂], ≤ 3 roots, r² ≤ 4.1 | 7,830 | 135 | 0 |
| pool Z[ζ₈] (W=3), Z[ζ₁₀] (W=2,3), Z[ζ₁₂] (W=2) | 1,301 | 0 | 0 |
| greedy float, 3000 seeds (1551 valid starts) | 1,551 | 1,349 | 0 |

No clique enumeration hit its cap. Greedy sets reach μ(Δ₂) − n = 5, which is consistent with Ve87's 3n/2.

## Consequence

- **The Unconditional form of Cor A1 is proved.** Theorem A (angle_C.md) together with 2 ≤ deg_{G′}(p) ≤ min(h(p), 4) on L₁′ gives
  μ(Δ₂) ≤ |L₁| + |L₂| + ½ Σ_{p∈L₁} (min(h(p), 4) − 2)⁺.
  So μ(Δ₂) ≤ n whenever that sum is ≤ 2m₃.
- CDL's 2|L₁| + |L₂| (Thm 1.3, first bound) now rests only on VERIFY_A1b and this file, plus obs. (1)–(2).
- Refinement available for free: in(p) ≤ 2, so in fact deg_{G′}(p) ≤ min(h(p), 4, out_{G′}(p) + 2).

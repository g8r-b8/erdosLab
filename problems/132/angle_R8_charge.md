# Erdős #132, angle R8: the Charge Lemma

Date: 2026-09-25. Scripts: `problems/132/scripts/r8_charge_*.py`.
Builds on `angle_R5.md` §3 (hooks, trapezoid lemma, core configuration).

## 0. Summary and status

| Claim | Status |
|---|---|
| **Charge Lemma**: each (x, orientation) carries at most one hook (§1) | **PROVED** (§3–§5) |
| Core configuration of R5 §3.3–3.4 does not exist (Thm 5.1) | **PROVED**, elementary |
| Lemma D (same middle vertex ⇒ opposite orientations; R5 stated it without proof) | **PROVED** (§4) |
| **μ(Δ₂) ≤ \|L₁\| + \|L₂\| + \|V_Δ ∩ L₁′\| ≤ n − m₃ + \|V_Δ\|** | **PROVED** (§6), using Theorem A (Lean `Erdos132Layer.theoremA`) |
| Computer-assisted steps | **none**. Every identity used is also machine-checked in sympy (72 checks); float and exact-lattice stress tests found 0 failures. |
| Lean formalisation of R8 | OPEN (not attempted) |

Main points.

1. The proof is elementary. After the trapezoid lemma fixes coordinates, each step is a sign argument or a monotonicity argument. No interval arithmetic or branch-and-bound is needed, so the brief's fallback (interval arithmetic on the 5-parameter region) was not used.
2. **The reduction is more general than in R5.** *Any* two same-orientation hooks at x through different middle vertices form a core configuration (Prop 3.1). This avoids Lemma F′ and the u_{k−1}, u_k indexing.
3. **Correction to R5 §3.4's numerical chain.** R5 said "b′ = b is forced". That is false if only distances are used.
   - There is a 2-parameter family (case γ3 of Step 1: |xb′| = |pb′| = Δ) in which all 21 distances among x, p, b, u, w, p′, b′ are admissible.
   - R5's scan (`r5_b_core.py`) missed it: it sampled p′ only at angles where a distance *from p′* equals 1 or Δ, and here the special distance is |pb′|.
   - In this family p′ is never extreme: it lies inside the triangle u b′ p. So b′ = b does hold once the extremality of p′ is used.
   - The rest of R5's chain is confirmed and sharpened:
     - p′ is the axis point above xp, which forces s > 2t (R5's σ > 2τ);
     - then *every* candidate third neighbour c′ has |c′p| > Δ. R5 said "|c′p| = Δ, which puts c′ on the wrong side"; the strict inequality is stronger.

## 1. Setting and definitions

**Hypotheses (exactly those of R5 §3).**
- X ⊂ ℝ² is finite and spans at least two distinct distances.
- Δ > Δ₂ are its two largest distances, normalised so that Δ₂ = 1.
- Hence:

  (★) every distance between distinct points of X lies in (0, 1] ∪ {Δ}, and Δ > 1.

- Nothing else is assumed: no counterexample hypothesis and no bound on n.

**Notation.**
- e(θ) = (cos θ, sin θ), and cross(o; a, q) = (a − o) × (q − o).
- "Extreme" means a vertex of conv X, and L₁ is the set of extreme points.
- A *unit neighbour* of q is a point at distance 1 = Δ₂ from q.
- G is the Δ₂-graph and G′ its 2-core on L₁ ∪ L₂. L₁′ = L₁ ∩ V(G′), and deg′ is the degree in G′.
- V_Δ is the set of endpoints of Δ-pairs, and m₃ = n − |L₁| − |L₂|.

**Definitions.**
- A unit neighbour w of an extreme point p is **middle** if p has unit neighbours strictly on both sides of the line pw.
- A **hook** is a triple (p, w, x) where:
  - p is extreme;
  - w is a middle neighbour of p;
  - x ≠ p is a unit neighbour of w.
- R5's hook (p, w, x; b) also names b, an outer unit neighbour of p strictly beyond pw from x. The charging never uses b, so we drop it. Every R5 hook gives a hook in our sense, and conversely T7 below supplies a b.
- By T7, x is strictly off the line pw. The **orientation** of the hook is ε = sign cross(x; w, p) ∈ {±1}.

> **Charge Lemma.** For every x ∈ X and every ε ∈ {±1}, there is at most one hook (p, w, x) with orientation ε.

By Prop 3.1 the Charge Lemma is equivalent to the conjunction of:
- (i) **Lemma D**: two hooks (p, w, x) and (p′, w, x) with p ≠ p′ have opposite orientations;
- (ii) **Theorem 5.1**: the core configuration does not exist.

## 2. Tools (all proved; references given)

**T1 (Lemma M, VERIFY_A1c.md; Lean `lemmaM_real`).**
- Hypotheses: |pa| = |pb| = |br| = 1 and r ≠ p; a lies strictly on one side of the line pb, and r does not lie strictly on that side.
- Conclusion: |ar| > 1, and hence |ar| = Δ by (★).
- The identity behind it, |r − a|² − 1 = 2(1 + cos F)(1 − cos A) + 2 sin F sin A, is re-checked in `r8_charge_identities.py`.

**T2 (non-extreme points).**
- A point that is a convex combination of other points of X is not extreme.
- **Prop 1.** If |xb| = Δ, then x and b are extreme.
  - Suppose instead x = Σλᵢzᵢ with zᵢ ∈ X∖{x} and λᵢ > 0.
  - Then |x − b|² = Σλᵢ|zᵢ − b|² − Σλᵢ|zᵢ − x|² < max|zᵢ − b|² ≤ Δ², a contradiction.

**T3 (directions at an extreme point).**
- If p is extreme, there is a vector v with v·(q − p) > 0 for all q ∈ X∖{p}.
- Hence the directions from p to any points q₁, …, q_m of X∖{p} lie in an open half-plane.
- Contrapositive: suppose these directions, sorted by angle, have every consecutive gap (cyclically) ≤ π. Then 0 is a nonnegative non-trivial combination of the vectors qᵢ − p. So p ∈ conv{qᵢ}, and p is not extreme.

**T4 (crossing lemma; classical, Hopf–Pannwitz / Erdős 1946).** If |ab| = |cd| = Δ with a, b, c, d ∈ X, then the segments [a, b] and [c, d] intersect.

*Proof.* Suppose the segments are disjoint. Then the four points are distinct.
- **Some point lies in the convex hull of the other three.** Say d ∈ conv{a, b, c}, with d ∉ {a, b} since the segments are disjoint. Strict convexity of |· − c|² gives |cd| < max(|ca|, |cb|) ≤ Δ. This is a contradiction; the other labellings are symmetric.
- **Otherwise the points are in strictly convex position.** No three are collinear, and [a, b] and [c, d] are disjoint, so they are opposite sides of the quadrilateral. Its diagonals meet at an interior point o. The triangle inequality at o gives: sum of diagonals > |ab| + |cd| = 2Δ. So some diagonal exceeds Δ, a contradiction. ∎

**T5 (Lemma T, angle_C.md).**
- Hypotheses: |ab| = |cd| = Δ and |ac| = |bd| = 1.
- Conclusion: d is the reflection of a in the perpendicular bisector of bc.
- The other isometry exchanging b and c, the half-turn, would give |ad|² + |bc|² = 2(Δ² + 1) > 2Δ².

**T6 (Trapezoid Lemma, R5 Thm 2, re-proved here with all degenerate cases).**
- Hypotheses: (p, w, x) is a hook, and u is a unit neighbour of x strictly on the opposite side of line xw from p.
- **Normal form (N).** After an isometry:
  - x = (−s, 0), p = (s, 0), u = (−t, −d), b = (t, −d), w = (0, −k), where b is any unit neighbour of p strictly beyond line pw from x;
  - d = √(1 − (t−s)²) > 0, k = √(1 − s²) > 0, and 0 < s < 1, t > 0;
  - **Δ² = 1 + 4st**, and |pu| = |xb| = Δ;
  - cross_w := cross(x; u, w) = sd − k(s − t) > 0;
  - 2s, 2t ∈ (0, 1] ∪ {Δ}, not both equal to Δ;
  - **Δ ≤ φ** = (1+√5)/2.

*Proof.*
1. **Δ-distances.** |pu| = Δ by T1: centre x, legs xw and wp, u and p strictly on opposite sides of xw. Also |xb| = Δ by T1: centre p, legs pw and wx.
2. **Coordinates.** Apply T5 to (a, b, c, d) = (x, b, u, p). This gives p = σ(x) and u = σ(b), where σ is the reflection in a line L. Take L as the vertical axis, with x = (−s, 0), p = (s, 0) and b = (τ, −δ), u = (−τ, −δ). Then Δ² − 1 = |xb|² − |xu|² = 4sτ, so s and τ have the same sign. Reflecting in L if necessary, s, τ > 0. Reflecting in the horizontal axis if necessary, δ ≥ 0.
3. **δ ≠ 0.** Suppose δ = 0, so all four points are collinear. Then 2s = Δ = s + τ would force s = τ and |xu| = 0, so 2s ≤ 1. Likewise 2τ ≤ 1. Then |xu| = |τ − s| ≤ ½, a contradiction. So δ > 0; write t = τ and d = δ.
4. **The point w.** |wx| = |wp| = 1 puts w on L. So s < 1. If s = 1, then w is the midpoint of xp and x lies on line pw, which T7 excludes. Hence w = (0, ±k).
5. **w = (0, +k) is impossible.**
   - The two hook side conditions become −sd − k(s − t) > 0, so t > s.
   - Then |wu|² = 2 + 2kd + 2s(t − s) > 2, so |wu| = Δ, i.e. 1 + 2kd = 2s(s + t).
   - If 2s, 2t ≤ 1: the right side is ≤ 1, but the left side is > 1.
   - If 2t = Δ: then 2s = Δ − 1/Δ ≤ 1, so Δ ≤ φ. The right side is (2Δ² − 3 + Δ⁻²)/2 ≤ (φ + 1)/2 < 5/2. The left side is > 1 + 2·(3/4) = 5/2, because k ≥ √3/2 and t − s = 1/(2Δ) < ½.
   - If 2s = Δ: then 2t = Δ − 1/Δ < 2s, which contradicts t > s.
6. **Remaining items of (N).** With w = (0, −k), the condition "u strictly beyond xw from p" is exactly cross_w > 0. Finally Δ² − 1 = (2s)(2t) ≤ 1·Δ, because the smaller of 2s, 2t is ≤ 1. So Δ² ≤ 1 + Δ and Δ ≤ φ. ∎

All identities in this proof are checked in `check_trapezoid`. Also, with (N): cross(x; u, p) = 2sd > 0, cross(x; u, b) = 2td > 0 and cross(x; b, p) = 2sd > 0. So **p, b and w all lie strictly on the same side of line xu, and seen from x the directions are ordered u, b, p.**

**T7 (x is off line pw; the far and near neighbours).** Let (p, w, x) be a hook.

- **x is strictly off line pw.**
  - Otherwise x = 2w − p, so |px| = 2 = Δ.
  - Take unit neighbours a, c of p strictly on the two sides of pw. T1 gives |ax| = |cx| = 2.
  - Then a, c = (¼, ±√15/4) in the frame p = 0, x = (2, 0).
  - So |ac|² = 15/4 ∈ (1, 4), a contradiction (`check_offline`).
- **The far and near neighbours.** Let b be any unit neighbour of p strictly beyond pw from x (one exists because w is middle).
  - T1 gives |xb| = Δ.
  - By Prop 1, x ∈ V_Δ and x is extreme.
  - p also has a unit neighbour c strictly on x's side of pw.

## 3. Reduction to the core configuration

**Core configuration.** Points x, w, u, p, b, p′, b′, c′ of X with:
- **(C1)** (p, w, x) is a hook, and b is a unit neighbour of p strictly beyond pw from x;
- **(C2)** u is a unit neighbour of x strictly on the opposite side of line xw from p;
- **(C3)** (p′, u, x) is a hook with p′ strictly on the same side of line xu as w. Here b′ is a unit neighbour of p′ strictly beyond p′u from x (so |xb′| = Δ by T7), and c′ is a unit neighbour of p′ strictly on x's side of line p′u.

**Prop 3.1.** Let (p, w, x) and (p′, w′, x) be hooks with the same orientation and (p, w) ≠ (p′, w′). Then either w = w′ and p ≠ p′, or, after possibly exchanging the two hooks, a core configuration with u = w′ exists.

*Proof.*
1. By T7, x is extreme. Its unit neighbours w ≠ w′ therefore cannot be antipodal about x, so w′ is strictly off line xw.
2. Let ε be the common orientation, so sign cross(x; w, p) = sign cross(x; w′, p′) = ε.
3. **Case sign cross(x; w, w′) = −ε.** Then w′ is on the opposite side of xw from p, which is (C2). Also sign cross(x; w′, w) = ε = sign cross(x; w′, p′), so p′ and w are on the same side of xw′, which is (C3). Condition (C1) holds by T7.
4. **Case sign cross(x; w, w′) = +ε.** Then sign cross(x; w′, w) = −ε, and exchanging the two hooks gives the first case. ∎

*Remark.* R5 §3.3 reached the same configuration via Lemma F′, with w = u_{k−1} and u = u_k. Prop 3.1 shows that this indexing is not needed.

## 4. Lemma D

**Lemma D.** If (p, w, x) and (p′, w, x) are hooks with p ≠ p′, then they have opposite orientations.

*Proof.*
1. **Frame.** Suppose both hooks have the same orientation. Work in the frame w = 0, x = e(0), with p and p′ in the upper half-plane: p = e(θ), p′ = e(θ′), 0 < θ, θ′ < π, θ ≠ θ′. The two hooks play symmetric roles, so we may assume θ < θ′.
2. **The point b′ lies on the bisector.** Let b′ be a unit neighbour of p′ strictly beyond line wp′ from x. By T7, |xb′| = Δ.
   - Both x and p lie strictly on one side of line wp′, because their angles lie in (θ′ − π, θ′).
   - T1 (centre p′, legs p′w and wp, a = b′, r = p) gives |pb′| = Δ.
   - So b′ lies on the perpendicular bisector of xp, which is the line through w in direction e(θ/2). Write b′ = ρ e(θ/2).
3. **Solving for ρ.** |p′b′| = 1 gives ρ(ρ − 2cos(θ′ − θ/2)) = 0. Since b′ ≠ w (because |xw| = 1 ≠ Δ), we get ρ = 2cos(θ′ − θ/2).
4. **ρ < 0.** Next, Δ² = |xb′|² = 1 + ρ(ρ − 2cos(θ/2)) > 1. We have θ/2 < θ′ − θ/2 < π − θ/2, so cos(θ′ − θ/2) < cos(θ/2), i.e. ρ − 2cos(θ/2) < 0. Hence ρ < 0, which means **θ′ > π/2 + θ/2**.
5. **|xp′| = Δ.** |xp′| = 2 sin(θ′/2) > 2 sin(π/4) = √2 > 1. So |xp′| = Δ by (★).
6. **The two short distances.**
   - |xp| = 2 sin(θ/2) < 2 sin(θ′/2) = Δ, so |xp| ≤ 1 and θ ≤ π/3.
   - |pp′| = 2 sin((θ′ − θ)/2) < 2 sin(θ′/2) = Δ, so |pp′| ≤ 1 and θ′ ≤ θ + π/3.
7. **Contradiction.** Combining with step 4: π/2 + θ/2 < θ + π/3, i.e. θ > π/3. This contradicts θ ≤ π/3. ∎

Identities: `check_lemma_D`. Lemma D uses only T1, T7 and (★); no extremality is used. The case "x has a unit neighbour beyond xw" also follows from `mid_pair_real`, as R5 noted, but the proof above covers every case.

## 5. The core configuration does not exist

**Theorem 5.1.** No finite X satisfying (★) contains a core configuration.

*Proof.*
- **Setup.** Apply T6 to (C1) and (C2). This puts x, p, u, b, w in normal form (N).
- **Hypotheses used from (C3).**
  - (a) p′ is extreme.
  - (b) |p′u| = 1, p′ ≠ x, and p′ lies strictly on w's side of line xu.
  - (c) |p′b′| = 1, |xb′| = Δ, and x and b′ lie strictly on opposite sides of line up′.
  - (d) |p′c′| = 1, and c′ lies strictly on x's side of line up′.

### Step 1: b′ = b

**Frame F.** Move x to 0 by an isometry, with u = e(0) and w's side of xu being the upper half-plane.
- By T6, p = 2s·e(θ_p) and b = Δ e(A_b) with **0 < A_b < θ_p < π**.
- By (b), p′ = u + e(ψ) with sin ψ > 0. Writing g = ψ/2:

  p′ = 1 + e(2g) = r e(g),  r = 2cos g,  **0 < g < π/2**,

  so r ∈ (0, 2).
- Write b′ = Δ e(A).

**Crossing.** [x, b′] and [p, u] are Δ-segments, so by T4 they meet at some point z. Since x, p, u are not collinear, z ≠ x. So b′ lies in the closed cone spanned by u and p, i.e. **A ∈ [0, θ_p]**.

Now split by the position of A relative to g and A_b.

- **(α) A > g.**
  - p′ lies in the open cone spanned by u and b′, whose angle A is < π. Write p′ = λu + μb′ with λ, μ > 0.
  - If λ + μ ≤ 1, then p′ ∈ conv{x, u, b′} and p′ ∉ {x, u, b′}. So p′ is not extreme (T2), contradicting (a).
  - If λ + μ > 1, then cross(u; p′, x) = μ·Δ sin A and cross(u; p′, b′) = (λ + μ − 1)·Δ sin A. These have the same strict sign, contradicting (c).
- **(β) A = g.**
  - Then x, p′, b′ lie on one ray, and |r − Δ| = 1.
  - r = Δ + 1 > 2 is impossible, so r = Δ − 1 and p′ lies in the open segment (x, b′). So p′ is not extreme.
- **(γ1) A_b < A < g.** Here 0 < g − A < g − A_b < g < π/2.
  - Since |b| = |b′| = Δ, we have |p′b|² − 1 = |p′b|² − |p′b′|² = 2p′·(b′ − b) = 2rΔ(cos(g − A) − cos(g − A_b)) > 0.
  - Also |p′b|² − Δ² = 2r(cos g − Δ cos(g − A_b)) < 0, because cos(g − A_b) > cos g > 0 and Δ > 1.
  - So 1 < |p′b| < Δ, which contradicts (★).
- **(γ2) A = A_b.** Then b′ = b.
- **(γ3) 0 ≤ A < A_b.**
  - **|pb′| = Δ.** The law of cosines is monotone: θ_p − A_b < θ_p − A ≤ θ_p < π. So |pb′| > |pb| = 1, hence |pb′| = Δ.
  - **Short base.** Likewise ℓ := |ub′| < |ub| = 2t ≤ Δ, so ℓ ≤ 1 by (★).
  - **Both p and p′ lie on m.** Since |pu| = |pb′| = Δ and |p′u| = |p′b′| = 1, both lie on the perpendicular bisector m of ub′. Let M be the midpoint of ub′. Then p = M + h₂n, with h₂ = √(Δ² − ℓ²/4), and p′ = M ± h₁n, with h₁ = √(1 − ℓ²/4) < h₂.
  - **Sign "+".** p′ lies in the half-open segment [M, p), and M lies in the open segment (u, b′). So p′ is a convex combination of u, b′, p with p′ ∉ {u, b′, p}. So p′ is not extreme.
  - **Sign "−".** |pp′|² = (h₁ + h₂)² = Δ² + 1 − ℓ²/2 + 2h₁h₂ > Δ², since ℓ ≤ 1. This contradicts the definition of Δ.
  - This is the family R5's scan missed. Every distance among the 7 points can be admissible here; only extremality of p′ excludes the "+" apex.

So b′ = b.

### Step 2: p′ is the upper axis point, and s > 2t

- **The two candidates.** p′ ∈ C(u, 1) ∩ C(b, 1) = {P₁, P₂}, where P₁ = (0, c − d) and P₂ = (0, −d − c) with c = √(1 − t²) (in the identity script the Step 3 angle η is called `phi`). Here t < 1 because 2t ≤ Δ ≤ φ < 2.
- **P₂ is excluded by the side conditions.**
  - (b) requires sign cross(x; u, P₂) = sign cross_w > 0.
  - (c) requires cross(u; P₂, x) < 0, because cross(u; P₂, b) = 2ct > 0.
  - But **cross(x; u, P₂) = cross(u; P₂, x) = td + c(t − s)** identically (`check_step2`), so the two requirements contradict each other.
  - Example: in the regular pentagon (s = ½, 2t = φ), P₂ is the fifth vertex, and it is exactly this side condition that fails (`check_strata`).
- **P₁ must lie above xp.**
  - If c − d ≤ 0, then P₁ is on the segment from (0, 0) (the midpoint of xp) to (0, −d) (the midpoint of ub), excluding the latter. So P₁ ∈ conv{x, p, b, u} and is not a vertex, hence not extreme.
  - So c > d. Since c² − d² = s(s − 2t), this means **s > 2t**. This is R5's "σ > 2τ", and the stratum s = 2t (where P₁ is the midpoint of xp) is included here.
  - In particular 2t < 2s ≤ Δ, so 2t ≤ 1 by (★), and t ≤ ½.

### Step 3: p′ = P₁ has no admissible c′

**Frame.** Put y = c − d > 0 and η = arcsin t ∈ (0, π/6]. Then, measured from p′:

  u − p′ = (−t, −c) = e(3π/2 − η),  b − p′ = (t, −c) = e(3π/2 + η),  p − p′ = (s, −y) = R e(−ζ),

with R = √(s² + y²) and ζ ∈ (0, π/2).

**Range of c′.** Write c′ = p′ + e(γ).
- **Side condition (d).**
  - cross(p′; u, x) = ty − cs < 0, since t < s and y < c. It also equals −(td + c(s − t)).
  - cross(p′; u, c′) = cos(γ + η).
  - So (d) means cos(γ + η) < 0, i.e. γ ∈ (π/2 − η, 3π/2 − η).
- **Extremality (a).** Apply T3 to the three directions of c′, u, b.
  - Suppose γ ∈ (π/2 − η, π/2 + η]. The cyclic gaps are 3π/2 − η − γ < π, then 2η ≤ π/3, then γ + π/2 − η ≤ π. All are ≤ π, so p′ is not extreme.
  - Hence **γ ∈ (π/2 + η, 3π/2 − η)**.

**Every such c′ is too far from p.**
- **The distance formula.** |c′p|² = 1 + R² − 2R cos(γ + ζ).
- **Its value at c′ = u.** The value at the excluded endpoint γ = 3π/2 − η is |up|² = Δ². Note that c′ = u itself is excluded, because u lies on line p′u.
- **Where θ = γ + ζ lives.** θ ranges over the open interval I = (π/2 + η + ζ, 3π/2 − η + ζ) ⊂ (π/2, 2π), because ζ − η < π/2.
- **Shape of cos on I.** On (π/2, 2π), cos decreases up to π and then increases. So on the open interval I, cos θ < max(cos(left end), cos(right end)) = max(−sin(ζ + η), sin(ζ − η)).
- **The right end wins.** sin(ζ − η) − (−sin(ζ + η)) = 2 sin ζ cos η > 0, so the maximum is sin(ζ − η).
- **Conclusion.** cos θ < sin(ζ − η), and therefore

  |c′p|² > 1 + R² − 2R sin(ζ − η) = |up|² = Δ².

  This contradicts the definition of Δ. ∎

**Which hypotheses were used.**
- (★): only for the pairs pb′, ub′, p′b in Step 1.
- Extremality: of p′ throughout, and of x (via T7).
- The strict side conditions of both hooks.

The distances from c′ to x, b, u, w and the "outer" choice of b, b′ were never used. So the theorem is stronger than the configuration R5 scanned.

## 6. Consequence

**Theorem 6.1.** For every finite X ⊂ ℝ² with at least two distances:

  **μ(Δ₂) ≤ |L₁| + |L₂| + |V_Δ ∩ L₁′| ≤ n − m₃ + |V_Δ|.**

*Proof.*
1. **Theorem A** (angle_C.md; Lean `Erdos132Layer.theoremA`) gives μ(Δ₂) ≤ |L₁| + |L₂| + ½E, where E = Σ_{p∈L₁′}(deg′p − 2).
2. **E counts middle core pairs.** E is the number of pairs (p, w) with p ∈ L₁′ and w one of the deg′p − 2 core neighbours of p that are not first or last in angular order. Such a w is a middle neighbour of p. By the half-plane fact T3, the core neighbours of p lie in an open half-plane, so the angular order is well defined.
3. **Each pair gives a hook at a charged vertex.** For such (p, w), w ∈ G′ has a G′-neighbour x ≠ p, so (p, w, x) is a hook. By T7, x is extreme and x ∈ V_Δ; also x ∈ V(G′). So x ∈ V_Δ ∩ L₁′.
4. **Charging.** Choose one such x for each pair and send (p, w) to (x, orientation). By the Charge Lemma (Lemma D plus Prop 3.1 plus Thm 5.1) this map is injective. Hence E ≤ 2|V_Δ ∩ L₁′|.
5. **Conclusion.** Substitute into step 1, and use |L₁| + |L₂| = n − m₃. ∎

**Exact chain of lemmas used.**
- Theorem A. This rests on CDL obs. (1), (2) and Prop 3; see VERIFY_A1b, and Lean `theoremA`.
- Lemma M (T1), Lemma T (T5), Prop 1 and T2–T4.
- The Trapezoid Lemma (T6, which is R5 Thm 2 re-proved above) and T7 (which is R5 Thm 1(b)).
- Prop 3.1, Lemma D and Theorem 5.1.
- **Not used:** Lemma F, Lemma F′, `mid_pair_real`, the middle lemma, and deg′ ≤ 4. Using deg′ ≤ 4 (E = t₃ + 2t₄) only rewrites the bound as t₃/2 + t₄ ≤ |V_Δ ∩ L₁′|.

**Corollaries (from R5 §3.4, now unconditional).**
- In Case II (μ₂ ≥ n + 1): |V_Δ ∩ L₁′| ≥ m₃ + μ₂ − n ≥ m₃ + 1.
- By Hopf–Pannwitz, |V_Δ| = μ(Δ) + #(acyclic components of the Δ-graph).
- **Tightness.** The sharpened bound is tight on R5's rings (regular m-gon plus one server per edge). There μ₂ = 3m = m + m + m, and every hull vertex carries exactly 2 hooks, one per orientation, so the Charge Lemma is tight too. This was re-checked in float for m = 7, …, 12 and 16 (`r8_charge_exact.py rings`).
- The bound is false with μ(Δ) in place of |V_Δ| (even rings; R5).

## 7. Verification scripts (run via `tools/memcap.sh 3000`, one process at a time)

| Script | What it checks | Result |
|---|---|---|
| `r8_charge_identities.py` | Every identity in T1, T6, T7, Lemma D and Steps 1–3, plus exact boundary strata (s = 2t, regular pentagon, Δ ≤ φ). Exact sympy, Gröbner reduction modulo d² = 1 − (t−s)², k² = 1 − s², c² = 1 − t² | 72/72 ok, `ALL OK` |
| `r8_charge_stress.py 60` | Float, *not* part of the proof. Step 1: b′ swept over C(x, Δ) plus the special points b, p and the γ3 point; p′ from both circle intersections; each admissible (p′, b′) classified into α/β/γ1/γ2/γ3± and the proof's stated reason re-checked. Steps 2–3: both apexes, and a sweep of γ over the whole x-side. Lemma D: θ < θ′ grid, plus the stratum \|xp′\| = Δ by bisection | 1,113,237 admissible (p′, b′), 0 failures. Every out-of-cone b′ has a pair > Δ (T4). γ3 "+" occurs 1,042 times, all non-extreme. Min normalised margin of \|c′p\| − Δ > 0. `ALL OK` |
| `r8_charge_exact.py tri 49` | Exact Z[ω] cliques (the pools of `r5_b_exact.py`): tests CH, LD, CC, EX, x-on-line, K8+ = Theorem 6.1, and E ≤ 2\|V_Δ ∩ L₁′\| | 76,187 sets, 5,062 hooks, 0 violations |
| `r8_charge_exact.py sq 65` | Same tests on Z[i] | 128,827 sets, 755 hooks, 0 violations |

| `r8_charge_exact.py rings` | Float: Theorem 6.1 and the Charge Lemma on rings, m = 7…12, 16 | tight in every case (μ₂ = bound = 3m, 2m hooks) |

The lattice counts reproduce R5's (76,187 / 5,062 and 128,827 / 755).

## 8. PROVED / computer-assisted / OPEN

- **PROVED:**
  - T6 (with the degenerate cases δ = 0 and s ≥ 1 closed) and T7;
  - Prop 3.1 and Lemma D;
  - Theorem 5.1, and hence the Charge Lemma;
  - Theorem 6.1.
- **Computer-assisted: nothing.** The sympy script is a mechanical check of identities that can each be expanded directly. The float and lattice runs are sanity checks, not proof steps.
- **OPEN:**
  - Lean formalisation. The natural route is a frame-based real-arithmetic lemma per step, as in E132Ve87; all steps are polynomial identities plus sign facts.
  - Everything in R5 §6 beyond (i): Case II with μ₃ ≥ n + 1, and Conjecture R5.4.

## 9. Referee attack points and double checks

**(A) Step 1, the case split in frame F.** Angle and sign conventions are the most error-prone part.
- **Frame facts used:**
  - 0 < A_b < θ_p < π (exact: cross(x; u, b) = 2td, cross(x; b, p) = 2sd, cross(x; u, p) = 2sd, all > 0);
  - g ∈ (0, π/2) (from Im p′ > 0);
  - the crossing lemma, which puts A in [0, θ_p]. Without it, (γ3)'s monotonicity would fail for A < 0.
- **The (α) sub-case λ + μ > 1** is excluded by the side condition (c), not by distances. The identities cross(u; p′, x) = μ cross(0; u, b′) and cross(u; p′, b′) = (λ + μ − 1) cross(0; u, b′) are checked exactly.
- **The γ3 family.** It contradicts R5's "b′ = b is forced" as a distance statement. It is killed only because p′ lies inside triangle u b′ p. The stress test confirms that all 1,042 sampled γ3-with-|pb′| = Δ cases have p′ in that triangle, and that the "−" apex never satisfies the hook side conditions.
- **Boundary strata re-checked:**
  - b′ = p (2s = Δ): A = θ_p, covered by (α)/(γ1) with no special role.
  - A = 0 (b′ on ray xu): covered by (γ3).
  - p′ = w or p′ = b (possible if |wu| = 1 or 2t = 1): the arguments never assume p′ is a new point.
  - Equality |p′b| = Δ in (γ1): excluded strictly, because cos(g − A_b) > cos g.

**(B) Step 3, the extremality range and the valley argument.**
- The infimum Δ² of |c′p|² is approached only as c′ → u. That point is excluded because (d) is strict: u lies on line p′u. So the inequality is strict on the whole open range.
- The lower end of the range (c′ antipodal to b) is not needed in isolation: only the comparison of the two endpoint values of cos matters, and that is the identity sin(ζ − η) + sin(ζ + η) = 2 sin ζ cos η > 0 (exact).
- **Range for θ.** I ⊂ (π/2, 2π) needs ζ − η < π/2, which holds since ζ < π/2 and η > 0.
- **Extremality exclusion.** For γ ∈ (π/2 − η, π/2 + η] all three gaps are ≤ π; the stress test re-checks the extremality exclusion on 28,951 samples.
- **Stratum s = 2t.** P₁ is the midpoint of xp, so it is handled in Step 2 (exact: c = d there).

**(C) Definitions and the reduction.**
- **Hook definition.** Hooks here are triples with no "outer b". This only enlarges the hook set, so the Charge Lemma is stronger than R5's CX.
- **Theorem 6.1 counts each (p, w) once**, choosing one x. Injectivity needs exactly "same x and same orientation ⇒ same (p, w)", which is Lemma D plus Thm 5.1 via Prop 3.1.
- **Collinear x** (x on line pw) is excluded by T7. Exact: |ac|² = 15/4.
- **Lemma D's WLOG θ < θ′** is legitimate because both hooks satisfy identical hypotheses.
- **T6's WLOGs** (reflections in L and in the horizontal axis) preserve every hypothesis. The degenerate case δ = 0 is closed explicitly.
- **R5 Thm 2's case "2t = Δ"** uses Δ ≤ φ, and that is proved inside the case (2s = Δ − 1/Δ ≤ 1).

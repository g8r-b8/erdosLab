# Erdős #132 / CDL Problem 1.6: Angle A2, an unconditional bound below 3/2

Date: 2026-09-23. Continues `angle_A.md`.

New scripts, all in `scripts/`:
- `lp5.py`: the LPs.
- `a2_checks.py`: threshold constants, the lens-corner bound, the final LPs.
- `degen_check.py`: the degenerate regime.
- `classify_a2.py`: edge classification on the ring constructions.

## 0. Main result

**Theorem A2.** There is an absolute constant C₀ such that for every n-point set X ⊂ R²,

  min{μ(Δ₂), μ(δ)} ≤ (54/37)·n + C₀.

Here 54/37 ≈ 1.4595 < 3/2. So Problem 1.6 has L ≤ 54/37.

External results used as black boxes:
- **[Ve87]** Vesztergombi, Discrete Math. 67 (1987): *in any m-point planar set, the second-largest distance occurs at most 3m/2 times.* CDL (arXiv 2505.04283, §2.2, ref. [23]) quotes it with no condition on m.
- **[HP]** Hopf–Pannwitz: the diameter occurs at most m times.
- Trivial fact: a point has at most 6 points at the minimum distance.

**The CDL/Vesztergombi structural Props 1–8 are no longer needed.** Theorem A in `angle_A.md` used them; Theorem A2 does not.

What each regime gives (δ = 1, t = Δ − Δ₂, τ := t − (1 − t²)/(2Δ₂), β := 1/100):

| regime | bound | main tool |
|---|---|---|
| degenerate: Δ > 1.94 Δ₂, n ≥ 4 | μ(Δ₂) ≤ n + 1 | star diameter graph + ball-polygon incidences (§6) |
| I: τ ≤ √3/2 − 2β (includes t → 0, the 9/7 construction) | 18n/13 + C ≈ 1.385n | band lemma → e(S) ≤ \|S\| + C |
| III: √3/2 − 2β < τ < √3/2 + 3β | 7n/5 + C | rung vertices are pruned; weighted LP |
| II, near-resonant: τ ≥ cos(β/2) (t within ~β²/8 of 1) | 54n/37 + C | ownership/rhombus lemma → e(S) ≤ (4/3)\|S\| + C |
| II, rest: √3/2 + 3β ≤ τ < cos(β/2), plus all τ > 1 | 36n/25 + C = 1.44n | same lemma; rhombi impossible → (5/4)\|S\| |

Here C depends only on β and on the constant 1.94 (see §7). If Δ₂ < Δ₀ := 10⁴, then Δ ≤ 2Δ₂ is bounded, so n = O(1). That case goes into C₀.

**Correction to angle_A.md.** Its Proposition R (16/11) and the claim "k < 1.2 needed" did not apply [Ve87] to S. With (VS) below, the Ring Lemma alone gives 18/13, and **any** k < 3/2 suffices. I re-checked `lp3.py`/`lp4.py`: they reproduce 16/11 for k = 1, and 19/13 = 1.4615 for pruned-weight α = 3 in the old LP. So the previous agent's LP claim is verified, but it has been superseded.

## 1. Reduction (VS): the only LP needed

Let S be the set of points having a Δ₂-partner, and R = X ∖ S, with r = |R|.

**(VS) μ(Δ₂) ≤ (3/2)|S|.**
- Every Δ₂-pair lies inside S, and distances within S are distances of X.
- If S contains a diametral pair of X, then Δ₂ is the second-largest distance of S (X has no distances in (Δ₂, Δ)). So [Ve87] applies to S.
- Otherwise diam S = Δ₂, and [HP] gives μ ≤ |S|.

**(E) μ(δ) ≤ e_δ(S) + 6r.** Every δ-edge not inside S has an endpoint in R, and each point has δ-degree ≤ 6.

**Lemma 1.1.** If e_δ(S) ≤ k|S| + C with k < 3/2, then min{μ(Δ₂), μ(δ)} ≤ 9n/(7.5 − k) + C.

Proof. Put s = |S|. If s ≤ 6n/(7.5 − k), use (VS). Otherwise use μ(δ) ≤ 6n − (6 − k)s + C. ∎

Values: k = 1 gives 18/13; k = 5/4 gives 36/25; k = 4/3 gives 54/37; k = 7/5 gives 90/61 (`lp5.py`).

**Weighted version (Region III).** Let P₁ ⊂ S be a set of points of Δ₂-degree exactly 1. Then
  μ(Δ₂) ≤ |P₁| + (3/2)(|S| − |P₁|).
The Δ₂-edges not touching P₁ lie inside S ∖ P₁, so apply [Ve87]/[HP] to S ∖ P₁.

If also e_δ(S) ≤ |S| + 2|P₁| + C, then maximising T subject to
  T ≤ 1.5s − 0.5p,  T ≤ s + 2p + 6r,  s + r = n
gives T = 7n/5 (at p = n/5, r = 0; `a2_checks.py`). The direct check: T ≥ 1.4 + ε forces p ≤ 0.2 − 3r − 2ε, and then the second bound is < 1.4 + ε.

## 2. Geometry common to all regimes (δ = 1)

Notation: D = set of diameter endpoints, and K := ∩_{w∈X} D(w, Δ₂).

Standard facts from angle_A §2 (Lemma 2):
- X ∖ D ⊂ K and S ∖ D ⊂ ∂K.
- dist(z, K) ≥ t for z ∈ D.
- D consists of hull vertices.

Direction field:
- For p ∈ S ∖ D: u_p = (w_p − p)/Δ₂, where w_p is a fixed Δ₂-partner.
- For p ∈ S ∩ D: u_p = (x_p − p)/Δ, where x_p is a fixed diametral partner.

**Lemma 2.1 (exact identities).**
- For p ∈ S ∩ D and every y: (y − p)·u_p ≥ |y − p|²/(2Δ) > 0.
- For p ∈ S ∖ D and every y: either (y − p)·u_p ≥ |y − p|²/(2Δ₂) > 0 ("normal"), or |y − w_p| = Δ, y ∈ D ("exception").
- In the exception case with |y − p| = 1, **exactly** (y − p)·u_p = −τ. So y − p = −τ u_p ± s u_p^⊥, with s := √(1 − τ²) = sin θ₀ and θ₀ := arccos τ.
- Exceptions at distance 1 need τ ≤ 1, so there are none for t > 1.

Proof: the law of cosines, using Δ² − Δ₂² = t(2Δ₂ + t). ∎

This exactness was not used in angle_A. It is the key new ingredient.

**Normal cones.** u_p is an inward normal of K at p (for p ∈ S ∖ D), or of P1 = conv X at p (for p ∈ D). Distinct boundary points have normal cones with disjoint interiors, so the total is 2π.

**Lemma 2.2 (no common normal).** If p ≠ q are in S ∖ D, then u_p ≠ u_q. Indeed, by 2.1, (q − p)·u_p > 0 and (p − q)·u_q > 0, and the two cannot both hold with u_p = u_q.

**Good and bad edges.** A δ-edge pq in S is **good** if ∠(u_p, u_q) ≤ β, and **bad** otherwise.

For a good edge, set a = (q − p)·u_p and b = (p − q)·u_q. Then |a + b| ≤ β, and exactly one of the following holds:
- **T-edge (tangential):** a, b ∈ (0, β).
- **Rung:** one end v ∈ S ∖ D sees the other end z ∈ D as an exception, a = −τ, and the other dot product lies in [τ − β, τ + β].

Both ends being exceptions is impossible (an exception source is in S ∖ D, an exception target is in D). The dichotomy needs τ > 2β, which holds in Regions II and III.

(T1) Each vertex has ≤ 1 T-neighbour on each side (left or right of u_p). Two T-directions on one side are within arcsin β of each other, hence < 60° apart.

(T2) If q is right of p, then p is left of q. So T-edges form paths and cycles, each with a well-defined rightward direction.

## 3. Bad edges are O(1)

Explicit constants, assuming Δ ≤ 1.94Δ₂ and Δ₂ ≥ 10⁴ ≥ 100/β. This completes the "sketched" part of angle_A.

**Lens lemma.** Let two circles of radius Δ₂ have centres at distance d ≤ λΔ₂, and put cos φ₀ = d/(2Δ₂); the lens corner angle is 2φ₀. Suppose p is on one arc, q is on the other, |pq| = 1, and Δ₂ ≥ 2/(cos(φ₀/2) − cos φ₀). Then p and q are within arc-distance ρ₀ = 1/sin(φ₀/2) of a **common** corner.

Proof. In coordinates, |pq| ≤ 1 forces cos φ − cos φ₀ ≤ 1/Δ₂ and cos ψ − cos φ₀ ≤ 1/Δ₂, which excludes |φ| < φ₀/2. Then the mean value theorem gives Δ₂(φ₀ − |φ|) ≤ 1/sin(φ₀/2). Opposite signs of φ and ψ would give |sin φ − sin ψ| ≥ 2 sin(φ₀/2) > 1/Δ₂. ∎

`a2_checks.py` samples 4000 lenses: the worst ratio of actual arc-distance to the bound is 0.52.

Constants:
- For KK edges, λ = 1.94, so φ₀ ≥ 14.07° and ρ₀ ≤ 8.2.
- For DD edges, the centres are at distance ≤ Δ with radius Δ, so φ₀ ≥ 60° and ρ₀ ≤ 2.

**Counting bad edges, by type.**

- **KK** (p, q ∈ S ∖ D):
  - If w_p = w_q, the angle is < 2/Δ₂ < β, so the edge is good.
  - Otherwise K ⊂ Λ(w_p, w_q), with p and q on different arcs (d = |w_p w_q| ≤ Δ ≤ 1.94Δ₂).
  - By the lens lemma, the arc of ∂K from p to q on the corner side lies in the curvilinear triangle (p, c, q). Its length is ≤ 2ρ₀ + 2, and its turning, endpoint cones included, is ≥ ∠(u_p, u_q) > β.
  - S ∖ D points are ≥ 1 apart along ∂K, and each has δ-degree ≤ 6. So every point of ∂K lies in ≤ 6(4ρ₀ + 5) such arcs.
  - Hence #KK-bad ≤ 12π(4ρ₀ + 5)/β ≈ 4.4·10⁴.
- **DD** (both ends in S ∩ D): the same argument with the lens of D(x_p, Δ) and D(x_q, Δ), on ∂P1, with ρ₀ = 2. At most 12π·13/β.
- **Cross, (c1)** (z ∈ D, v ∈ S ∖ D, |z w_v| = Δ):
  - (w_v − z)/Δ is a second P1-normal at z, and it is within 2/Δ₂ of u_v.
  - So the normal cone at z has angle > β/2.
  - At most 4π/β such z, each of δ-degree ≤ 4.
- **Cross, (c2)** (|z w_v| ≤ Δ₂):
  - Let g be the direction from v to x_z. Then ∠(u_v, g) > β/2, and v is at depth d₀ ≤ 1 − t ≤ 1 inside D(x_z, Δ₂) ⊃ K.
  - Move along ∂K from v in the direction e₀ ⊥ u_v with e₀·g < 0. If the turning stayed ≤ β/4 over length s, then (γ(s) − v)·g ≤ −sβ/5. The law of cosines then puts γ(s) outside D(x_z, Δ₂) once s > 5d₀Δ₂/(β(Δ₂ − d₀)).
  - So the turning is ≥ β/4 within length L = 6/β.
  - This bounds the count by 2π(L + 2)·4/β·4 = O(1/β²) ≈ 2·10⁷.
  - (If the perimeter of K is < 2L, then |S ∖ D| ≤ 2L anyway.)

Total: C_bad ≤ 10⁸ for β = 1/100. The constant is huge, but it is explicit and absolute.

## 4. Region I: τ ≤ √3/2 − 2β, giving 18/13

For p ∈ S ∖ D, the possible good-neighbour directions on one side lie between elevation −arcsin τ (the exception) and +arcsin β (T). That arc is ≤ arcsin(√3/2 − 2β) + arcsin β = 58.35° < 60°.

For p ∈ D, a reverse rung has elevation arcsin((v − p)·u_p), where the dot product lies in (0, τ + β]. So the arc is ≤ arcsin(τ + β) = 58.87° < 60°.

If τ < 0 (tiny t), everything lies within (0, arcsin β] ∪ {−arcsin τ}, which is also < 60°.

So every vertex has ≤ 1 good neighbour per side, and e(S) ≤ |S| + C_bad. Lemma 1.1 with k = 1 gives 18/13. ∎

## 5. Regions II and III: the window, and above it

### 5.1 Mixed T-edges are O(1) when t ≥ 0.87

Take v ∈ S ∖ D and z ∈ D with (z − v)·u_v ∈ (0, β). Suppose ∂K turned by Θ < t − arcsin β (≥ 0.886 rad in Region II) over length 2 from v on z's side. Then some γ(s) ∈ K has |γ(s) − v| = 1 and |γ(s) − z| ≤ Θ + arcsin β < t ≤ dist(z, K), a contradiction.

With 3-fold overlap on each side, #mixed-T ≤ 2·2·3·2π/0.886 < 90.

From here on, "rows" means:
- the **K-row** S ∖ D, with pure T-edges among its own points;
- the **D-row** S ∩ D, likewise;
- rungs join the two rows.

### 5.2 Region II: τ ≥ √3/2 + 3β, so s ≤ 0.444

**(R1) At most one rung per vertex.**
- For v: the two candidate positions v − τu ± s u^⊥ are 2s < 1 apart.
- For z: two partners v, v′ would satisfy |v − v′| ≤ 2s + 3β = 0.918 < 1.

**(R2) Proximity lemma.** Let (v₀, z₀) be a rung. Suppose v₁ is v₀'s right T-neighbour and v₁ has a good rung to z′, and z₁ is z₀'s right T-neighbour. Then z′ = z₁.

Proof: z′ − z₁ = (e₁ − e₂) + (off(v₁) − off(v₀)), so |z′ − z₁| ≤ 3β + √2β + 2s ≤ 2s + 4.5β = 0.933 < 1. ∎

**(R3) Parallel rungs.**
- Rungs with the same vector c satisfy c·u_v = −τ exactly, so u_v is one of the two solutions u^±.
- Lemma 2.2 forbids equal u's. So no three rungs are parallel, and two parallel rungs have normals exactly 2θ₀ apart.
- A rhombus of unit edges v₀v₁z₁z₀ forces parallel rungs: the equilateral quadrilateral argument, since v₁ and z₀ are the two points of C(v₀,1) ∩ C(z₁,1).
- The T-edge v₀v₁ is good, so a rhombus needs 2θ₀ ≤ β. **So rhombi exist only if τ ≥ cos(β/2).**

**Ownership count.**
- Every non-rung vertex on a T-path belongs to the nearest rung vertex to its left, if there is one.
- Rung r = (v, z) owns k vertices in the K-row and d in the D-row, and the edges: itself plus the right-going T-edges out of the vertices it owns.
- So edges(r) ≤ 1 + k + d, with equality only if both rows' walks reach a further rung vertex ("both reach").
- Unowned segments have ratio ≤ 1.

Consequences:
- By (R2), if both reach and k = 1, then v₁'s rung is z₁, so d = 1 and the gap is a rhombus. Symmetrically d = 1 forces k = 1.
- So a both-reach gap is either a rhombus (1,1), with ratio 3/2, or has k, d ≥ 2, with ratio ≤ 5/4.
- If there are no rhombi (τ < cos(β/2)), then e(S) ≤ (5/4)|S| + C.
- Otherwise pair each rhombus rung with its successor, which is not a rhombus rung by (R3): (3 + 1 + k′ + d′)/(2 + k′ + d′) ≤ 8/6, or ≤ 5/4 if the successor does not reach on both sides.

Hence e(S) ≤ (4/3)|S| + C_bad + 90. Lemma 1.1 gives 54/37.

### 5.3 Region III: τ ∈ (√3/2 − 2β, √3/2 + 3β), so θ₀ ∈ (26.36°, 32.22°)

**Corner lemma.** Let v ∈ S ∖ D have a rung and a second Δ₂-partner w′. Then ∠(u, u′) ≥ min(2θ₀, 90° − θ₀) ≥ 52.7°:
- if z is an exception for w′ too, then u and u′ are reflections of each other (exact identity);
- otherwise (z − v)·u′ > 0 while ∠(z − v, u) = 180° − θ₀.

Both u and u′ are K-normals at v, and 52.7° > 360°/7, so **at most 6** such v.

Every other rung K-vertex has Δ₂-degree 1; call the set of these P₁. Then:
- each K-vertex has ≤ 2 rungs;
- by (T1), T-edges number ≤ |S|;
- so e(S) ≤ |S| + 2|P₁| + 12 + C_bad.

The weighted LP of §1 gives 7/5.

**This regime genuinely needs P₁.** A single centre w with a run of Δ₂-partners on C(w, Δ₂) and a run of diametral partners on C(w, Δ), with θ₀ = 30° + arcsin(1/(2Δ₂)), is locally a "hexagonal strip": K-row degree 4, D-row degree 2, average 3.

## 6. Degenerate regime: Δ > 1.94Δ₂ and n ≥ 4 give μ(Δ₂) ≤ n + 1

Elementary, with no black box.

1. **No two disjoint diametral pairs.**
   - For disjoint pairs (x, x′) and (z, z′), the four cross distances satisfy Σ|a − b|² = 2Δ² + 4|m − m′|² ≥ 2Δ², where m, m′ are the midpoints.
   - With ≤ 1 diametral cross pair the sum is ≤ Δ² + 3Δ₂² < 1.8Δ², a contradiction. So ≥ 2 cross pairs are diametral.
   - If the two are disjoint, they form a Δ-rhombus, whose longer diagonal is ≥ √2Δ. Contradiction.
   - If they share a vertex, there is an equilateral triangle of side Δ, and the fourth point lies on its 60° arc, so one of its distances to the triangle is ≥ 2Δ sin 15° = 0.518Δ > Δ₂, and hence equals Δ. Contradiction.
   - So the diameter graph is a star or a triangle.
   - A triangle with n ≥ 4 is impossible: the circumradius Δ/√3 exceeds Δ₂, and a diametral edge to a 4th point is disjoint from the opposite side.
2. **So D = {y} ∪ A with A = Diam(y). Put B = X ∖ D ⊂ K.**
   - The lens D(y, Δ₂) ∩ D(a, Δ₂) has diameter ≤ 0.49Δ₂, so there are no Δ₂-pairs in B.
   - A lies on an arc of C(y, Δ) with pairwise chords ≤ Δ₂, so e_{Δ₂}(A) ≤ 1 (only the two extreme points can be at distance Δ₂).
   - |ya| = Δ for a ∈ A.
3. **Incidence count between B and W = {y} ∪ A.**
   - Each C(w, Δ₂) ∩ K is a single arc: spindle convexity, and K has diameter < Δ₂.
   - An interior point of a nondegenerate arc lies on no other W-circle (equal-radius tangency would force the same circle).
   - So Σ_b deg(b) ≤ |B| + #corners + #degenerate arcs ≤ |B| + |W|.
   - Hence μ(Δ₂) ≤ 1 + |B| + |A| + 1 = n + 1.

`degen_check.py` builds 300 adversarial star configurations: B at every corner of K plus many arc points, with the extreme A-pair forced. It checks that no distance lies in (Δ₂, Δ). The maximum of μ(Δ₂) − n is 0.

## 7. Numerical sanity (`classify_a2.py`)

**Odd ring (CDL skeleton).** m = 201, τ = 0.99997, θ₀ = 0.45°, Region II.
- Every rung has dot product exactly −τ (asserted to 1e−6).
- At most 1 rung per vertex.
- e(S)/|S| = 0.5.

**Even ring (9/7 skeleton).** Region I.
- There are bad edges at m ≤ 200. This is expected: Δ₂ ≈ 30 < 1/β. The lemmas are asymptotic in Δ₂, as stated.

**Constants** (`a2_checks.py`):

| check | value | required |
|---|---|---|
| Region I, S ∖ D same-side arc | 58.35° | < 60° |
| Region I, D same-side arc | 58.87° | < 60° |
| Region II, proximity bound 2s + 4.5β | 0.933 | < 1 |
| Region III, minimum corner angle | 52.7° | > 51.43° |

## 8. Status / gaps (honest)

- **Proved (modulo [Ve87], [HP]):** Theorem A2, i.e. L ≤ 54/37 ≈ 1.4595 for CDL Problem 1.6.
  - This is unconditional. The window √3/2 < t ≤ 1 and the degenerate regime are both closed.
  - The proof is written at the level of "careful notes", not refereed.
- **Points a referee should check:**
  - (i) The turning-measure overlap bookkeeping in §3 and §5.1: multiplicities, and the one-sided arc from a corner point.
  - (ii) Every place where "Δ₂ ≥ 10⁴" is used: 2/Δ₂ < β/2, and the lens-lemma hypothesis.
  - (iii) (T2) together with the rightward walk on T-cycles in §5.2. A cycle owned by a single rung has k ≥ 3, which is harmless.
  - (iv) In §6, the connectedness of C(w, Δ₂) ∩ K and "∂K is covered by W-arcs". B-circles strictly contain K because diam K < Δ₂.
- **Weakest link:** Region II with 1 − τ ≤ β²/8 (t extremely close to 1). There, rhombi with normals exactly 2θ₀ ≤ β apart are allowed, and the pairing gives 4/3. Excluding the pattern "rhombus + (2,2)-gap" would lower the bound to 36/25 = 1.44. After that the bottleneck is 7/5 (Region III).
- **Not improved:** the lower bound 9/7. The gap is now [1.2857, 1.4595].
- **Novelty:**
  - (VS): applying Vesztergombi to S, which makes every k < 3/2 suffice.
  - The exact rung angle, with its no-three-parallel-rungs and 2θ₀ rhombus rigidity.
  - The degenerate-regime bound μ(Δ₂) ≤ n + 1.
  - Checked against angle_A, frontier.md and the forum as of 2026-09-22: none of these appear there. No new literature search was done today.

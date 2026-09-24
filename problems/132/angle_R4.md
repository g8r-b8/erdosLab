# Erdős #132 / CDL Problem 1.6: Angle R4, improving L ≤ 54/37

Date: 2026-09-23. Scratch files are in `scratchpad/R4/`, and the scripts are `scripts/r4_*.py`.

**Result: L ≤ 18/13 ≈ 1.3846.** The previous bound was 54/37 ≈ 1.4595, and the lower bound is 9/7 ≈ 1.2857.

- Two independent referee passes found no gap. One sub-agent checked Region II. For Region III, one sub-agent checked the τ ≠ √3/2 case and a second, independent one checked the τ = √3/2 case.
- The exact constants and the LP certificates are checked in rationals:
  - `scripts/r4_regionII_checks.py` (17 assertions);
  - `scripts/r4_regionIII_checks.py` (18 assertions);
  - `scripts/r4_lp_checks.py`.
- The argument stays inside the WRITEUP_A2 framework. The only black box is still [Ve87].

**Notation.** It follows `WRITEUP_A2.md`: δ = 1, β = 1/100, t = Δ − Δ₂, τ = t − (1−t²)/(2Δ₂), θ₀ = arccos τ, s = sin θ₀, K = ∩_{w∈X} D(w,Δ₂), D = diametral endpoints, S = points with a Δ₂-partner, R = X∖S, r = |R|, and u_p. The K-row is S∖D and the D-row is S∩D. T-edges, rungs, good and bad edges are as in WRITEUP_A2. **P₁ = conv X, as in WRITEUP_A2.** The set of points of Δ₂-degree 1 is called **Q** here, with p := |Q|. WRITEUP_A2 §4.2/§7.3 also calls that set "P₁", which clashes with conv X.

## 1. Where 54/37 loses

| regime | e(S) bound in WRITEUP_A2 | LP | value | new |
|---|---|---|---|---|
| I: τ ≤ √3/2 − 2β | \|S\| + C | Lemma 4.1, k = 1 | 18/13 | unchanged |
| III: √3/2 − 2β < τ < √3/2 + 3β | \|S\| + 2\|Q\| + C | Lemma 4.2 | 7/5 | \|S\| + \|Q\| + C → 18/13 (§3) |
| II-rest: √3/2 + 3β ≤ τ < cos(β/2) | (5/4)\|S\| + C | Lemma 4.1 | 36/25 | \|S\| + \|Q\| + C → 18/13 (§2) |
| II-near-resonant: cos(β/2) ≤ τ ≤ 1 | (4/3)\|S\| + C | Lemma 4.1 | **54/37** | \|S\| + \|Q\| + C → 18/13 (§2) |
| II-high: τ > 1 | \|S\| + C | Lemma 4.1 | 18/13 | unchanged |
| degenerate Δ > 1.94Δ₂ | — | — | n + 1 | unchanged |

There are two separate losses.

1. **Loss 1: rungs were charged without their Δ₂ cost (fixed here).** Every δ-edge that WRITEUP_A2 charges beyond |S| is a rung (the rhombus rungs and the (2,2) both-reach rungs of §7.2, and the second rungs of Region III). The K-end of each such rung has Δ₂-degree 1, apart from O(1) exceptions, or else the rung costs a T-edge elsewhere.
   - So in *every* regime e(S) ≤ |S| + |Q| + C.
   - This is paid on the μ(Δ₂) side by μ(Δ₂) ≤ |Q| + (3/2)(|S| − |Q|) + C_V, the Lemma 4.2 argument.
   - The LP with weights 10/13 and 3/13 gives (18/13)s − (2/13)p + (18/13)r ≤ 18n/13 (`r4_lp_checks.py`).
2. **Loss 2: the term 6r in (E), μ(δ) ≤ e(S) + 6r (open).** This is now the *entire* gap between 18/13 and 9/7.
   - The exact identity is μ(δ) = e(S) + Σ_{y∈R}(deg y + m_y)/2, where m_y := #δ-neighbours of y in S.
   - Suppose deg y + m_y ≤ 2c for all but o(n) of the y ∈ R. Then min{μ(Δ₂), μ(δ)} ≤ (3c/(2c+1))·n + o(n) (Region I form; see the table in `r4_lp_checks.py`).
   - The values are: 2c = 12 gives 18/13, 10 gives 15/11, 9 gives 27/20, 8 gives 4/3, 6 gives **9/7**.
   - In ienjoymath's construction e(S) = |S|, and the patch points have m_y = 0 and deg ≤ 6, i.e. 2c = 6. That is why it sits exactly at 9/7.

## 2. Region II (τ ≥ √3/2 + 3β) gives e(S) ≤ |S| + |Q| + C

Region II satisfies τ > cos(π/6), so θ₀ < 30°. It has t ≤ 1 whenever rungs exist, and t ≥ τ. By (R1), rungs form a matching.

**Lemma A (corner lemma, all τ ≤ 1).** Let v ∈ S∖D have a rung partner z, with c := z − v, c·u_v = −τ and |z w_v| = Δ. Let w′ ≠ w_v be another Δ₂-partner of v, and put u′ := (w′−v)/Δ₂. Exactly one of the following holds.
- **(i)** |zw′| ≤ Δ₂. Then c·u′ ≥ 1/(2Δ₂) > 0 by Lemma 3.2(b), and ∠(c,u_v) = π − θ₀, so ∠(u_v,u′) > π/2 − θ₀.
- **(ii)** |zw′| = Δ. Then c·u′ = −τ by Lemma 3.2(c) with w′, and u′ ≠ u_v. So u′ = u*, the reflection of u_v in ℝc, and ∠(u_v,u′) = 2θ₀. Call v a *double* vertex.

These cases are exhaustive because |zw′| ∈ [0,Δ₂] ∪ {Δ}.

Both u_v and u′ lie in N_K(v), and normal cones at distinct points of ∂K have disjoint interiors. K has nonempty interior because open chords between points of X∖D lie inside every disc.

Say a vertex is of type (i) if *any* of its extra partners is of type (i). In Region II a type-(i) cone is wider than π/3, so **there are at most 5 type-(i) vertices**. Every other rung K-end of Δ₂-degree ≥ 2 is double.

**Lemma B.** Let z ∈ D, w ∈ X with |zw| = Δ, ŵ := (w−z)/Δ, and let y ∈ X satisfy |zy| = 1 and η := (y−z)·ŵ. Then |yw|² = Δ² + 1 − 2Δη.
- If η < (Δ² − Δ₂² + 1)/(2Δ), then |yw| > Δ₂, hence |yw| = Δ.
- The threshold is at least t/2, and in fact at least t.

**Lemma C (all of Region II).** A double vertex's rung partner z has **no T-neighbour at all**, pure or mixed.

*Proof.*
1. Let w = w_v and let w* be the partner in direction u*. Then |zw| = |zw*| = Δ.
2. The angle between ŵ (from z) and u_v is ≤ arcsin(1/Δ). The same bound holds between ŵ* and u*.
3. ∠(u*,u_v) = 2θ₀, and ∠(u_v,u_z) ≤ β because the rung is good.
4. Let z₁ be a T-neighbour, so (z₁−z)·u_z ∈ (0,β). Then η and η* are small enough that Lemma B forces |z₁w| = |z₁w*| = Δ.
   - Near resonance (2θ₀ ≤ β): η, η* ≤ sin(arcsin β + 2.5β) < 0.04 < t/2.
   - On all of Region II, the referee's sufficient condition 2s_max + ε/τ_min < 1 − 1/(2Δ₂) holds exactly, with ε = β + arcsin β + 2/Δ₂. This uses sin 2θ₀ < cos θ₀ for θ₀ < 30°.
5. But z ≠ z₁ are then two points of C(w,Δ) ∩ C(w*,Δ). These two points are ≥ √3Δ > 1 apart. Contradiction. ∎

**Count.**
- By (T1) every vertex has T-degree ≤ 2 (one T-neighbour per side), so #T-edges ≤ |S|.
- By Lemma C, the D-ends of double rungs have T-degree 0. They are distinct, because rungs form a matching. So

  #T-edges ≤ |S| − #double rungs.

- Hence e(S) ≤ #T-edges + #rungs + C_bad ≤ |S| + #(non-double rungs) + C_bad ≤ |S| + |Q| + 5 + C_bad.

This makes the ownership walks, (R2)/(R2-sym), the rhombus pairing and the sub-regime split of §7.2 unnecessary. For τ > 1 there are no rungs at all.

Checks: `r4_regionII_checks.py`. Part A checks the constants exactly, Part B the LP exactly, Part C Lemma B (500 exact and 2000 random exact instances), Part D is an adversarial search against Lemma C (2·10⁵ samples, minimum margin 0.97), and Part E covers all of Region II (minimum margin 0.088).

## 3. Region III (√3/2 − 2β < τ < √3/2 + 3β) gives e(S) ≤ |S| + |Q| + C

**Facts used.**
- **(F1)** Good edges are T-edges or rungs, since τ > 2β.
- **(F2)** (T1) holds for all T-edges, pure and mixed. Write e_T = (#used T-slots)/2, where each vertex has a left slot and a right slot.
- **(F3)** Lemma 7.1 of WRITEUP_A2 is also valid in Region III, because t ≥ τ > 0.846 and Θ < t − arcsin β < π/3. So **#mixed T-edges < 76**.
- **(F4)** The §7.3 corner lemma: all but ≤ 6 rung K-vertices have Δ₂-degree 1.

Let q₁ and q₂ be the numbers of K-vertices with exactly 1 and 2 rungs. Then #rungs ≤ q₁ + 2q₂ and p ≥ q₁ + q₂ − 6. It therefore suffices to prove

  **e_T ≤ |S| − q₂ + C**,

since then e(S) ≤ e_T + #rungs + C ≤ |S| + q₁ + q₂ + C ≤ |S| + |Q| + C.

### 3.1 The case τ > √3/2 (2s < 1)

The two rung positions v + o_±(u_v) are 2s < 1 apart, so q₂ = 0.

### 3.2 The case τ < √3/2 (2s > 1): slot killing

**Lemma III.1.** Let v have rungs z = v + o₊(u_v) and z′ = v + o₋(u_v). Then z′ has no T-neighbour (pure or mixed) on the side of z, and z has none on the side of z′.

*Proof.*
1. o₊ − o₋ = 2s·u_v^⊥, and ∠(u_v,u_{z′}) ≤ β.
2. A T-neighbour y of z′ on the z-side therefore satisfies ∠(y−z′, z−z′) ≤ γ := β + arcsin β < 0.0201.
3. Hence |y−z|² ≤ (2s−1)² + 4s(1−cos γ) < 0.005 < 1.
4. Also y ≠ z, since |zz′| = 2s ≠ 1. This contradicts δ = 1. ∎

**Injectivity.**
- Suppose v and v̄ are double vertices with the same z′ and the same side. Then |z̄ − z| ≤ 2s·2β < 1, so z̄ = z.
- So v̄ is the mirror image of v in the line zz′. That gives (v̄−z′)·u_{z′} ≤ −τ cos β + s sin β < 0, contradicting Lemma 3.2(a).
- Hence the 2q₂ killed slots are distinct, and e_T ≤ |S| − q₂.

Float worst case: |y − z| ≤ 0.069.

### 3.3 The exact case τ = √3/2 (s = ½, θ₀ = 30°)

**Setting.** A double-rung vertex v has rungs z′ = v + o₋(u_v) and z = v + o₊(u_v). Then z − z′ = u_v^⊥, so v z′ z is an equilateral triangle of side 1. Its base z′z is a D–D δ-edge.

**Base determines apex.** The other point of C(z,1) ∩ C(z′,1) is v̄ = z′ − τu_v + ½u_v^⊥. It has (v̄ − z′)·u_{z′} ≤ −τ cos β + ½ sin β < 0, contradicting 3.2(a). Hence:
- a base is the base of at most one triangle;
- triangles whose base is a bad edge number ≤ C_bad.

From now on we consider triangles with a *good* base, which is a pure D-row T-edge.

**Goal.** e_T ≤ |S| − q₂ + C. Then e(S) ≤ e_T + ρ + C_bad ≤ |S| + q₁ + q₂ + C ≤ |S| + p + C.

#### (R) Rows are cyclic orders

**Claim.** A pure K–K T-edge vv′ joins two points of S∖D that are adjacent in the cyclic order of S∖D on ∂K. The same holds for D–D T-edges on ∂P₁.

*Proof.*
1. Take coordinates with v = (0,0), v′ = (1,0) and u_v = (sin ε, cos ε), u_{v′} = (−sin ε′, cos ε′), where ε, ε′ ∈ (0, arcsin β).
2. u_v and u_{v′} are inward normals of K. For the D-row, u_z is an inward normal of P₁ by 3.2(a).
3. So the cap of the body on the side y ≤ 0 lies in the triangle {y ≤ 0, y ≥ −x tan ε, y ≥ (x − 1) tan ε′}.
4. That triangle has x ∈ [0,1] and depth ≤ tan(arcsin β). Every point of it is within √(¼ + tan²) < 1 of v or v′.
5. So the boundary arc from v to v′ on that side contains no other row point. ∎

**Consequences.**
- The arc between T-neighbours runs in the "right" traversal direction.
- e_TK = N_K − B_K and e_TD = N_D − B_D, where B_K and B_D count cyclically adjacent pairs of the row that are not joined by a pure T-edge. (Rows with N ≤ 2 are O(1).)
- Therefore **e_T ≤ |S| − B_K − B_D + 75**, using #mixed < 76 from Lemma 7.1.

#### (B′) A D-row component lies on one circle

**Claim.** Let Z be the component of the pure D–D T-graph that contains a good base z′z of the triangle at v, and put w := w_v. Then:
- Z ⊂ C(w, Δ);
- consecutive vertices of Z are at angle exactly α₁ := 2 arcsin(1/(2Δ)), all in the same (right) rotational sense;
- Z spans an angle ≤ π/3, so Z is a path, not a cycle.

*Proof.*
1. **Start.** |zw| = |z′w| = Δ by the rung definition.
2. **Interior vertices have narrow normal cones.** Let z_k have both a left and a right T-neighbour. Write n = cos φ·u + sin φ·u^⊥ with u = u_{z_k}.
   - Inwardness against z_{k+1} gives sin(ε₁ − φ) ≥ 0.
   - Inwardness against z_{k−1} gives sin(ε₂ + φ) ≥ 0.
   - Hence φ ∈ [−ε₂, ε₁], and N_{P₁}(z_k) lies in the cap of radius arcsin β around u.
3. **Induction step.** Suppose |z_k w| = Δ. Then w is a diametral partner of z_k.
   - Since |y − w| ≤ Δ for every y ∈ X, the vector ŵ_k := (w − z_k)/Δ is an inward P₁-normal at z_k.
   - For interior z_k, η := (z_{k+1} − z_k)·ŵ_k = sin(ε₁ − φ) ∈ [0, sin(2 arcsin β)], and sin(2 arcsin β) < 0.0201.
   - Also |z_{k+1} − w|² = 1 + Δ² − 2Δη.
   - This exceeds Δ₂² because η < (Δ² − Δ₂² + 1)/(2Δ) = t + (1 − t²)/(2Δ) ≥ t > 0.866. The identity and the fact t < 1 are checked in the script.
   - There are no distances in (Δ₂, Δ), so |z_{k+1} w| = Δ.
4. **Induct outwards.**
   - Going right from z: z has left neighbour z′, so z (and each later vertex) is interior whenever it has a right neighbour.
   - Going left from z′: symmetric.
   - So every vertex of Z lies on C(w, Δ).
5. **Angles and span.**
   - The two points of C(w,Δ) ∩ C(z_k,1) are at angles ±α₁. The right T-neighbour is the one in the right rotational sense, because ŵ_k is within arcsin β of u_{z_k}.
   - Points of X are pairwise ≤ Δ apart, so the chord 2Δ sin(θ/2) ≤ Δ gives θ ≤ π/3.
   - Monotone steps cannot close up into a cycle within π/3. ∎

#### (W) One centre per component

**Claim.** If A and B are triangles whose good bases lie in the same Z, then w_A = w_B =: w.

*Proof.*
1. By (B′) applied to A, the base z′_B z_B of B lies on C(w_A, Δ). By the rung definition it also lies on C(w_B, Δ).
2. If w_A ≠ w_B, then w_A is the mirror image of w_B in the line z′_B z_B.
3. Let a := (w_B − z_B)/Δ and let e be the unit vector along the base. Then a·e = sin∠(a, u_{v_B}), which is tiny: the angle at w_B in the triangle w_B v_B z_B is ≤ arcsin(1/Δ).
4. The mirror a* of a satisfies a·a* = 2(a·e)² − 1 < 0. So (w_A − z_B)·a = Δ·a·a* < 0.
5. But w_B is a diametral partner of z_B and w_A ∈ X, so (w_A − z_B)·a ≥ 0 by the 3.2(a) argument. Contradiction. ∎

#### (Arc) The arc between consecutive apexes lies on ∂K

**Setting.** The apex v_A lies on C(w, Δ₂), on the perpendicular bisector of its base (which passes through w), so at the base-midpoint angle. Let A and B be consecutive triangles in Z, B to the right, with bases (z_i, z_{i+1}) and (z_{i+k}, z_{i+k+1}). Then:
- the apexes are at angular distance kα₁;
- kα₁ ≤ π/3 − α₁ < π/3;
- kα₁ ≥ α₂ := 2 arcsin(1/(2Δ₂)), because |v_A v_B| ≥ 1.

**Spindle convexity.** For x ∈ X, D(x, Δ₂) ∩ C(w, Δ₂) = {θ : cos(θ − θ_x) ≥ |wx|/(2Δ₂)}. This is one arc of width ≤ π, or the whole circle if x = w.
- It contains v_A and v_B, which are less than π apart, so it contains the short arc γ_AB between them.
- Hence γ_AB ⊂ K ⊂ D(w, Δ₂), and therefore γ_AB ⊂ ∂K.

#### (Rigid) The K-path is forced along the arc

Follow pure right K–K T-edges from v_A = v_0: v_0, v_1, ….

**Normal fact (flagged step).** For every v_i ∈ γ_AB with v_i ≠ v_B we have u_{v_i} = ŵ_i := (w − v_i)/Δ₂.
- At v_0 this holds because w = w_{v_A} by definition.
- At a point v_i in the relative interior of γ_AB, K contains the circle arc on both sides of v_i and K ⊂ D(w, Δ₂). So every inward normal n satisfies (y − v_i)·n ≥ 0 for y on the arc on both sides of v_i. This forces n ∥ ŵ_i: the normal cone is the single ray ŵ_i.
- u_{v_i} is an inward normal of K at v_i (K ⊂ D(w_{v_i}, Δ₂)), so it equals ŵ_i.

**Step.** Let v_i ∈ γ_AB, v_i ≠ v_B, and let v_{i+1} be its pure right T-neighbour. Let v* be the right point of C(v_i,1) ∩ C(w,Δ₂).
1. v* lies on γ_AB. Otherwise v_B would be at angle in (0, α₂) from v_i, giving |v_i v_B| < 1.
2. Take coordinates (r, u) with u = ŵ_i and r the right tangent. Then v_{i+1} − v_i = (cos ψ, sin ψ) with ψ < arcsin β, since u_{v_i} = ŵ_i.
3. v_{i+1} ∈ K ⊂ D(w, Δ₂) forces ψ ≥ ψ* := arcsin(1/(2Δ₂)), where ψ* is the elevation of v*.
4. Suppose ψ > ψ*. Let n = (sin φ, cos φ) be the inward normal u_{v_{i+1}}. Since the T-edge is good, |φ| ≤ β.
   - v_i ∈ K gives (v_i − v_{i+1})·n = −sin(ψ + φ) ≥ 0, so φ ≤ −ψ < 0.
   - v* ∈ K (by (Arc)) gives (v* − v_{i+1})·n = (cos ψ* − cos ψ) sin φ + (sin ψ* − sin ψ) cos φ ≥ 0.
   - But the first term is < 0 (cos ψ* > cos ψ and sin φ < 0), and the second is < 0 (sin ψ* < sin ψ and cos φ > 0). Contradiction.
5. Hence v_{i+1} = v*. Float search B2: 0 violations in 2·10⁵ samples.

**This also settles the thin-K / "long way round" worry.** A pure right T-neighbour of a point of γ_AB is always the next arc point at angle α₂. It can never lie on the other branch of ∂K.

**Consequence.** The path moves along γ_AB in steps of exactly α₂. It cannot jump past v_B, since that would put a point within distance < 1 of v_B. So it reaches v_B only if jα₂ = kα₁ for some j ≥ 1. Otherwise it stops at a vertex b ∈ γ_AB ∖ {v_B} that has no pure right K T-edge. (b's right slot is either unused or used by a mixed T-edge.)

#### (Arith) The path cannot land exactly on v_B

Since α₂ > α₁, jα₂ = kα₁ forces k > j. Then j(α₂ − α₁) = (k − j)α₁ ≥ α₁, so

  kα₁ = jα₂ ≥ α₁α₂/(α₂ − α₁) = 1/(1/α₁ − 1/α₂).

Bounds on f(R) := 1/α_R:
- Since arcsin x ≤ x + x³/(6(1 − x²)), we have R − 1/(23R) ≤ f(R) ≤ R for R ≥ 10⁴.
- Hence 1/α₁ − 1/α₂ ≤ t + 1/(23Δ₂).
- At τ = √3/2, t < √3/2 + 1/(2Δ₂) < 0.8661 (because t < 1).

So kα₁ ≥ 1/(t + 1/(23Δ₂)) > 1/0.8662 > π/3. This contradicts kα₁ < π/3. (The script checks 0.8662 < 3/π.)

Therefore **every pair (A, B) of consecutive triangles in the same Z yields a K-break b_{AB} ∈ [v_A, v_B)**. The pair (b_{AB}, succ b_{AB}) is counted in B_K.

Float check B3: the nearest approach |jα₂ − kα₁|·Δ₂ is 1.7·10⁻⁶. That is nonzero, as expected (it is the case j = k at Δ₂ = 10⁶). Physically it forces a break.

#### (Count) One break per triangle

Break pairs are identified by their left elements b, so distinct b give distinct pairs. It remains to show that the b_{AB} are distinct.

**The half-open arcs [v_A, v_B) ⊂ ∂K are pairwise disjoint (flagged step).**
- **Same Z.** The arcs are consecutive intervals on one circle, so they are disjoint.
- **Different Z, same centre w.** The angular ranges of the components are disjoint: a point of one component strictly inside the range of another would be at angle < α₁, hence distance < 1, from one of its points. So the apex arcs are disjoint.
- **Different centres w ≠ w′.** Suppose γ ⊂ C(w,Δ₂) and γ′ ⊂ C(w′,Δ₂) are arcs of ∂K sharing a point p.
  - If p were in the relative interior of γ, then near p ∂K equals γ on both sides. The nondegenerate arc γ′ ∋ p contains a small piece of ∂K on one side of p, which would lie on both circles, forcing w = w′.
  - So p is an endpoint of both arcs. For the half-open arcs, p ≠ v_B and p ≠ v_{B′}, so p = v_A = v_{A′}.
  - Each K-vertex has only one triangle, so A = A′, and the two arcs are the same one.

Hence **B_K ≥ Σ_Z (m_Z − 1)**, where m_Z is the number of good-base triangles in Z.

Each Z with m_Z ≥ 1 is a path by (B′). Its right end has no right pure D T-edge, which gives an unjoined adjacent D-pair; these pairs are distinct for distinct Z. So **B_D ≥ #{Z : m_Z ≥ 1}**.

Adding up:
- B_K + B_D ≥ Σ_Z m_Z ≥ q₂ − C_bad;
- e_T ≤ |S| − q₂ + C_bad + 75;
- **e(S) ≤ |S| + q₁ + q₂ + C ≤ |S| + p + C.** No o(|S|) term is needed.

#### Conclusion of 3.3

Region III (every τ, including τ = √3/2) gives e(S) ≤ |S| + p + C.

The LP uses μ(Δ₂) ≤ p + (3/2)(s − p) + C_V and μ(δ) ≤ s + p + 6r + C. With weights 10/13 and 3/13 it gives (18/13)n + C. Together with regionII_draft (18/13), Region I (18/13) and the degenerate case (n + 1), this yields **L ≤ 18/13**.

**Steps that deserve a second referee:**
1. (Rigid): the normal fact u_{v_i} = ŵ_i at relative-interior arc points.
2. (Count): arc disjointness across different centres.
3. Lemma 7.1 (#mixed < 76) is now a required ingredient in Region III, through (R).

**Second referee's additions to §3.3.** These are presentation fixes; no step changes.
- **(B′).** Say explicitly why ε₂ ∈ (0, arcsin β): the elevation of z_{k−1} relative to u_{z_k} comes from b ∈ (0,β) on the incoming T-edge. Also note that there is no wrap-around.
- **(W).** There is a simpler route: a·e = ±1/(2Δ) exactly (a chord of C(w_B,Δ)), so a·a* < 0.
- **(Rigid).** State that "right" means the same rotational sense (about w) in both rows. This holds because u_v, u_z and ŵ agree up to O(β).
- **(Arith).** The margin is wide: kα₁ ≥ 1/0.8662 ≈ 1.154 > π/3 ≈ 1.047.

## 4. Theorem

**Theorem (R4).** Every n-point set X ⊂ ℝ² satisfies min{μ(Δ₂), μ(δ)} ≤ (18/13)·n + C₀ for an absolute constant C₀. Hence **L ≤ 18/13**.

*Proof.*
1. The degenerate regime and small Δ₂ are handled as in WRITEUP_A2 §8 and §4.
2. In the nondegenerate regime, §§2–3 together with Region I (WRITEUP_A2 §6) give e(S) ≤ |S| + |Q| + C in every τ-regime. (In Region I, Q = ∅ suffices.)
3. The two sides are bounded by μ(Δ₂) ≤ p + (3/2)(s − p) + C_V ([Ve87] applied to S∖Q, or Hopf–Pannwitz) and μ(δ) ≤ s + p + 6r + C.
4. With weights 10/13 and 3/13 these combine to 18n/13 + C. ∎

18/13 exceeds 9/7, so this is consistent with ienjoymath's lower bound. The construction lies in Region I (t/δ → 0) and has e(S) = |S|. The Region I LP is tight for the inputs used: the adversary takes s = 12n/13 with r-points of δ-weight 6. Such weight-6 R-points do not occur in the construction.

## 5. Beyond 18/13: the 6r term

TODO: results of the local R-neighbour route and the global Euler route (sub-agents running).

## 6. Consistency with ienjoymath's construction

- **Region.** The even-m ring core has t = 2 − 2cos(π/m) ≈ 4ε at δ = g ≈ 2√ε, so t/δ → 0 and τ → 0⁺ (Region I). None of the new lemmas (§§2–3) apply there, and nothing new is claimed about Region I.
- **Region I accounting.** The server–vertex δ-edges u_i–v_{i+m/2}, u_i–v_{i+m/2+1} are exceptions for u_i (v_{i+m/2} is antipodal to u_i's partner v_i). So e(S) = 2m = |S|, which is exactly Region I's k = 1.
- **Δ₂-degrees.** Servers have Δ₂-degree 2 and ring vertices have Δ₂-degree 4, so Q = ∅ and μ(Δ₂) = 1.5|S| is tight.
- **The patch.** Patch points have m_y = 0 and deg ≤ 6, so they contribute 3 each, not 6. That gap is precisely Loss 2.

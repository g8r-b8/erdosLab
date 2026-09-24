# Erdős #132 / CDL Problem 1.6: Angle R4, improving L ≤ 54/37

Date: 2026-09-23. Scratch files are in `scratchpad/R4/`, and the scripts are `scripts/r4_*.py`.

**Result: L ≤ 15/11 ≈ 1.3636.** The previous bound was 54/37 ≈ 1.4595, and the lower bound is 9/7 ≈ 1.2857. The proof has two steps:
1. 54/37 → 18/13: fix Loss 1, §§2–4.
2. 18/13 → 15/11: the R-neighbour lemma, §5.1 and Appendix A.

Region II alone gives 4/3.

- Referee passes found no gap in any step:
  - Region II: one referee;
  - Region III, τ ≠ √3/2: one referee;
  - Region III, τ = √3/2: two independent referees;
  - Theorems N1 and N2: one independent referee (REF4).
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
   - Suppose deg y + m_y ≤ 2c for all but o(n) of the y ∈ R. Then:
     - in Region I, where e(S) ≤ |S|, min{μ(Δ₂), μ(δ)} ≤ (3c/(2c+1))·n + o(n);
     - with the |Q| term (Regions II and III), the bound is max{4/3, 3c/(2c+1)}·n, because the weight on μ(Δ₂) must be at least 2/3.
   - The values are (`r4_lp_checks.py`):

     | 2c | Region I | with the \|Q\| term |
     |---|---|---|
     | 12 | 18/13 | 18/13 |
     | 10 | 15/11 | 15/11 |
     | 9 | 27/20 | 27/20 |
     | 8 | 4/3 | 4/3 |
     | 6 | 9/7 | 4/3 |

   - So 9/7 also needs the Δ₂ side to be sharpened in Regions II and III.
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

**Theorem (R4).** There is an absolute constant C₀ such that every n-point set X ⊂ ℝ² satisfies

  min{μ(Δ₂), μ(δ)} ≤ (15/11)·n + C₀.

Hence **L ≤ 15/11**. Two regime refinements:
- In the nondegenerate regime with τ ≥ √3/2 + 3β (Region II), the bound improves to (4/3)·n + C₀.
- The degenerate regime Δ > 1.94Δ₂ gives n + 1.

*Proof.*
1. **Degenerate regime and small Δ₂.** These are handled as in WRITEUP_A2 §8 and §4. The O(1) exceptional sets of the lemmas below only enlarge C₀.
2. **Step 1: bounding e(S).** In the nondegenerate regime, §§2–3 together with Region I (WRITEUP_A2 §6) give e(S) ≤ |S| + |Q| + C in every τ-regime. (In Region I, Q = ∅ already suffices.)
3. **Step 2: bounding the R-contribution.** By Theorem N1 (§5.1, Appendix A), deg y + m_y ≤ 10 for all but O(1) points y ∈ R. Hence μ(δ) = e(S) + Σ_{y∈R}(deg y + m_y)/2 ≤ s + p + 5r + C.
4. **The Δ₂ side.** μ(Δ₂) ≤ p + (3/2)(s − p) + C_V. This is [Ve87] applied to S∖Q, or Hopf–Pannwitz when S∖Q contains no diametral pair.
5. **Combining.** With weight 8/11 on μ(Δ₂) and 3/11 on μ(δ), the bound is (15/11)(s + r) − (1/11)p + C ≤ 15n/11 + C.
6. **Region II.** Theorem N2 gives 4r in place of 5r, and weights 2/3 and 1/3 then give 4n/3 + C. ∎

If one uses only step 1 together with the trivial bound (E), μ(δ) ≤ e(S) + 6r, the weights 10/13 and 3/13 give 18/13.

**Consistency.** The new bound 15/11 exceeds 9/7, so it agrees with ienjoymath's lower bound.
- The construction lies in Region I (t/δ → 0) and has e(S) = |S|.
- Its patch points have deg + m ≤ 6, not 10.
- The LP adversary for 15/11 uses s = 10n/11 together with R-points of δ-weight 5 (deg + m = 10). Whether such R-points can make up Θ(n) of a near-extremal set is exactly the open question of §5.1.

## 5. Loss 2: the 6r term

Both routes attack Loss 2 (§1).

### 5.1 Local route: the R-neighbour lemma (PROVED; independent referee REF4: correct)

The full proof is in Appendix A. The scripts are:
- `scripts/r4_nb_exact.py`: the 60-digit sharpness example;
- `scripts/r4_nb_search.py`: adversarial search, 0 violations;
- `scripts/r4_nb_ring16_check.py`: the construction;
- `scripts/r4_nb_referee_checks.py`: the referee's exact Fraction checks with rigorous Taylor bounds.

**Theorem N1 (every τ).** All but fewer than 7·10⁷ points y ∈ R have m_y ≤ 4, hence deg y + m_y ≤ 10.

*Why.*
- Points in R∩D have all their neighbours in an open half-plane, so deg + m ≤ 6.
- R∖D ⊂ int K, because ∂K ⊂ ∪_{w∈X} C(w,Δ₂).
- **Lemma T (thin K).** If some point of ∂K near y is off the 232-arc around y's nearest boundary point, then K lies in a 400 × 9 box, so |X∖D| = O(1). This uses that every point p ∈ ∂K has an outer normal (p − w)/Δ₂ with w ∈ X, and Δ ≤ 1.94Δ₂.
- **Lemma BT.** A large turning of the 464-arc happens for O(1) points y, by Lemma 3.4.
- **Lemma F (flat case).** K is locally the subgraph of a concave function with |f′| ≤ tan(1/50). So every S-neighbour of y lies in an open arc of < 183°, and at most 4 points can sit in such an arc 60° apart.

**Theorem N2 (t > √3/2 + tan(1/50), in particular Region II).** deg y + m_y ≤ 8 for all but O(1) points y.

**Consequence.** μ(δ) ≤ e(S) + 5r + C ≤ s + p + 5r + C. The LP with weights 8/11 on μ(Δ₂) and 3/11 on μ(δ) gives s-coefficient 15/11, r-coefficient 15/11 and p-coefficient −1/11. Hence

  **min{μ(Δ₂), μ(δ)} ≤ (15/11)·n + C for every n-point set, and ≤ (4/3)·n + C in Region II.**

**Sharpness of the local method.** For τ < √3/2, an exact "chord-midpoint fan" has deg = 6 and m = 4 locally:
- K-row points p± are the ends of a chord of length 2 of C(w,Δ₂), and y is its midpoint;
- two D-points sit at y ± e/2 + (√3/2)n, using the identity c_D(0) = τ.

So 10 is the best that local arguments can give there. Whether Θ(n) such y can exist, with D-points in S and μ(Δ₂) large, is open.

The natural next step is a charging argument: each 10-point y is the inner apex of a unit D–D edge z₁z₂, and y ↦ z₁z₂ is injective.

### 5.2 Global route: Euler/peel (PARTIAL; one sub-agent's proof, not refereed)

Report: `scratchpad/R4/global/GLOBAL_report.md`. Scripts: `scripts/r4_global_*.py`. Write Def := 3n − μ(δ) = 3 + 3c + Σ_f(|f|−3) for the plane δ-graph with c components.

**Peel identity (exact).** For a vertex set A,

  Def(H) = Def(H − A) + 3|A| − e(A) − e(A, V∖A).

**Theorem G (proved by the sub-agent).** Let a penny-graph component have a convex outer cycle C of k vertices, with turning ≤ 2 arcsin β at each vertex and at most one inward edge per vertex. Then

  Def ≥ 2k − #chords − (2π − 3).

- The proof uses Euler's formula on each inner component, the non-crossing of rungs, and a telescoping projection of the inner boundary walk onto the chord directions.
- It is tight on ienjoymath's even-m core (Def = 2|S| exactly).

**Conditional corollaries.** These assume hypothesis H: the K-row and the D-row are each a single unbroken T-cycle.
- τ > 1: 9/7.
- Region II: 4/3.

**Obstructions.**
1. Gaps in the rows. A "gap lemma" charging each row break O(1) would remove H.
2. Region I "zigzag stack". Here K-vertices have two outward exceptions and the rows are stacked. It defeats any one-layer count: S–R edges exceed the first-layer R-deficit. The multi-layer peel pays for it, so a proof must be multi-layer.
3. Thin, path-like deep peel components.

### 5.3 Conjecture (equivalent to L = 9/7 given (VS))

Def(δ-graph) ≥ 2|S| − o(n), i.e. μ(δ) + (4/3)μ(Δ₂) ≤ 3n + o(n).

- Evidence: the even-m core has equality (m = 8…80). The odd-m core has Def − 2|S| = m. The full construction has Def − 2|S| ≈ √(12P).
- All adversarial searches (angle D, R4) found nothing below.
- In Regions II and III the Δ₂ side would also need sharpening, because of the |Q| term (see the table in §1).

## 6. Consistency with ienjoymath's construction

- **Region.** The even-m ring core has t = 2 − 2cos(π/m) ≈ 4ε at δ = g ≈ 2√ε, so t/δ → 0 and τ → 0⁺ (Region I). None of the new lemmas (§§2–3) apply there, and nothing new is claimed about Region I.
- **Region I accounting.** The server–vertex δ-edges u_i–v_{i+m/2}, u_i–v_{i+m/2+1} are exceptions for u_i (v_{i+m/2} is antipodal to u_i's partner v_i). So e(S) = 2m = |S|, which is exactly Region I's k = 1.
- **Δ₂-degrees.** Servers have Δ₂-degree 2 and ring vertices have Δ₂-degree 4, so Q = ∅ and μ(Δ₂) = 1.5|S| is tight.
- **The patch.** Patch points have m_y = 0 and deg ≤ 6, so they contribute 3 each, not 6. That gap is precisely Loss 2.

## Appendix A. The R-neighbour lemma: Theorems N1 and N2 (full proofs, transcribed from the local-route sub-agent; the degree-1 set is renamed Q)

Notation as in problems/132/WRITEUP_A2.md. δ = 1, R := Δ₂, t = Δ − Δ₂, τ = t − (1−t²)/(2R),
K = ∩_{w∈X} D(w,R), D = diametral endpoints, S = points with a Δ₂-partner, R-set := X∖S (written 𝓡 below
to avoid a clash with the radius R). For y ∈ 𝓡: deg y = δ-degree, m_y = #δ-neighbours of y in S.
Standing hypotheses: nondegenerate regime (Δ ≤ 1.94R) and R ≥ 10⁴ (WRITEUP §4). No assumption on τ.
Checks: `r4_nb_exact.py` (Fractions/Decimal; rigorous rational bounds for sin/cos/tan), `r4_nb_search.py`
(float screening), `r4_nb_ring16_check.py` (consistency with ienjoymath's construction).

### A.0. Identity, LP, and trivial cases

(0.1) μ(δ) = e(S) + Σ_{y∈𝓡} (deg y + m_y)/2. (S–S edges: e(S); S–𝓡 edges: Σ m_y; 𝓡–𝓡 edges: Σ (deg y − m_y)/2.)

(0.2) LP. With μ(Δ₂) ≤ 1.5s − 0.5p + C and μ(δ) ≤ s + p + c·r + C (p = |Q|), the best weight is
λ = max{(c−1)/(c+½), 2/3} (λ ≥ 2/3 is needed to kill the p-term), giving
min{μ(Δ₂),μ(δ)} ≤ max{4/3, 3c/(2c+1)}·n + C. Values: 2c = 6 → 4/3 (NOT 9/7; 9/7 only without the Q term),
8 → 4/3, 9 → 27/20, 10 → 15/11, 12 → 18/13. Without the Q term (Region I, e(S) ≤ |S| + C) the value is
3c/(2c+1) for all c ≥ 1. [r4_nb_exact.py (2)]

(0.3) Structure of 𝓡.
 (a) y ∈ 𝓡 ∩ D: by Lemma 3.2(a) every other point lies in the open half-plane {(x−y)·u_y > 0}; neighbours are
     pairwise ≥ 60° apart as seen from y, so deg y ≤ 3 and deg y + m_y ≤ 6.
 (b) ∂K ⊂ ∪_{w∈X} C(w,R): a point x ∈ K with |x−w| < R for all (finitely many) w ∈ X is interior. Hence a point
     of X∖D on ∂K has a Δ₂-partner, i.e. is in S. With X∖D ⊂ K (Lemma 3.1a): 𝓡∖D ⊂ int K, S∖D = (X∖D) ∩ ∂K.
 (c) For y ∈ 𝓡∖D put h := dist(y, ∂K) > 0. Every S-neighbour q of y is ∉ int K: either q ∈ S∖D ⊂ ∂K, or
     q ∈ D, and D ∩ K = ∅ with dist(q,K) ≥ t (Lemma 3.1c). The segment [y,q] leaves K at some b ∈ ∂K, so
     h ≤ |y b| ≤ 1; for q ∈ D even h ≤ |yb| ≤ 1 − |bq| ≤ 1 − t.
     **Consequently if h > 1 then m_y = 0 and deg y + m_y ≤ 6.** This is the answer to "points near D-points but
     far from ∂K": such points do not exist — a D-neighbour forces h ≤ 1 − t, and points with h > 1 have no
     S-neighbour at all. All y with h ≤ 1 (whatever their D-neighbours) are treated below; D-neighbours enter
     only through constraint (F3).

Throughout §§1–3, y ∈ 𝓡∖D with h ≤ 1; p₀ ∈ ∂K is a nearest boundary point, n₀ := (p₀ − y)/h is an outer
normal of K at p₀, H₀ := {x : (x − p₀)·n₀ ≤ 0} ⊃ K, and ℓ₀ = ∂H₀.

Turning (WRITEUP §3): for a closed boundary arc γ, turning(γ) = length of the union of the normal cones at all
points of γ, endpoints' full cones included. Lemma 3.4 (multiplicity): Σ turning(γ_i) ≤ 2πM if every boundary
point is in ≤ M of the arcs.

Small-K clause: if per(K) < 464 then diam K < 232, and |X∖D| ≤ (2·232+1)² (disjoint discs of radius ½), so
|𝓡∖D| = O(1). Assume per(K) ≥ 464 from now on and define
  **γ_y := the closed arc of ∂K consisting of points at arc-length distance ≤ 232 from p₀.**

### A.1. Thin-K lemma

**Lemma T.** If some b ∈ ∂K ∩ B̄(y,1) is not in γ_y, then diam K < 409, hence |X∖D| ≤ 410² = O(1).

*Proof.* Let ν_b be any outer normal of K at b, H_b = {(x − b)·ν_b ≤ 0} ⊃ K, ℓ_b = ∂H_b. Note
dist(y, ℓ₀) = h ≤ 1 and dist(y, ℓ_b) ≤ |yb| ≤ 1. Both arcs of ∂K from p₀ to b have length > 232 (b ∉ γ_y).

Case ν_b = n₀. Then ℓ₀ = ℓ_b: otherwise one of p₀ ∈ ℓ₀, b ∈ ℓ_b lies strictly outside the other half-plane, but
both are in K ⊂ H₀ ∩ H_b. So [p₀, b] ⊂ K ∩ ℓ₀ ⊂ ∂K is a boundary arc of length |p₀b| ≤ 2 < 232. Contradiction.

Case ν_b not parallel to n₀. ℓ₀, ℓ_b meet at A and Z := H₀ ∩ H_b is a closed cone with apex A and opening
θ = π − ∠(n₀, ν_b) ∈ (0, π). y ∈ Z has distance ≤ 1 to both bounding lines, so |yA| ≤ 1/sin(θ/2) (the set of
points of the cone at distance ≤ 1 from both lines is a rhombus with far vertex on the bisector at distance
1/sin(θ/2)). p₀ ∈ ℓ₀ ∩ K ⊂ ℓ₀ ∩ Z, which is the boundary ray of Z on ℓ₀; similarly b lies on the other ray.
|Ap₀| ≤ |Ay| + |yp₀| ≤ 1 + 1/sin(θ/2), and likewise |Ab|. Let H⁺ be the closed half-plane bounded by line p₀b
containing A; Z ∩ H⁺ = triangle T(A, p₀, b). If [p₀,b] ⊂ ∂K we are done as before; otherwise the line p₀b meets
∂K only in p₀, b and ∂K ∩ H⁺ is one of the two arcs from p₀ to b. K ∩ H⁺ ⊂ T is convex, so by monotonicity of
perimeter, length(∂K ∩ H⁺) + |p₀b| ≤ per(T), i.e. length ≤ |Ap₀| + |Ab| ≤ 2 + 2/sin(θ/2).
 (i) θ ≥ 1°: length ≤ 2 + 2/sin(0.5°) < 231.2 < 232 [exact, (3)]. Contradiction.
 (ii) θ < 1°: fatness step below.
Case ν_b = −n₀ (strip): Z is a strip of width ≤ 2 containing y; treat as (ii) with θ = 0.

*Fatness step (θ < 1° or strip).* Let e be the bisector direction of Z (the strip direction if θ = 0), e⊥ a unit
normal to it; "level" = coordinate along e, "height" = coordinate along e⊥. The cross-section of Z at level s has
height-length w(s) = w(s_y) + 2 tan(θ/2)(s − s_y) (s_y the level of y, sign chosen so the cone opens towards
increasing s; if K extends to the other side the cross-sections are only smaller), and
w(s_y) = (d₁ + d₂)/cos(θ/2) ≤ 2/cos(θ/2) =: w_y, d_i ≤ 1 the distances from y to the two lines.
Let [E₋, E₊] be the range of levels of K (it contains s_y), L := E₊ − E₋ > 0 (K has interior), and W the
height-width of K. Then W ≤ w_y + 2 tan(θ/2)·L, and L ≤ diam K ≤ 2R (K ⊂ D(w,R)).
Pick a, a′ ∈ K at levels E₋, E₊ and let m := (E₋+E₊)/2. The section of K at level m is a segment of positive
length (m is an interior level of a convex body with interior) with top p_top and bottom p_bot.
Let n_top = cos φ·e⊥ + sin φ·e be an outer normal at p_top. From n_top·(a − p_top) ≤ 0 and n_top·(a′ − p_top) ≤ 0,
with a − p_top = −(L/2)e + v_a e⊥, a′ − p_top = (L/2)e + v_{a′} e⊥, |v_a|, |v_{a′}| ≤ W:
  −(L/2) sin φ + v_a cos φ ≤ 0,  (L/2) sin φ + v_{a′} cos φ ≤ 0.
If cos φ ≤ 0 these force v_a, v_{a′} ≥ 0 ≥ v_a + v_{a′} (the midpoint of a a′ is in K, at level m, below p_top),
so v_a = v_{a′} = 0, sin φ = 0, n_top = −e⊥, and then K lies on or above the line through p_top, contradicting
p_bot ≠ p_top below it. So cos φ > 0 and |tan φ| ≤ 2W/L. Same at p_bot with −e⊥.
Every boundary point lies on some C(w,R) with w ∈ X (0.3b), and (p − w)/R is then an outer normal at p (K ⊂ D(w,R)).
Choose such w_top for p_top and w_bot for p_bot and use their normals above. Then
  (w_bot − w_top)·e⊥ = (p_bot − p_top)·e⊥ + R(n_top·e⊥ − n_bot·e⊥) ≥ −W + 2R cos φ*,  tan φ* = 2W/L,
while |w_bot − w_top| ≤ Δ ≤ 1.94R. Suppose L ≥ 400. Then tan φ* ≤ 2w_y/400 + 4 tan(θ/2) and
W ≤ w_y + 4R tan(θ/2), so (2R cos φ* − W)/R ≥ 2(1 − tan²φ*/2) − 4 tan(θ/2) − w_y/10⁴ > 1.94 + 0.0229
[exact rational bounds, (3)], contradicting 1.94R. Hence L < 400, W ≤ w_y + 800 tan(0.5°) < 9.0, and
diam K ≤ L + W < 409. ∎

Remark. The argument only uses boundary points of K and centres in X, so corners and non-X boundary points are
covered. It kills the "three-row strip" obstruction: a K of width ≈ √3 has length < 409.

### A.2. Big turning is O(1)

**Lemma BT.** Fix ε₀ ∈ (0, π/6). #{y ∈ 𝓡∖D : h ≤ 1, turning(γ_y) > ε₀} < 2πM/ε₀ with M = 468².

*Proof.* If b ∈ γ_y then |b − p₀| ≤ 232 (chord ≤ arc), so |b − y| ≤ 233. The points y are ≥ 1 apart, so for a
fixed b at most (2·233.5)² ≤ 468² of them (disjoint discs of radius ½ in B(b, 233.5)). Apply Lemma 3.4. ∎
With ε₀ = 1/50: < 6.9·10⁷ [(3)].

### A.3. Flat-case lemma

**Lemma F.** Suppose ∂K ∩ B̄(y,1) ⊂ γ_y and turning(γ_y) ≤ ε₀ < π/6; put ε := tan ε₀. Use coordinates with
origin p₀, x-axis t₀ ⊥ n₀, z-axis n₀; so y = (0, −h). Then there is a concave f on [−231, 231] with f(0) = 0,
f ≤ 0, |f(x)| ≤ ε|x|, whose graph is contained in γ_y ⊂ ∂K, and
  U := B̄(y,1) ∩ {z < f(x)} ⊂ int K.
Writing a neighbour as q = y + (sin ψ, cos ψ) (ψ measured from n₀):
 (F1) every neighbour q ∉ int K (in particular every S-neighbour, and every D-neighbour) has
      cos ψ ≥ h + f(sin ψ) ≥ h − ε|sin ψ| > −ε;
 (F2) every neighbour q ∈ S∖D (K-row) has cos ψ = h + f(sin ψ) ∈ [h − ε, h];
 (F3) every neighbour z ∈ D (whether in S or in 𝓡) has cos ψ ≥ h + t + f(sin ψ) ≥ h + t − ε;
 (F4) every neighbour in int K has cos ψ < h.

*Proof.* The normal set N(γ_y) is an arc of S¹ of length ≤ ε₀ containing n₀ ∈ N(p₀). Parametrise γ_y by arc length
s ∈ [−232, 232], γ(0) = p₀. Every one-sided tangent is perpendicular to a normal in N(γ_y), hence within ε₀ of
±t₀, and (orienting) γ′(s)·t₀ ≥ cos ε₀ > 0. So x(s) := γ(s)·t₀ is strictly increasing with |x(±232)| ≥ 232 cos ε₀
> 231, and γ_y ⊃ graph of a function f on [−231, 231] with |f′| ≤ tan ε₀ = ε a.e.; f(0) = 0 so |f(x)| ≤ ε|x|.
f ≤ 0 because K ⊂ H₀. At each graph point the outer normals have positive n₀-component (≥ cos ε₀), and K lies in
the corresponding supporting half-plane, so K lies below every supporting line of the graph: f is concave.
U is convex (disc ∩ strict hypograph of a concave function; x-range of B̄(y,1) is [−1,1] ⊂ [−231,231]),
contains y (−h < 0 = f(0)), and U ∩ ∂K = ∅, since ∂K ∩ B̄(y,1) ⊂ γ_y and γ_y ∩ B̄(y,1) lies on the graph, where
z = f(x). A connected set meeting int K and missing ∂K lies in int K. So U ⊂ int K.
(F1) q ∈ B̄(y,1), q ∉ int K ⇒ q ∉ U ⇒ q_z ≥ f(q_x), i.e. cos ψ − h ≥ f(sin ψ); and h > 0.
(F2) q ∈ ∂K ∩ B̄(y,1) ⊂ graph ⇒ equality.
(F3) The graph point g = (sin ψ, f(sin ψ)) is in K and lies directly below z (by F1), so
     t ≤ dist(z, K) ≤ |z − g| = cos ψ − h − f(sin ψ).
(F4) a neighbour in int K is not on ∂K; if it had cos ψ ≥ h it would satisfy z ≥ 0 ≥ f(x), i.e. lie on or
     above the graph; points strictly above a graph point are outside K (K below the supporting line), and
     points on the graph are in ∂K. So cos ψ − h < f(sin ψ) ≤ 0. ∎
(Every neighbour of y is in int K, in S∖D ⊂ ∂K, or in D; there is no fourth kind, by 0.3b.)

### A.4. Theorem N1 (all τ-regimes)

**Theorem N1.** In the nondegenerate regime with R ≥ 10⁴, for all but C₁ < 7·10⁷ + 2·10⁵ points y ∈ 𝓡:
m_y ≤ 4, hence deg y + m_y ≤ 10. Consequently μ(δ) ≤ e(S) + 5r + C, and via (0.2):
Region I (e(S) ≤ |S| + C): 15n/11 + C; Regions II/III (e(S) ≤ |S| + |Q| + C): 15n/11 + C.

*Proof.* y ∈ 𝓡∩D: deg + m ≤ 6 (0.3a). y ∈ 𝓡∖D with h > 1: m = 0 (0.3c). Otherwise h ≤ 1:
 – if some point of ∂K ∩ B̄(y,1) is outside γ_y: Lemma T, |𝓡∖D| ≤ 410² in total (or the small-K clause);
 – else if turning(γ_y) > ε₀ = 1/50: Lemma BT, < 6.9·10⁷ such y;
 – else Lemma F applies. By (F1) every S-neighbour has cos ψ > −ε, i.e. |ψ| < π/2 + arcsin ε: an open arc of length
   π + 2 arcsin ε < 4π/3. Neighbours are pairwise ≥ 60° apart (distinct points of X are ≥ 1 apart), and an open
   arc of length < 240° contains at most 4 such points. So m_y ≤ 4. ∎
Only ε₀ < π/6 is used here, so N1 is uniform and holds in Region I, II, III, at τ = √3/2, for τ ≤ 0 and τ > 1.
Nothing about rungs or τ enters.

### A.5. Theorem N2 (t > √3/2 + ε; in particular Region II)

**Theorem N2.** Let ε₀ ∈ (0, π/6), ε = tan ε₀, and suppose t > √3/2 + ε (this implies t > ½ + 2ε).
Then for all but C(ε₀) = 2π·468²/ε₀ + 410² + 465² points y ∈ 𝓡: m_y ≤ 3, and deg y = 6 ⇒ m_y ≤ 2. So
deg y + m_y ≤ 8, μ(δ) ≤ e(S) + 4r + C and, with e(S) ≤ |S| + |Q| + C, the bound is **4n/3 + C**.
In Region II (τ ≥ √3/2 + 3β) take ε₀ = 1/50: ε < 0.0201 < 0.03, and t ≥ √3/2 + 3β (WRITEUP §7.1: t ≥ τ if t ≤ 1,
else t > 1), so the hypothesis holds with an absolute constant.

*Proof.* Exceptions as in N1; so let y be in the flat case of Lemma F, h ≤ 1.
(i) At most one D-neighbour. By (F3) a D-neighbour has cos ψ ≥ t − ε > √3/2, i.e. |ψ| < 30°; two neighbours at
    angular distance ≥ 60° cannot both lie in this open 60° arc. (This applies to all D-neighbours, in S or not.)
(ii) At most one K-row neighbour with ψ ∈ [0, π) and at most one with ψ ∈ (−π, 0]. If 0 ≤ ψ₁ < ψ₂ with
    ψ₂ − ψ₁ ≥ 60° are both K-row, then by (F1) ψ₂ < 90° + arcsin ε, so (ψ₁+ψ₂)/2 ∈ [30°, 91.2°] and
    (ψ₂−ψ₁)/2 ∈ [30°, 45.6°], hence cos ψ₁ − cos ψ₂ = 2 sin((ψ₁+ψ₂)/2) sin((ψ₂−ψ₁)/2) ≥ ½ > ε,
    contradicting (F2) (both cosines lie in [h−ε, h]).
So m_y ≤ 3, and m_y = 3 means the S-neighbours are one D-point at ψ_D (|ψ_D| < 30°) and K-row points K₊ (ψ ≥ 0),
K₋ (ψ ≤ 0).
(iii) deg y = 6 and m_y = 3 is impossible. Six neighbours pairwise ≥ 60° apart are exactly 60° apart: at
    ψ_D + 60°k. K₊, K₋ are two of the five directions ψ_D ± 60°, ψ_D ± 120°, ψ_D + 180°, with cosines in
    [h − ε, h] (F2), so they differ by at most ε.
  • ψ_D + 180°: cos = −cos ψ_D < −√3/2 < −ε, contradicting (F1).
  • {ψ_D + 60°, ψ_D − 60°}: |cos(ψ_D+60°) − cos(ψ_D−60°)| = √3|sin ψ_D| ≤ ε, so |sin ψ_D| ≤ ε/√3 and
    cos(ψ_D ± 60°) ≥ ½cos ψ_D − (√3/2)|sin ψ_D| ≥ ½(1 − ε²/3) − ε/2 ≥ ½ − ε. By (F2) h ≥ ½ − ε, and then
    (F3) gives cos ψ_D ≥ h + t − ε ≥ ½ + t − 2ε > 1. Contradiction.
  • {ψ_D + 120°, ψ_D − 60°} (or the mirror pair {ψ_D − 120°, ψ_D + 60°}): cos(ψ_D − 60°) = −cos(ψ_D + 120°), so
    both lie in an interval of length ε only if |cos(ψ_D+120°)| ≤ ε/2; hence h ≤ 3ε/2 by (F2). As
    ψ_D + 120° ∈ (90°, 150°), this forces ψ_D + 120° ≤ 90° + arcsin(ε/2), i.e. ψ_D + 60° ∈ (30°, 31.2°]. The
    neighbour at ψ_D + 60° is not in S (m = 3); cos(ψ_D+60°) > ½ > h, so by (F4) it is not in int K, hence it is
    in D, and (F3) puts a second D-neighbour in |ψ| < 30°, contradicting (i).
  • {ψ_D + 120°, ψ_D − 120°}: both angles have |ψ| > 90° (|ψ_D| < 30°), so their cosines are < 0 and h ≤ ε by
    (F2). The neighbours at ψ_D ± 60° are not in S; one of them has |ψ| ≤ 60°, so cos ψ ≥ ½ > h, it is not in
    int K by (F4), hence in D, and (F3) gives a second D-neighbour in |ψ| < 30°: contradiction with (i).
  • Two directions on the same side are excluded by (ii).
Hence deg 6 ⇒ m ≤ 2 (deg + m ≤ 8), and deg ≤ 5 ⇒ deg + m ≤ 5 + 3 = 8. ∎

Regimes. N2 needs t > √3/2 + ε with ε > 0 fixed: it holds uniformly in Region II (and for τ > 1). In Region III
with τ ≥ √3/2 + η it holds with ε₀ = arctan(η/2), but the exceptional count ~ 1/η is not uniform as η → 0.
It gives nothing for τ ≤ √3/2 (Region I, lower Region III, τ = √3/2): there only N1 (deg + m ≤ 10) is proved.

### A.6. Sharpness for τ < √3/2 (N1 cannot be improved locally)

Single-arc model (K = D(w,R) near y, |y − w| = R − h). A neighbour at angle ψ from the outward radial satisfies
|q − w|² = (R−h)² + 1 + 2(R−h)cos ψ, so
  K-row ⇔ cos ψ = c_K(h) := h + (h² − 1)/(2(R−h)),  D-feasible ⇔ cos ψ ≥ c_D(h) := h + t + ((h+t)² − 1)/(2(R−h)),
with the identity **c_D(0) = τ** and c_D increasing in h [(1)]. Two D-neighbours 60° apart need c_D(h) ≤ cos 30°,
so m = 4 or (deg 6, m 3) needs τ < √3/2. For τ < √3/2 it is attained:

Example (verified in 60-digit Decimal, r4_nb_exact.py (4)). w = 0, R = 10⁴. On C(w,R) take chords [p₋,p₊] of
length 2 (every other chord position); y := chord midpoint (depth R − √(R²−1) ≈ 1/(2R)); e := (p₊−p₋)/2,
n := y/|y|; z± := y ± e/2 + (√3/2)n; a± := y ± e/2 − (√3/2)n. Then |y p±| = |y z±| = |y a±| = 1, all pairwise
distances are ≥ 1, the z± lie on C(w, R + t) with t = 0.86598790…, τ = √3/2 − 5.0·10⁻⁵, dist(z±, D(w,R)) = t,
and a± ∈ int D(w,R). So every y has deg 6, two K-row neighbours and two D-feasible neighbours: deg + m = 10 as
soon as z± ∈ S. In this one-centre fan the z's have no Δ₂-partner (they are 𝓡∩D, so there m_y = 2); whether
Θ(n) such y with z± ∈ S can exist globally is OPEN. Locally the constraint on the z's is only dist(z,K) ≥ t, so
the same local picture is admissible for every t ≤ √3/2 − O(1/R), i.e. throughout Region I.
Structure of a 10-point (flat case, deg 6, m 4): the order is K,D,D,K at ψ ≈ −90°, −30°, 30°, 90° (within O(ε₀)),
h ≤ O(ε), |z₁z₂| = 1, and p₋z₁, z₂p₊ are unit edges. y is the inner apex of the equilateral triangle on the
D–D edge z₁z₂, so y ↦ z₁z₂ is injective. A charging argument on this structure is the next step for Region I.

At τ = √3/2 exactly: N1 holds. In the pure single-arc case deg 6 ∧ m 4 is impossible (c_D(h*) > c_D(0) = √3/2),
but small corners (turning ≤ ε₀) are not excluded by the argument above, so nothing better than 10 is proved there.

### A.7. Checks
- ienjoymath ring construction (n = 60, 120, 250): all 𝓡-points have m_y = 0 and deg + m ≤ 6.
- Float search (172 random local boundaries with corners, R = 10⁴): never m > 4 when turning < 30°. With turning
  < 30°, τ ≥ √3/2 gives max deg + m = 8 and τ < √3/2 gives max 9 (10 needs the exact chord depth; see §6).
  10 appeared only with large turning, which is the O(1) case.

**Referee fixes (REF4), which override the text above where they differ.**
1. **Lemma T, the case cos φ ≤ 0.** Adding the two inequalities gives v_a + v_{a′} = 0. So the midpoint of aa′ is p_top, and a, a′ lie on the supporting line.
   - If cos φ < 0, then p_bot violates the half-plane.
   - If cos φ = 0, the two inequalities contradict each other, since L > 0.
   - Either way, cos φ > 0.
2. **The bound on |X∖D| in the thin case.** Use the box L < 400, W < 9, which gives fewer than 5106 points. The bound diam K < 409 on its own does not give 410².
3. **The remark "only ε₀ < π/6 is used".** This needs the sharp form |ψ| < 90° + ε₀ of (F1). The coarse form needs tan ε₀ < 1/2. Neither matters at ε₀ = 1/50.
4. The degree-1 set is renamed from P₁ to Q.

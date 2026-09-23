# An upper bound below 3/2 for Problem 1.6 of Clemen–Dumitrescu–Liu

**Write-up of angle A2 (Erdős #132).** Date: 2026-09-23.

- Sources: `angle_A2.md` (the notes) and `REFEREE_A2.md` (verdict: correct with fixable gaps).
- Numerical verification: `scripts/writeup_a2_checks.py`. It uses exact rationals and rational interval arithmetic (58 assertions, all passing). A tag **[Ck]** marks each inequality checked in section Ck of that script.
- §10 lists how each referee gap was closed.

---

## 1. Statement

For a finite set X ⊂ ℝ² we use the following notation.

- Δ = Δ(X) is the diameter, Δ₂ the second-largest distance, and δ the minimum distance.
- μ(d) is the number of unordered pairs of X at distance d.

Clemen, Dumitrescu and Liu [CDL, Problem 1.6] ask for

  L := limsup_{n→∞} max_{|X|=n} min{μ(Δ₂), μ(δ)}/n.

Known bounds:
- Lower bound: 9/7 (ienjoymath, 2026).
- Upper bound: 3/2, from Vesztergombi's bound μ(Δ₂) ≤ 3n/2.

**Theorem.** There is an absolute constant C₀ such that every n-point set X ⊂ ℝ² satisfies

  min{μ(Δ₂), μ(δ)} ≤ (54/37)·n + C₀.

Hence L ≤ 54/37 ≈ 1.4595 < 3/2.

## 2. Black boxes

- **[Ve87]** K. Vesztergombi, *On large distances in planar sets*, Discrete Math. **67** (1987) 191–198.
  - Statement used: in every m-point planar set, the second-largest distance occurs at most (3/2)m times.
  - We use it in the weaker form μ₂ ≤ (3/2)m + C_V with an absolute constant C_V ≥ 0. Any additive constant in the original statement therefore only changes C₀.
  - We have not read the original paper. CDL (arXiv 2505.04283v5, §2.2) quote it as stated, with no condition on m.
  - The convex-position 4m/3 bound is in the different paper Vesztergombi, Discrete Math. **57** (1985) 129–145. It is not used here.
- **[HP]** H. Hopf and E. Pannwitz (1934): in every m-point planar set the diameter occurs at most m times.
- **Trivial facts.**
  - A point has at most 6 points of X at distance δ.
  - If K ⊂ K′ are compact convex sets, then per(K) ≤ per(K′).
  - The normal cones of a convex body at distinct boundary points have disjoint interiors, and together they cover the circle of directions S¹.

Nothing else is used. In particular, the structural propositions of Vesztergombi used by CDL (their Props 1–8) are not needed.

## 3. Notation and set-up

Scale so that **δ = 1**. Put

- t := Δ − Δ₂ > 0;
- τ := t − (1 − t²)/(2Δ₂);
- **β := 1/100**.

Basic facts about τ **[C2]**:
- τ − t = (t² − 1)/(2Δ₂).
- Hence τ ≤ t when t ≤ 1, and τ > 1 exactly when t > 1.

X has **no distance in (Δ₂, Δ)**. We use the following sets and objects.

- **D**: the set of endpoints of diametral pairs. Every point of D is a vertex of P₁ := conv X.
- **S**: the set of points having a Δ₂-partner. **R** := X ∖ S, and r := |R|.
- **K** := ∩_{w∈X} D(w, Δ₂). This is a convex "ball polygon".
- e(S) := the number of δ-pairs inside S.
- **The regime split.**
  - The *degenerate regime* is Δ > 1.94Δ₂ (§8).
  - The *nondegenerate regime* is Δ ≤ 1.94Δ₂ (§§4–7).

**Lemma 3.1 (ball polygon).**
- (a) X ∖ D ⊂ K.
- (b) S ∖ D ⊂ ∂K.
- (c) dist(z, K) ≥ t for z ∈ D.

*Proof.*
- (a) A point y ∉ D has all its distances ≤ Δ₂, because there are none in (Δ₂, Δ).
- (b) If v ∈ S ∖ D has a partner w with |vw| = Δ₂, then v ∈ K ∩ C(w, Δ₂) ⊂ ∂K.
- (c) If z ∈ D and |zx| = Δ, then K ⊂ D(x, Δ₂). ∎

**Direction field.** For each p ∈ S, fix one unit vector u_p as follows.

- For p ∈ S ∖ D: choose a Δ₂-partner w_p and put u_p := (w_p − p)/Δ₂. This is an inward normal of K at p, because K ⊂ D(w_p, Δ₂).
- For p ∈ S ∩ D: choose a diametral partner x_p and put u_p := (x_p − p)/Δ. This is an inward normal of P₁ at p.

**Lemma 3.2 (exact identities).** Let y ∈ X.

- (a) If p ∈ S ∩ D, then (y − p)·u_p ≥ |y − p|²/(2Δ) > 0 for y ≠ p.
- (b) If p ∈ S ∖ D, then either
  - (y − p)·u_p ≥ |y − p|²/(2Δ₂) ("normal"), or
  - |y − w_p| = Δ, so that y ∈ D ("exception").
- (c) In the exception case with |y − p| = 1, we have **exactly** (y − p)·u_p = −τ. Hence y − p = −τu_p ± s u_p^⊥ with s := √(1 − τ²). Such exceptions exist only when τ ≤ 1.

*Proof.*
- (a) and (b): expand (y − p)·u_p with the law of cosines, and use |y − x_p| ≤ Δ and |y − w_p| ∈ [0, Δ₂] ∪ {Δ}.
- (c): (1 + Δ₂² − Δ²)/(2Δ₂) = −τ is a polynomial identity in t **[C2]**. ∎

**Lemma 3.3 (no common normal).** If p ≠ q both lie in S ∖ D, then u_p ≠ u_q.

*Proof.* Neither point is in D, so each is normal for the other: (q − p)·u_p > 0 and (p − q)·u_q > 0. These two inequalities cannot hold with u_p = u_q. ∎

**Good edges, T-edges and rungs.** A δ-edge pq inside S is **good** if ∠(u_p, u_q) ≤ β, and **bad** otherwise. For a good edge put e = q − p, a := e·u_p and b := −e·u_q. Then |a + b| = |e·(u_p − u_q)| ≤ β.

If τ > 2β, each good edge is exactly one of the following two kinds.
- **T-edge:** a, b ∈ (0, β).
- **Rung:** one end v ∈ S ∖ D sees the other end z ∈ S ∩ D as an exception. Then (z − v)·u_v = −τ and (v − z)·u_z ∈ [τ − β, τ + β].

Why this is a dichotomy:
- An exception target lies in D, and points of D see everything as normal (3.2a). So both ends cannot be exceptions.
- One end an exception with the other in (0, β) would give |a + b| ≥ τ − β > β.

Two further facts:
- **(T1)** Each p has at most one T-neighbour on each side of the line ℝu_p.
  - Two T-directions on one side both have elevation in (0, arcsin β), so they are less than 60° apart.
  - But two points at distance 1 from p are at least 60° apart as seen from p.
- **(T2)** If q is the right T-neighbour of p, then p is the left T-neighbour of q, since ∠(u_p, u_q) ≤ β.
- Hence the T-edges form directed paths and cycles, with every cycle of length ≥ 3.

**Turning measure.** Let γ be a closed arc of the boundary of a convex body. Its **turning** is the length of the arc N(γ) ⊂ S¹, where N(γ) is the union of the normal cones at *all* points of γ, **including the full cones at its endpoints**.

**Lemma 3.4 (multiplicity).** Let γ₁, …, γ_m be closed boundary arcs of one convex body, and suppose every boundary point lies in at most M of them. Then Σ_i turning(γ_i) ≤ 2πM.

*Proof.*
- For all but countably many directions ν, the set of boundary points with normal ν is a single point y_ν.
- ν ∈ N(γ_i) if and only if y_ν ∈ γ_i.
- Integrate over ν ∈ S¹. ∎

Points of S ∖ D (on ∂K), and likewise points of S ∩ D (on ∂P₁), are at least 1 apart in arc length along the boundary. So a boundary arc of length ℓ contains at most ℓ + 1 of them.

## 4. The reductions: (VS), (E), and the linear programmes

**(VS)** μ(Δ₂) ≤ (3/2)|S| + C_V.

*Proof.* Every Δ₂-pair lies in S, and every distance within S is a distance of X.
- If S contains a diametral pair of X: then diam S = Δ, and the next distance of S is ≤ Δ₂. Since S contains all the Δ₂-pairs, Δ₂ is the second-largest distance of S. Apply [Ve87] to S.
- Otherwise: every distance within S is ≤ Δ₂, so Δ₂ = diam S and [HP] gives μ(Δ₂) ≤ |S|. ∎

The same argument applied to any S′ ⊂ S shows that the Δ₂-pairs inside S′ number at most (3/2)|S′| + C_V.

**(E)** μ(δ) ≤ e(S) + 6r. Every δ-pair not inside S has an endpoint in R.

**Lemma 4.1.** Suppose e(S) ≤ k|S| + C with k < 3/2. Then

  min{μ(Δ₂), μ(δ)} ≤ 9n/(7.5 − k) + C + C_V.

*Proof.* Put λ = (6 − k)/(7.5 − k) ∈ (0, 1). Then

  λ·(1.5s) + (1 − λ)(ks + 6r) = (9/(7.5 − k))(s + r) = 9n/(7.5 − k).

**[C1]** checks the certificate exactly: for k = 1, 5/4, 4/3 the value is 18/13, 36/25, 54/37 respectively. ∎

**Lemma 4.2 (weighted form).** Let P₁ ⊂ S consist of points of Δ₂-degree exactly 1, with p := |P₁|. Suppose e(S) ≤ |S| + 2p + C. Then min{μ(Δ₂), μ(δ)} ≤ (7/5)n + C + C_V.

*Proof.*
- At most p Δ₂-pairs touch P₁. The remaining pairs lie inside S ∖ P₁. So μ(Δ₂) ≤ p + (3/2)(s − p) + C_V.
- Combine with weights 4/5 and 1/5: (4/5)(1.5s − 0.5p) + (1/5)(s + 2p + 6r) = 1.4s + 1.2r ≤ 1.4n **[C1]**. ∎

So it suffices to prove the following in the nondegenerate regime:
- e(S) ≤ (4/3)|S| + O(1) in every τ-regime except the one in §7.3;
- that regime satisfies the hypothesis of Lemma 4.2.

**Small cases.** Suppose the regime is nondegenerate and Δ₂ < 10⁴.
- Then X lies in a disc of radius Δ < 1.94·10⁴ around any of its points.
- Packing gives n ≤ (2Δ + 1)² < N₀ := 1.51·10⁹ **[C11]**.
- Since μ(δ) ≤ 3n, the theorem holds for such X once C₀ ≥ 3N₀.

**From now on, in the nondegenerate regime, Δ₂ ≥ 10⁴.** In particular 2/Δ₂ ≤ β/2 **[C3]**.

> *Correction to the notes (referee caveat).* The notes say "if Δ₂ < Δ₀ then Δ ≤ 2Δ₂". That is false in general: take a point together with a short arc of its diametral partners. The correct statement is **Δ ≤ 1.94Δ₂**, and it holds by definition in the nondegenerate regime, which is the only place it is used.

## 5. Bad edges are O(1) (nondegenerate regime)

### 5.1 Lens lemma

**Lemma 5.1.** Let Λ = D(c₁, R) ∩ D(c₂, R) with 0 < |c₁c₂| = d < 2R, and put cos φ₀ := d/(2R). Assume

  R ≥ 2/(cos(φ₀/2) − cos φ₀).

Let p lie on the arc of ∂Λ belonging to C(c₁, R), let q lie on the arc belonging to C(c₂, R), and suppose |pq| ≤ 1. Then there is a corner c of Λ such that the boundary arcs from p to c and from c to q each have length at most ρ₀ := 1/sin(φ₀/2).

*Proof.* Take c₁ = (−d/2, 0) and c₂ = (d/2, 0). Write p = c₁ + R(cos φ, sin φ) and q = c₂ + R(−cos ψ, sin ψ), with |φ|, |ψ| ≤ φ₀.

1. **Both points are far from the middle.** We have p_x − q_x = R(cos φ − cos φ₀) + R(cos ψ − cos φ₀), and both terms are ≥ 0. Since |p_x − q_x| ≤ 1, each term is ≤ 1. The hypothesis then gives cos φ < cos(φ₀/2), i.e. |φ| > φ₀/2. Likewise |ψ| > φ₀/2.
2. **Both points are close to a corner.** By the mean value theorem, R(φ₀ − |φ|) ≤ 1/sin ξ for some ξ ∈ (φ₀/2, φ₀) ⊂ (0, π/2]. So R(φ₀ − |φ|) ≤ ρ₀. Likewise R(φ₀ − |ψ|) ≤ ρ₀.
3. **Both are close to the same corner.** Suppose φ and ψ had opposite signs. Then |p_y − q_y| ≥ 2R sin(φ₀/2). The hypothesis gives R ≥ 2/(1 − cos φ₀) = 1/sin²(φ₀/2), so 2R sin(φ₀/2) ≥ 2/sin(φ₀/2) ≥ 2 > 1, a contradiction.
4. So the corner c = (0, sign(φ)·R sin φ₀) works. ∎

`a2_checks.py` and `ref_checks.py §3` found no violation in about 7000 random lenses, with worst ratio 0.66.

**Constants [C7].**
- **KK lenses** (R = Δ₂, d ≤ Δ ≤ 1.94Δ₂):
  - cos φ₀ ≤ 0.97, so ρ₀² = 2/(1 − cos φ₀) ≤ 66.7 < 8.2².
  - The hypothesis needs R ≥ 89.0. The function g(c) = cos(φ₀/2) − c is decreasing in c = cos φ₀.
- **DD lenses** (R = Δ, d ≤ Δ): cos φ₀ ≤ 1/2, so ρ₀ ≤ 2, and the hypothesis needs R ≥ 5.5.

**Lemma 5.2 (lens-corner arc length).** Suppose that in Lemma 5.1 we also have p, q ∈ ∂K′, where K′ ⊂ Λ is a compact convex set, and |pq| = 1. Let H be the closed half-plane bounded by the line pq that contains c, and let γ := ∂K′ ∩ H be the boundary arc of K′ from p to q on c's side. Then

  length(γ) ≤ 2ρ₀.

*Proof.*
- ∂Λ contains no segment, so the line pq meets it only in p and q. Hence ∂Λ ∩ H is exactly the arc p → c → q, which has length ≤ 2ρ₀.
- K′ ∩ H ⊂ Λ ∩ H, and both sets are convex. Monotonicity of perimeter gives length(γ) + 1 ≤ 2ρ₀ + 1.
- If K′ ∩ H is degenerate, i.e. equal to the segment [p, q], then γ is that segment, of length 1 ≤ 2ρ₀. ∎

This is sharper than the 2ρ₀ + 2 in the notes and the 2ρ₀ + 1 the referee asked for.

### 5.2 The count

Recall the three kinds of bad edge pq by type of endpoints: **KK** (both ends in S ∖ D), **DD** (both in S ∩ D) and **cross** (one end in each).

If a perimeter (of K or P₁) is below 2·600 + 2, then the corresponding row has fewer than 1203 points and at most 6·1203 edges. We assume from now on that both perimeters exceed this.

**KK.** Let p, q ∈ S ∖ D form a bad edge.
- If w_p = w_q, then ∠(u_p, u_q) ≤ 2 arcsin(1/(2Δ₂)) < β **[C3]**, so the edge is good. Hence w_p ≠ w_q.
- Then K ⊂ Λ(w_p, w_q). Here p lies on the C(w_p)-arc and q on the C(w_q)-arc, and d = |w_p w_q| ≤ Δ ≤ 1.94Δ₂.
- Lemmas 5.1 and 5.2 give an arc γ_pq ⊂ ∂K from p to q of length ≤ 2ρ₀.
- The union of the normal cones along the closed arc γ_pq is connected and contains u_p and u_q. So turning(γ_pq) ≥ ∠(u_p, u_q) > β.
- **Multiplicity.** If y ∈ γ_pq, then p lies within arc distance 2ρ₀ of y. There are ≤ 4ρ₀ + 1 such points p, each of degree ≤ 6. So M ≤ 6(4ρ₀ + 1).
- Lemma 3.4 gives

  #KK-bad ≤ 12π(4ρ₀ + 1)/β < **1.28·10⁵** **[C9]**.

- *Corrected constant.* The notes' own formula 12π(4ρ₀ + 5)/β evaluates to ≈ **1.43·10⁵**, not 4.4·10⁴ **[C9]**. Either value is harmless.

**DD.** The same argument, on ∂P₁ with the lens D(x_p, Δ) ∩ D(x_q, Δ) and ρ₀ ≤ 2. (If x_p = x_q, the angle is < 2/Δ < β, so the edge is good.)

  #DD-bad ≤ 12π·9/β < 3.4·10⁴.

**Cross edges** zv with z ∈ S ∩ D and v ∈ S ∖ D. Since z ∈ X, |z w_v| ∈ [0, Δ₂] ∪ {Δ}.

**(c1) The case |z w_v| = Δ.**
- By 3.2(a), (w_v − z)/Δ is a second P₁-normal at z.
- Its angle to u_v is the angle at w_v of the triangle z v w_v. That angle is opposite the side of length 1, hence acute, and at most arcsin(1/Δ) < 2/Δ₂ ≤ β/2 **[C3]**.
- So the normal cone of P₁ at z has angle > β − β/2 = β/2.
- Normal cones are interior-disjoint, so fewer than 4π/β points z qualify, each of degree ≤ 6.

  #(c1) < 24π/β < 7600.

**(c2) The case |z w_v| ≤ Δ₂.** This case closes referee gap (c2) in full. Let g be the unit vector from v towards x_z, and put α := ∠(u_v, g).

1. **Depth.** v ∉ D gives |v x_z| ≤ Δ₂, and |z x_z| = Δ with |zv| = 1 gives |v x_z| ≥ Δ − 1. So v ∈ D(x_z, Δ₂) at depth d₀ := Δ₂ − |v x_z| ∈ [0, 1 − t].
   - In particular (c2) needs t ≤ 1.
   - Also K ⊂ D(x_z, Δ₂).
2. **α is not small.** ∠(u_z, g) is the angle at x_z of the triangle z v x_z, which is ≤ arcsin(1/Δ) < β/2. Hence α ≥ ∠(u_v, u_z) − ∠(u_z, g) > β/2.
3. **α is not close to π (the missing step).**
   - w_v and x_z both lie in X, so |w_v x_z| ≤ Δ ≤ 1.94Δ₂.
   - The law of cosines in the triangle v w_v x_z (sides Δ₂ and Δ₂ − d₀ at v, with angle α) gives cos α ≥ (1 + ρ² − 1.94²)/(2ρ), where ρ := (Δ₂ − d₀)/Δ₂ ∈ [1 − 10⁻⁴, 1].
   - The right-hand side is increasing in ρ, so cos α ≥ −0.8821, i.e. **α ≤ 151.9°** **[C8]**.
   - Since sin is concave on [0, π], for α ∈ [β/2, 151.9°] we get sin α ≥ min{sin(β/2), 0.471} = sin(β/2) **[C8]**.
4. **The walk.**
   - Let e₀ ⊥ u_v be the unit vector with e₀·g = −sin α < 0.
   - Follow ∂K from v in the direction whose forward one-sided tangent is closest to e₀, parametrised by arc length: γ(0) = v.
   - Suppose the turning of γ([0, σ]) is ≤ β/4. This turning includes the **whole** normal cone N_K(v), not just the part beyond u_v; this is the corner case the referee raised.
   - Then every normal on the arc is within β/4 of u_v, so every forward tangent γ′ is within β/4 of e₀. (At a corner v the forward tangent is perpendicular to an extreme normal of N_K(v), which by assumption is also within β/4 of u_v.)
   - Hence γ′·g ≤ −sin α + 2 sin(β/8) ≤ −sin(β/2) + 2 sin(β/8) < −β/5 **[C8]**.
   - Integrating, (γ(σ) − v)·g ≤ −σβ/5, and so

     |γ(σ) − x_z|² ≥ (Δ₂ − d₀)² + (2/5)(Δ₂ − d₀)σβ.

   - For σ = L := 6/β = 600 the right-hand side exceeds Δ₂² **[C8]**. That puts γ(L) outside D(x_z, Δ₂) ⊃ K, a contradiction.
   - Hence the closed arc J_v of length L from v, in the chosen direction, has turning > β/4.
5. **Count.**
   - A point y lies in J_v only if v is within arc distance L of y. That allows ≤ 2L + 1 points v.
   - Lemma 3.4 gives #{v} ≤ 2π(2L + 1)/(β/4).
   - Each such v has degree ≤ 6, so

     #(c2) ≤ 48π(2L + 1)/β < 1.82·10⁷ **[C9]**.

**Total.** Together with the 71 mixed T-edges of §7.1 and the 12 corner rungs of §7.3,

  C_bad + 71 + 12 < 1.83·10⁷ < 10⁸ **[C9]**.

## 6. Region I: τ ≤ √3/2 − 2β, giving 18/13

Let p ∈ S ∖ D and let q be a good neighbour of p. The *elevation* of q − p is arcsin((q − p)·u_p).

- If q is normal for p, then b > 0 whether q ∈ D (by 3.2a) or q ∉ D (by 3.2b). So a < β.
- Otherwise q is an exception and a = −τ.
- **Case τ ≥ 0.** Every good neighbour on one side of ℝu_p has elevation in [−arcsin τ, arcsin β). So any two are less than arcsin(√3/2 − 2β) + arcsin β ≈ 58.35° < 60° apart **[C4]**. This bound is proved via cos(A + B) > 1/2.
- **Case τ < 0.** Then |τ| ≤ 1/(2Δ₂), and all elevations lie in (0, arcsin β) ∪ {arcsin|τ|}. The window is again < 60° **[C4]**.

Let p ∈ S ∩ D. Then a > 0 always, and either a < β, or p is the exception of q and a ∈ [τ − β, τ + β]. The window is ≤ arcsin(√3/2 − β) < 60° **[C4]**.

Two neighbours of p are ≥ 60° apart, so p has at most one good neighbour per side. Hence

  e(S) ≤ |S| + C_bad,

and Lemma 4.1 with k = 1 gives **18n/13 + C**.

## 7. The regions with τ > √3/2 − 2β

Here τ > 2β **[C5, C6]**, so the T-edge/rung dichotomy of §3 applies.

### 7.1 Mixed T-edges (Region II only)

Region II is **τ ≥ √3/2 + 3β**. In this region t ≥ √3/2 + 3β:
- if t ≤ 1, then t ≥ τ;
- if t > 1, then t > 1 > √3/2 + 3β.

Hence t − arcsin β ≥ 0.886 **[C5]**.

This lemma is stated and used **only in Region II**. Region III never uses it: there (T1) alone bounds all T-edges, mixed ones included, by |S|. This closes the referee's cosmetic gap about the threshold "t ≥ 0.87".

**Lemma 7.1.** Let v ∈ S ∖ D and z ∈ S ∩ D be joined by a T-edge. Then the closed arc of ∂K of length 2 starting at v on z's side has turning ≥ t − arcsin β.

*Proof.*
- Suppose the turning is Θ < t − arcsin β < π/3. Then every forward tangent is within Θ of e₀, the tangent pointing to z's side.
- So |γ(σ) − v| ≥ σ cos Θ, and some σ* ≤ 2 has |γ(σ*) − v| = 1.
- The unit vector γ(σ*) − v lies in the Θ-cone around e₀. The vector z − v has elevation < arcsin β on the same side.
- Hence |γ(σ*) − z| ≤ Θ + arcsin β < t ≤ dist(z, K). But γ(σ*) ∈ K, a contradiction. ∎

**Multiplicity.** Each v has at most 2 T-edges, and v must lie within arc distance 2 of y: at most 5 such v. So M ≤ 10, and

  #mixed-T ≤ 2π·10/0.886 < 71 **[C5]**.

From here on, the **K-row** means S ∖ D and the **D-row** means S ∩ D, each carrying its own *pure* T-edges. Rungs join the two rows.

### 7.2 Region II: τ ≥ √3/2 + 3β

**Sub-regime τ > 1 (t > 1).** By 3.2(c) there are no rungs. By (T1), e(S) ≤ |S| + C_bad, which gives 18n/13 + C.

So assume √3/2 + 3β ≤ τ ≤ 1. Then s = √(1 − τ²) ≤ s_max ≈ 0.4440 **[C5]**.

**Offsets.** For a rung (v, z) write z = v + o_σ(u_v), where o_σ(u) := −τu + σs u^⊥ and σ = ±1.
- u ↦ o_σ(u) is a rotation, so |o_σ(u) − o_σ(u′)| = |u − u′| ≤ ∠(u, u′).
- |o₊(u) − o₋(u)| = 2s.

**(R1) Each vertex has at most one rung.**
- *At v.* The two candidate positions are 2s < 1 apart.
- *At z.* Suppose z had rungs to v ≠ v′. Both rungs are good, so ∠(u_v, u_{v′}) ≤ 2β. Hence |v − v′| ≤ 2βτ + 2s ≤ 2s + 2β ≈ 0.908 < 1 **[C5]**, a contradiction.

**T-steps.** If q is the right T-neighbour of p, then q − p = cos ε·(u_p rotated −90°) + sin ε·u_p with ε ∈ (0, arcsin β). Consequently, for T-steps e₁ at v₀ and e₂ at z₀ we get ∠(e₁, e₂) ≤ ∠(u_{v₀}, u_{z₀}) + arcsin β, and so |e₁ − e₂| ≤ β + arcsin β.

**(R2) Proximity lemma.**
- *Setting.* (v₀, z₀) is a rung. v₁ is the right pure T-neighbour of v₀, and z₁ is the right pure T-neighbour of z₀. Write e₁ = v₁ − v₀ and e₂ = z₁ − z₀.
- *Claim.* If v₁ has a rung (v₁, z′), then z′ = z₁.

*Proof.*
- z′ − z₁ = (e₁ − e₂) + (o_{σ₁}(u_{v₁}) − o_{σ₀}(u_{v₀})).
- ∠(u_{v₀}, u_{z₀}) ≤ β (the rung is good) and ∠(u_{v₀}, u_{v₁}) ≤ β (the T-edge is good).
- Hence |z′ − z₁| ≤ (β + arcsin β) + β + 2s = 2s + 2β + arcsin β ≈ 0.918 < 1 **[C5]**.
- Distinct points of X are ≥ 1 apart, so z′ = z₁. ∎

**(R2-sym) Symmetric proximity lemma.** This is the referee gap: here it is proved, not merely asserted.
- *Setting.* As in (R2).
- *Claim.* If z₁ has a rung (v′, z₁), then v′ = v₁.

*Proof.*
- v′ = z₁ − o_{σ′}(u_{v′}) and v₁ = z₀ − o_{σ₀}(u_{v₀}) + e₁. So

  v′ − v₁ = (e₂ − e₁) − (o_{σ′}(u_{v′}) − o_{σ₀}(u_{v₀})).

- The angle between u_{v′} and u_{v₀} is at most 3β, as the sum of three good-edge angles:
  - ∠(u_{v′}, u_{z₁}) ≤ β, because the rung (v′, z₁) is good;
  - ∠(u_{z₁}, u_{z₀}) ≤ β, because the T-edge (z₀, z₁) is good;
  - ∠(u_{z₀}, u_{v₀}) ≤ β, because the rung (v₀, z₀) is good.
- Hence

  |v′ − v₁| ≤ (β + arcsin β) + 3β + 2s = 2s + 4β + arcsin β ≤ **2s + 6β ≈ 0.948 < 1** **[C5]**.

- So v′ = v₁. ∎

The adversarial maximum found by the referee was 0.914.

**(R3) Parallel rungs and rhombi.**
- *At most two rungs share a vector.* Rungs with the same vector c satisfy c·u_v = −τ, so u_v is one of the two unit solutions. These lie at ±θ₀ from −c, where θ₀ := arccos τ ∈ [0, π/2].
  - By Lemma 3.3 two distinct K-ends have distinct u. So **no three rungs are parallel**. (Rungs form a matching by (R1), so the K-ends are distinct.)
  - Two parallel rungs have normals exactly 2θ₀ apart.
- *Rhombi force parallel rungs.* Suppose v₀v₁, v₁z₁, z₁z₀, z₀v₀ are all unit edges. Then v₁ and z₀ are two distinct points of C(v₀, 1) ∩ C(z₁, 1), so they are its two points. Hence v₀ + z₁ = v₁ + z₀, i.e. z₀ − v₀ = z₁ − v₁.
- *When rhombi can exist.* If the T-edge v₀v₁ is good, then 2θ₀ ≤ β. So **rhombi exist only if τ ≥ cos(β/2)**, and cos(β/2) > √3/2 + 3β **[C5]**.

**Ownership count.**
- *Walks.* For a rung r = (v, z), walk right from v along pure K-row T-edges until the first vertex after v that is a rung vertex, or until the walk stops. Let k ≥ 1 be the number of vertices visited before stopping, v included. Define d likewise in the D-row starting from z.
  - r **owns** these k + d vertices.
  - Every other row vertex is **unowned**: it has no rung vertex to its left on its T-path or T-cycle.
- *Charging.* Charge to r the rung itself and the right T-edge out of each vertex r owns. Charge each other T-edge to its unowned left endpoint.
- Every good non-mixed edge is charged exactly once. Every vertex has at most one right T-edge.
- *Bounds.*
  - **edges(r) ≤ 1 + k + d**, with equality only if both walks end at a rung vertex ("both reach").
  - Otherwise edges(r) ≤ k + d.
  - Unowned vertices carry at most one edge each.
- *Both-reach gaps are (1,1) or (≥2, ≥2).*
  - If both reach and k = 1: z₀ has a right neighbour z₁, and v₁ is a rung vertex. By (R2) its rung is (v₁, z₁), so d = 1.
  - If both reach and d = 1: v₀ has a right neighbour v₁, and z₁ is a rung vertex. By (R2-sym) its rung is (v₁, z₁), so k = 1.
  - A (1,1) gap is a rhombus v₀v₁z₁z₀. (By R1, z₁ ≠ z₀ and v₁ ≠ v₀.)
- *Ratios.*
  - Rhombus gap: 3/2.
  - Both-reach gap with k, d ≥ 2: ≤ 5/4.
  - Otherwise: ≤ 1.
- *If τ < cos(β/2)* there are no rhombi, and e(S) ≤ (5/4)|S| + C.
- *If τ ≥ cos(β/2)* we pair each rhombus rung r₀ with its successor r₁ = (v₁, z₁).
  - r₁ is not a rhombus rung. Otherwise r₀, r₁, r₂ would be three parallel rungs; v₂ ≠ v₀, since T-cycles have length ≥ 3.
  - The pairing is injective, because v₀ is the unique left T-neighbour of v₁.
  - Pair ratio ≤ max{(4 + m)/(2 + m) : m ≥ 4, (3 + m)/(2 + m) : m ≥ 2} = 4/3 **[C5]**.

**Conclusion for Region II.**
- If τ ≥ cos(β/2): e(S) ≤ (4/3)|S| + C_bad + 71. Lemma 4.1 gives **54n/37 + C**.
- If √3/2 + 3β ≤ τ < cos(β/2): the bound is 36n/25 + C.

### 7.3 Region III: √3/2 − 2β < τ < √3/2 + 3β

Here θ₀ = arccos τ ∈ (26.36°, 32.22°).

**Corner lemma.** Suppose v ∈ S ∖ D has a rung partner z and a second Δ₂-partner w′, with u′ := (w′ − v)/Δ₂. Then ∠(u_v, u′) ≥ min(2θ₀, 90° − θ₀) > 2π/7.

*Proof.* There are two cases.
- **|z w′| = Δ.** Then c = z − v satisfies c·u′ = −τ as well (3.2c applied to w′). So u′ is the other solution, and the angle is 2θ₀.
- **|z w′| ≤ Δ₂.** Then c·u′ > 0, while ∠(c, u_v) = 180° − θ₀. So the angle is ≥ 90° − θ₀.

For the numerical bound **[C6]**:
- 2θ₀ > 2π/7 because τ < √3/2 + 3β < cos(π/7).
- 90° − θ₀ > 2π/7 because τ > √3/2 − 2β > cos(3π/14). ∎

Both u_v and u′ are normals of K at v, so N_K(v) is wider than 2π/7. Hence **at most 6** such v exist.

Every other K-vertex that has a rung has Δ₂-degree exactly 1. Let P₁ be the set of these vertices. Then:
- a K-vertex has at most 2 rungs (the two positions v + o_±);
- (T1) bounds all T-edges, mixed ones included, by |S|.

Hence e(S) ≤ |S| + 2|P₁| + 12 + C_bad. Lemma 4.2 gives **7n/5 + C**.

This regime really does need P₁. The single-centre "hexagonal strip" has average degree 3 locally.

## 8. Degenerate regime: Δ > 1.94Δ₂ and n ≥ 4 give μ(Δ₂) ≤ n + 1

Put q := (Δ₂/Δ)² < 1/1.94².

**Step 1. No two disjoint diametral pairs.** Suppose (x, x′) and (z, z′) are disjoint diametral pairs, with midpoints m and m′.
- The four cross distances satisfy Σ|a − b|² = 2Δ² + 4|m − m′|² ≥ 2Δ².
- Each cross distance is ≤ Δ₂ or equal to Δ.
- If at most one is Δ, the sum is ≤ Δ²(1 + 3q) < 2Δ² **[C10]**, a contradiction. So at least two are Δ.
- **Two disjoint cross pairs.** Then the four points form a rhombus of side Δ. Its diagonals satisfy d₁² + d₂² = 4Δ², so one diagonal is ≥ √2Δ. Contradiction.
- **Two cross pairs sharing a point.** Then there is an equilateral triangle of side Δ, and the fourth point lies on the 60° arc of radius Δ between two of its vertices.
  - One of its distances to those two vertices is ≥ 2Δ sin 15°.
  - Since (2 sin 15°)² = 2 − √3 > q **[C10]**, that distance is > Δ₂.
  - It is also < Δ, which is impossible.

**Step 2. The diameter graph is a star.**
- By Step 1 the diameter graph is a star or a triangle.
- A triangle with n ≥ 4 is impossible. Any 4th point is non-diametral, so its distances to all three vertices are ≤ Δ₂. That would put it within Δ₂ of all three vertices, but Δ₂² < Δ²/3 = (circumradius)² **[C10]**.
- So D = {y} ∪ A with A = Diam(y). Put B := X ∖ D ⊂ K.

**Step 3. Where the Δ₂-pairs can be.**
- **Within B: none.** K ⊂ D(y, Δ₂) ∩ D(a, Δ₂) for a ∈ A, a lens whose bounding box has diagonal² < 0.24Δ₂² **[C10]**. So diam K < Δ₂.
- **Within A: at most one.** A ⊂ C(y, Δ), and its pairwise distances are ≤ Δ₂ (a Δ-pair inside A would make a triangle).
  - A chord of length ≤ Δ₂ subtends an angle < 120° at y **[C10]**. So A lies in an arc whose angular width equals the largest pairwise angle.
  - A Δ₂-pair must realise that maximum, so it can only be the two extreme points.
- **Between y and A: none**, since those distances are Δ.

Hence μ(Δ₂) ≤ 1 + I, where I := #{(b, w) : b ∈ B, w ∈ W := {y} ∪ A, |bw| = Δ₂}.

**Step 4. Incidence bound I ≤ |B| + |W|.**
- **Each J_w is a single arc.** For w ∈ X, let J_w := C(w, Δ₂) ∩ K.
  - For x ∈ X, C(w, Δ₂) ∩ D(x, Δ₂) is one closed arc of angular length ≤ π, namely {cos(θ − θ_x) ≥ |wx|/(2Δ₂)}.
  - So for p, q ∈ J_w (note |pq| < Δ₂ < 2Δ₂), the minor arc of C(w) from p to q lies in every D(x, Δ₂), hence in K.
  - Since diam K < Δ₂, the angular spread of J_w is < 60°.
  - Therefore J_w is a single closed arc, possibly a single point.
- **No point is interior to two arcs.** Suppose b is a relative-interior point of a nondegenerate arc J_w and also lies on C(w′, Δ₂) with w′ ≠ w.
  - The arc J_w stays inside D(w′, Δ₂) on both sides of b, so C(w) and C(w′) are internally tangent at b.
  - Two internally tangent circles of equal radius coincide, so w = w′. Contradiction.
- **Consequences.**
  - Each nondegenerate J_w is an edge of the ball-polygon ∂K.
  - At a point b ∈ B at most two nondegenerate W-arcs meet (the two edges at b). Any further incidences of b come from degenerate arcs J_w = {b}.
- **Counting.** Let I_nd be the incidences from nondegenerate arcs.
  - I_nd ≤ |B| + #{b : two W-edges meet at b}.
  - Map each such b to the W-edge that follows it clockwise. This map is injective. So I_nd ≤ |B| + #{w : J_w nondegenerate}.
  - Adding the degenerate arcs gives I ≤ |B| + |W|.

**Conclusion.** μ(Δ₂) ≤ 1 + |B| + |A| + 1 = n + 1, and n + 1 ≤ 54n/37 + 1.

Numerical support: `degen_check.py` and `ref_degen.py` (2403 adversarial star sets) give a maximum of μ(Δ₂) − n equal to 0.

## 9. Assembly

| regime (δ = 1, β = 1/100) | e(S) bound | min{μ(Δ₂), μ(δ)} ≤ |
|---|---|---|
| degenerate: Δ > 1.94Δ₂, n ≥ 4 | n/a | n + 1 (§8) |
| nondegenerate with Δ₂ < 10⁴ | n/a | n < 1.51·10⁹ (§4) |
| I: τ ≤ √3/2 − 2β (incl. τ ≤ 0) | \|S\| + C | 18n/13 + C (§6) |
| III: √3/2 − 2β < τ < √3/2 + 3β | \|S\| + 2\|P₁\| + C | 7n/5 + C (§7.3) |
| II-rest: √3/2 + 3β ≤ τ < cos(β/2) | (5/4)\|S\| + C | 36n/25 + C (§7.2) |
| II-near-resonant: cos(β/2) ≤ τ ≤ 1 | (4/3)\|S\| + C | **54n/37 + C** (§7.2) |
| II-high: τ > 1 (⟺ t > 1) | \|S\| + C | 18n/13 + C (§7.2) |

(Table cosmetics: "τ > 1" is now its own row. In the notes it sat inside both "II rest" and "τ ≥ cos(β/2)".)

**Coverage.**
- The τ-intervals partition ℝ.
- The regime split at 1.94 is exhaustive.
- The cases n ≤ 3 are trivial.

With C ≤ 10⁸ + C_V, all the constants are ≤ 54/37 **[C1]**. The theorem holds with **C₀ = 3N₀ + 10⁸ + C_V**. ∎

## 10. Referee gaps: status

| # | referee item | status | where |
|---|---|---|---|
| 1 | Symmetric (R2) asserted, not proved | **Closed.** Full proof: \|v′ − v₁\| ≤ 2s + 4β + arcsin β ≤ 2s + 6β ≈ 0.948 < 1 [C5] | §7.2 (R2-sym) |
| 2a | (c2) needs α bounded away from π | **Closed.** \|w_v x_z\| ≤ Δ ≤ 1.94Δ₂ gives cos α ≥ −0.8821, so α ≤ 151.9° and sin α ≥ sin(β/2) on the whole range [C8] | §5.2 (c2) step 3 |
| 2b | (c2) corner normal cone | **Closed.** Turning is defined to include full endpoint cones. The forward tangent at a corner is perpendicular to an extreme normal of N_K(v), within β/4 of u_v under the hypothesis | §3, §5.2 step 4 |
| 3 | KK constant | **Closed.** The notes' formula gives 1.43·10⁵ (not 4.4·10⁴). The sharper length bound gives 12π(4ρ₀+1)/β < 1.28·10⁵ [C9] | §5.2 |
| 4 | §5.1 threshold vs Region III | **Closed.** Lemma 7.1 is stated for Region II only; Region III uses (T1) | §7.1 |
| 5 | "Δ ≤ 2Δ₂" remark | **Closed.** Replaced by Δ ≤ 1.94Δ₂, which holds by definition in the nondegenerate regime | §4 |
| 6 | Citation mismatch | **Resolved, with a correction to the referee.** CDL v5 (arXiv HTML, fetched 2026-09-23) cites the 3n/2 bound as "[23]", which *is* Ve87 (Discrete Math 67, 1987). Their [22] is the 1985 paper and [24] the 1996 paper. The notes' "[23]" was correct; the claimed mismatch may come from an older arXiv version. This write-up cites Ve87 directly | §2 |
| 7 | Table cosmetics | **Closed** | §9 |
| — | Lens-corner length (publication item 5) | **Closed.** Proved ≤ 2ρ₀ by perimeter monotonicity (Lemma 5.2) | §5.1 |

**Minor adjustments made while writing.** None of these changes a conclusion.
- (c1) now uses degree ≤ 6 rather than ≤ 4.
- The (R1)-at-z bound is tightened to 2s + 2β.
- The (R2) bound is tightened to 2s + 2β + arcsin β.
- The mixed-T multiplicity is taken as M ≤ 10, so the count is < 71; the notes had 85.

**No mathematical error was found.**

**Remaining dependence.** The result depends on the exact statement of [Ve87], which we have not read in the original. Any additive constant is absorbed. A hypothesis such as m ≥ m₀ would also be harmless, because S is large whenever μ(Δ₂) is large.

Two parts are the least standard and deserve an independent check:
- the ownership/pairing bookkeeping (§7.2);
- the incidence count (§8, Step 4).

Both have been checked by hand twice (notes and referee), and numerically on adversarial families. Neither has a formal proof-assistant verification.

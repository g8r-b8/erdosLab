# Erdős #132 / CDL Problem 1.6: Angle A, pushing the upper bound below 3/2

Date: 2026-09-22. Scripts are in this directory: `lp*.py`, `fan*.py`, `constr.py`, `bands.py`.

## 0. Setup and sources

- X ⊂ R², |X| = n. Δ = diameter, Δ₂ = second-largest distance, δ = minimum distance, μ(d) = multiplicity.
  Normalize **δ = 1**. Put **t := Δ − Δ₂** (the "shell gap").
- CDL = Clemen–Dumitrescu–Liu, arXiv:2505.04283 (v5, 3 Feb 2026). Problem 1.6 asks for
  L := limsup max min{μ(Δ₂), μ(δ)}/n. Known: L ≥ 9/7 (ienjoymath, forum, 25 Jul 2026; even m-gon + "servers"
  + lattice patch). L ≤ 3/2 comes only from Vesztergombi's μ(Δ₂) ≤ 3n/2 (Discrete Math 67 (1987)).
- Inputs from CDL §2.2 (they cite Vesztergombi [24] Props 1–8), used here as black boxes:
  L1, L2 are the first two convex layers. Every Δ₂-pair meets L1, and both ends lie in L1 ∪ L2. Let G be the
  Δ₂-graph on L1 ∪ L2, and prune vertices of degree < 2 repeatedly until G' remains, on L1' ∪ L2'. Then
  e(G') ≤ min{4|L1'|/3 + 2|L2'|, 2|L1'| + |L2'|}. Each pruned vertex takes at most one edge with it.
- Novelty check: the forum thread (5 comments, newest 25 Jul 2026) has only the 9/7 lower bound and small-n
  cases. CDL v5 still lists 3/2 as the upper bound. Web and arXiv searches (Sep 2026) turned up no improvement
  of 3/2. The ienjoymath note says a companion note with an "LP analysis over Vesztergombi's constraints"
  (supporting 9/7) is coming, but it has not appeared.

## 1. Results (summary)

**Theorem A.** Fix κ ∈ (0,1) and β ∈ (0, 1/20). There is C = C(κ,β) such that every n-point X with δ = 1,
  Δ ≤ (2−κ)Δ₂, and **t ∉ (√3/2 − 2β, 1]**
satisfies
  min{μ(Δ₂), μ(δ)} ≤ (16/11) n + C.

(16/11 ≈ 1.4545 < 3/2.) Remark A′ (sketch only): if t > 1 and Δ ≤ √3(1−κ)Δ₂, the constant improves to
32/23 ≈ 1.391.

Coverage:
- **Covered:** the regime t/δ ≤ √3/2 − 2β, which contains the 9/7 construction (t/δ → 0). Also the regime
  1 < t/δ ≤ (1−κ)Δ₂.
- **Not covered, and this is the real gap:** the "resonant window" √3/2 ≲ t/δ ≤ 1. The CDL/Vesztergombi
  odd-m constructions sit exactly here (t/δ → 1⁻; checked numerically).
- **Not covered, degenerate:** Δ > (2−κ)Δ₂, where every Δ₂ is less than about 0.53Δ.

So **no unconditional c > 0 yet.** Theorem A gives c = 1/22 outside the window, and §6 explains why the window
needs a genuinely new, Δ₂-weighted ingredient.

Structure of the proof: (i) an LP reduction showing that a "Ring Lemma" e_δ(S) ≤ |S| + O(1) implies 16/11,
where S is the set of points having a Δ₂-partner; (ii) a proof of the Ring Lemma outside the window. It uses
the ball-polygon K = ∩_{w∈X} D(w, Δ₂) and a "band lemma" for δ-edges.

## 2. Basic lemmas (rigorous)

**Lemma 1 (support identities).**
(a) Let p have a Δ₂-partner w, and put u = (w−p)/Δ₂. For every y ∈ X,
  (y−p)·u = (|y−p|² + Δ₂² − |y−w|²)/(2Δ₂).
Since |y−w| ∈ [0,Δ₂] ∪ {Δ} (there are no distances in (Δ₂,Δ)), one of two things holds:
  (y−p)·u ≥ |y−p|²/(2Δ₂) > 0 ("normal"), or
  |y−w| = Δ and (y−p)·u = (|y−p|² − 2Δ₂t − t²)/(2Δ₂) ("exception": y is diametral to w).
For |y−p| = 1 an exception has (y−p)·u ∈ (−t, −t + 1/(2Δ₂)), and exceptions at distance 1 need t ≤ 1.
(b) Let z have a diametral partner x, and put u = (x−z)/Δ. Then for every y,
  (y−z)·u ≥ |y−z|²/(2Δ) > 0.
In particular u is an inward normal of P1 = conv X at z.
Proof: law of cosines. ∎

**Lemma 2 (ball-polygon structure).** Let D be the set of diameter endpoints, S the set of points with a
Δ₂-partner, and K := ∩_{w∈X} D(w,Δ₂). Then:
- X∖D ⊂ K.
- S∖D ⊂ ∂K, and for v ∈ S∖D with partner w, u_v = (w−v)/Δ₂ is an inward normal of K at v.
- D ∩ K = ∅, and dist(z,K) ≥ t for z ∈ D.
- D consists of hull vertices, and for z ∈ D the diametral directions Φ(z) lie in the normal cone of P1 at z.
Proof: all distances from a non-diametral point are ≤ Δ₂, and z ∈ C(x,Δ) with K ⊂ D(x,Δ₂). ∎

## 3. LP reduction (rigorous)

Let a′ = |L1'|, b′ = |L2'| (so V′ := L1' ∪ L2' ⊂ S), s₃ = |S∖V′| and r = n − |S|.
- Every pruned vertex that carried an edge when it was removed has a Δ₂-partner, so it lies in S∖V′. Hence
  μ(Δ₂) ≤ s₃ + e(G') ≤ s₃ + min{4a′/3 + 2b′, 2a′ + b′}.
- Trivially μ(δ) ≤ e_δ(S) + Σ_{z∉S} deg(z) ≤ e_δ(S) + 6r.

**Proposition R.** If e_δ(S) ≤ |S| + C, then min{μ(Δ₂), μ(δ)} ≤ 16n/11 + 8C/33.

Proof: take the convex combination with weights 10/33, 15/33, 8/33 of
  s₃+2a′+b′,  s₃+4a′/3+2b′,  a′+b′+s₃+6r+C.
The coefficients come out as 1 for s₃ and 48/33 for each of a′, b′, r, all at most 48/33 = 16/11, and
a′+b′+s₃+r = n. ∎

The LP is tight at a′ = 6n/11, b′ = 4n/11, r = n/11 (`lp3.py`, `lp4.py`).

Sensitivity:
- With a ring coefficient k in e(S) ≤ k|S| and the trivial weight 6 for R, the bound stays below 3/2 iff
  k < 1.2.
- If R-points have at most 2 neighbours in S (weight 4), the bound becomes 32/23.
- The general 3/2 upper bound is equivalent to k = 3/2 (average degree 3 on the ring). That is exactly what
  the "rhombic strip" of §6 achieves locally.

## 4. Ring Lemma outside the window

**Ring Lemma.** Under the hypotheses of Theorem A, e_δ(S) ≤ |S| + C(β,κ). With Proposition R this proves
Theorem A.

**Direction field.** Choose u_p once for each p ∈ S:
- p ∈ S∖D: the direction to one fixed Δ₂-partner w_p. This is a K-normal.
- p ∈ S∩D: the direction to one fixed diametral partner x_p. This is a P1-normal.

Call a δ-edge pq in S **good** if ∠(u_p,u_q) ≤ β, and **bad** otherwise.

**Band lemma (good edges).** Let e = q−p, a = e·u_p and b = (p−q)·u_q. Then |a+b| = |e·(u_p−u_q)| ≤ β, and by
Lemma 1 each of a, b is either > 0 or lies in the exception band (−t, −t+ε), where ε = 1/(2Δ₂). An exception
target is always in D, and points of D have a > 0. So:
- p ∈ S∖D: a ∈ (0,β) (tangential) or a ∈ (−t, −t+ε) (the exception is behind p).
- p ∈ D: a ∈ (0,β) or a ∈ (t−β−ε, t+β) (the other end, a point of S∖D, sees p as its exception).
- Both ends seeing each other as exceptions is impossible.

Hence on each side of the line ⊥ u_p, the good neighbours of p lie in a tangential arc of width arcsin β plus
one thin band at angle ≈ arcsin t from the tangent. If t ≤ √3/2 − 2β, any two such directions on the same side
are less than 60° apart. Two neighbours must be at least 60° apart, since all distances are ≥ 1. So **p has at
most one good neighbour per side.** If t > 1 there are no bands at all. Either way the number of good edges is
at most |S|. ∎

**Bad edges are O(1).** There are three types.

- **DD** (z, z′ ∈ D, fixed partners x ≠ x′):
  - P1 ⊂ Λ = D(x,Δ) ∩ D(x′,Δ), and z, z′ lie on different arcs of Λ. Since |xx′| ≤ Δ, the corner angles
    are ≥ 120°, so |zz′| = 1 forces both points within O(1) of a common corner c₀.
  - The arc of ∂P1 between z and z′ on the c₀ side lies inside the curvilinear triangle (z, c₀, z′). So it
    has length O(1), and its turning (normal cones included) is ≥ ∠(u_z,u_{z′}) > β.
  - A maximal family of disjoint such arcs has at most 2π/β members, so there are O(1/β) bad DD edges.
  - (If x = x′, the angle is < 1/Δ < β, so the edge is good.)
- **KK** (v, y ∈ S∖D, partners w ≠ w′):
  - Same argument for K ⊂ D(w,Δ₂) ∩ D(w′,Δ₂). Here |ww′| ≤ Δ ≤ (2−κ)Δ₂ bounds the corner angles below by
    θ(κ) > 0 and the lens width below by κΔ₂.
  - Result: O_κ(1/β). **This is the only place κ is used.**
- **Cross** (z ∈ D∩S, v ∈ S∖D). Two sub-cases:
  - (c1) z ∈ Diam(w_v). Then ∠(z→w_v, v→w_v) < 1/Δ₂, so a bad edge forces the diametral-direction set Φ(z)
    to span more than β/2. The sets Φ(z) sit in disjoint P1 normal cones, so at most 4π/β points z qualify.
  - (c2) |z w_v| ≤ Δ₂.
    - Then |v x_z| ∈ [Δ−1, Δ₂], so v ∈ D(x_z,Δ₂) lies within 1−t of that disk's boundary.
    - Also ∠(u_v, v→x_z) > β/2, and K ⊂ D(x_z,Δ₂).
    - Follow ∂K from v along the tangent direction that heads toward the disk's boundary. If the turning
      stayed below β/4, then within arc length ≈ 4(1−t)/β the curve would leave D(x_z,Δ₂), a contradiction.
    - So v lies on an O(1/β)-long arc of ∂K with turning ≥ β/4. There are O(1/β²) such v, each with degree ≤ 6.

Total: bad ≤ C(β,κ). ∎

(Asymptotic steps need Δ₂ ≫ 1/β. This holds for large n, since Δ ≳ √n.)

**Remark A′ (sketch).** For t > 1, an R-point z ∉ D sits in K at distance > 1 from D, so all its S-neighbours
lie on ∂K ∩ C(z,1). Three such neighbours force ∂K to turn by ≥ 60° inside a short arc. That short-arc claim
uses Jung fatness: B(c, Δ₂ − Δ/√3) ⊂ K. So R-points have at most 2 S-neighbours up to O(1) exceptions, which
gives weight 4 and the bound 32/23. Not written out in full.

## 5. Numerical checks (`constr.py`, `bands.py`)

| construction | t/δ | μΔ₂/n | μδ/n | \|S\| | e(S) | good edges, max good neighbours per side |
|---|---|---|---|---|---|---|
| even ring m=200 (9/7 skeleton) | 0.0157 | 1.5 | 1.0 | 400 | 400 = \|S\| | all good, ≤ 1 per side, e·u ∈ [−0.012, 0.020] ≈ ±t |
| even ring m=400 | 0.0079 | 1.5 | 1.0 | 800 | 800 | same |
| odd ring m=201 (CDL Prop 1.5 skeleton) | 1.0000⁻ | 1.5 | 0.5 | 402 | 201 | e·u = ±t (band), ≤ 1 per side |

- The 9/7 ring meets the Ring Lemma with equality (e(S) = |S|). So the lemma is sharp.
- The odd construction lies in the uncovered window, though it is very sparse there (e(S) = |S|/2).
- LP values: see `lp3.py` and `lp4.py`. `fan.py` checks the older "fan" approach: the minimum partner-direction
  angle is 120° when there are no exceptions (fan2 shows ≥ 80° with them). That approach is superseded by the
  band lemma.

## 6. The window √3/2 < t/δ ≤ 1: obstruction and what is missing

**The obstruction ("rhombic strip").** Take a top row of hull vertices on C(w,Δ) at spacing 1, all diametral
to w. Take a bottom row of S∖D points on C(w,Δ₂) at spacing 1, all Δ₂-partners of w. Shift the rows laterally
by h = √(1−t²) < 1/2, so that each bottom point is at distance 1 from exactly one top point, i.e. an exception.
- All mutual distances are ≥ 1 exactly when h ≤ 1/2, i.e. t ≥ √3/2. So the window's lower end is sharp.
- The structure has average δ-degree 3 on S, i.e. e(S) ≈ 1.5|S|. So the Ring Lemma is **false in the window**,
  and so is any purely local argument.
- Exceptions (the rungs) form a matching when t > √3/2. So in the window e(S) ≤ |S| + |M| + O(1), where M is a
  matching between S∖D and S∩D. This is too weak.

**Why this should still be fine.** The rows use one centre w for a whole run. Then w has many Δ₂-partners,
most of them pruned (Δ₂-degree 1), and many diametral partners, which have diameter-degree 1. Moreover the top
row's own Δ₂-partners must lie within O(1) of w, and each such point meets the arc C(w,Δ) at most twice. So only
O(1) top-row points per centre can be in S.

Hence dense rhombic runs are Δ₂-inefficient. Closing the window needs a weighted inequality of the form
  e(S) ≤ |S∖P| + α|P| + (small), with α < 3,
where P is the set of pruned points of S. Weight 3 for pruned points already gives 1.4615 (`lp4.py`).
Equivalently: charge each exception rung to a Δ₂-edge of a core L1' vertex, whose Δ₂-degree is at most 4.
I have not proved this.

**Degenerate regime Δ > (2−κ)Δ₂.**
- Every lens Λ(x,x') of a diametral pair has diameter < Δ₂, so every Δ₂-pair has an endpoint in D.
- Only the KK bad-edge count fails here.
- This is likely easy (μΔ₂ looks small there), but it is unproved.

## 7. Status / honesty

- **Rigorous** (modulo the CDL/Vesztergombi black boxes and routine asymptotic ε-bookkeeping): Lemmas 1–2,
  Proposition R, the band lemma, the bad-edge counts, and Theorem A.
- **Sketched:** Remark A′ (32/23); the lens-corner proximity step. The latter is elementary compactness; it
  should be written out with explicit R₀(κ).
- **Open:** the window √3/2 < t/δ ≤ 1 and the degenerate regime. **An unconditional L < 3/2 is NOT proved.**
- **Novel as far as I can tell:** the reduction to e(S) ≤ |S|, the ball-polygon K picture (S∖D ⊂ ∂K), the band
  lemma, and the identification of the resonant window with its rhombic-strip obstruction.

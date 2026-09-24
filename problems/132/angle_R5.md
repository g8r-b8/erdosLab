# Erdős #132, angle R5: the global view (full question (a) for n ≥ n₀)

Date: 2026-09-23. Coordinator R5, with sub-routes A (computation), B (Case II structure) and C (Δ₃ / top-k theory; C was killed by an outage after writing its scripts, and its exact family is re-run below).
Scripts: `problems/132/scripts/r5_*.py`. Scratch: `scratchpad/R5/{A,B,C}/`.

## Notation

- Δ = Δ₁ > Δ₂ > Δ₃ > … are the distances of X in decreasing order, and μ_j = μ(Δ_j).
- L_d is the d-th convex layer, d(x) is the depth of x, and m₃ = #{x : d(x) ≥ 3}.
- G is the Δ₂-graph and G′ its 2-core. t_k = #{p ∈ L₁′ : deg′ p = k}.
- V_Δ is the set of endpoints of Δ-pairs.
- A **counterexample** is a set X with n ≥ 5 in which every non-diameter distance has μ ≥ n+1.

## 0. Summary

1. **Case split** (§1). A counterexample must have D ≤ ⌊n/2⌋, and it must lie in Case II (μ₂ ≥ n+1). Case II forces t₃/2 + t₄ ≥ m₃ + 1 and |L₁| > m₃.
2. **PROVED, new (§2).** Strong localisation lemma: a pair at distance Δ_j satisfies d(x) + d(y) ≤ j + 1.
3. **PROVED, new (§3, route B).** Local structure theorem at hull vertices of Δ₂-degree ≥ 3, and the **trapezoid lemma**, which forces concyclic isosceles trapezoids with Ptolemy relation Δ² = Δ₂² + |xp|·|ub|. Also a partial charging theorem: each (x, orientation) carries at most 2 hooks, with equality only in one rigid "core configuration".
4. **CONJECTURED (§3.4, strong evidence).** The Charge Lemma: the core configuration does not exist. It implies
   **μ(Δ₂) ≤ |L₁| + |L₂| + |V_Δ|**,
   which is tight on odd and even rings. Case II would then force |V_Δ| ≥ m₃ + μ₂ − n.
5. **Negative results, exact (§4, routes A and C).**
   - "min(μ₂, μ₃) ≤ n" is **false**. There is an exact n = 8 example with μ₂ = μ₃ = 9.
   - There is an exact family (odd ring + depth-3 points) with min(μ₂, μ₃) ≈ 6n/5, verified for m = 9, 11, 13.
   - So any proof of (a) via "Δ₂ or Δ₃ is rare" is impossible. At least Δ₄, or another distance, must enter.
6. **Computational picture (§5).** Over about 3,500 states with μ₂ > n, the first rare index j (the least j ≥ 2 with μ_j ≤ n) was always 3 or 4. No set was found with μ₂, μ₃, μ₄ > n. The best value of min_{2≤j≤4} μ_j − n was 0 (odd regular polygons, and a 12-point lattice set).
7. **Remaining gap (§6).** Prove (Conjecture R5.4) that μ₂, μ₃, μ₄ > n is impossible, or find a non-top distance that is rare in Case II.

## 1. The global case split for a counterexample X

**(C0) Counting (Lemma B, angle_C).**
- C(n,2) ≥ μ(Δ) + (D−1)(n+1), and hence D ≤ ⌊n/2⌋.
- For even n with D = n/2, equality holds throughout: μ(Δ) = 1, and every other class has size exactly n+1.
- For odd n, D ≤ (n−1)/2 with total slack (n+1)/2.
- So X has at most as many distinct distances as the Altman minimum ⌊n/2⌋ for convex n-sets, even though X need not be convex.
- Consequences: every point sees ≤ ⌊n/2⌋ distinct distances (B3); no line carries ≥ ⌊n/2⌋ + 2 points (B1); few points lie on any non-degenerate curve (B2).

**(C1) Case I: μ₂ ≤ n.** Then (a) holds. So X lies in Case II: μ₂ ≥ n+1.

**(C2) Case II, via Theorem A (Lean: E132Layer).**
- n + 1 ≤ μ₂ ≤ |L₁| + |L₂| + t₃/2 + t₄. So t₃/2 + t₄ ≥ m₃ + 1, and |L₁| ≥ m₃ + 1.
- By the middle lemma (Lean: E132Ve87), t₄ ≤ #{core vertices of degree 2}. By the unconditional Cor A1, Σ_{p∈L₁}(min(h(p),4) − 2)⁺ ≥ 2m₃ + 1.
- Every excess unit is a **hook** (§3), which carries forced Δ-pairs and concyclic trapezoids. So Case II sets are rigid near the hull.

**(C3) Δ₃.** Both μ₃ ≤ n and μ₃ > n occur in Case II (§4). So Case II must split again:
- **(C3a)** μ₃ ≤ n: done.
- **(C3b)** μ₃ ≥ n+1: open. Every example found has μ₄ ≤ n (§5).

**(C4) Distances other than the top ones.**
- In every example found, the bottom of the spectrum (δ and lattice-type distances) can be rich. Penny-graph bounds (μ(δ) ≤ 3n − |L₁|) are ≥ 2n, so they give nothing.
- So the rare distance has to be sought at the top of the spectrum, where rigidity lives. Beyond Δ₂, this rigidity is currently unproved.

**Why no summation bound can close the problem.**
- R_n (n odd) has μ_j = n for every j. Any bound of the form Σ_{j≤J} μ_j ≤ c_J·n therefore has c_J ≥ J.
- A counterexample needs only Σ_{j=2}^{J} μ_j ≥ (J−1)(n+1), which is less than Jn.
- So the argument must be an equality or stability argument, not a counting argument. The problem sits exactly at the regular-polygon extremum, where every class has size n.

## 2. Strong localisation lemma (PROVED)

**Lemma L.** Let x ∈ L_d with d ≥ 2, and let y ≠ x be any point of X. Then there is z ∈ L_{d−1} with z ≠ x such that
- (z − x)·(x − y) ≥ 0, and
- |zy| > |xy|.

Consequently, if |xy| = Δ_j, then d(x) + d(y) ≤ j + 1.

**Proof.**
1. Let Y = X \ (L₁ ∪ … ∪ L_{d−2}). Then L_{d−1} is the set of extreme points (vertices) of conv Y, and x ∈ Y is not extreme in Y.
2. Let φ(z) = (z − x)·(x − y). This is a non-zero linear functional, since y ≠ x.
3. The maximum of φ over Y is attained on a face of conv Y, so it is attained at some extreme point z ∈ L_{d−1}.
4. Since x ∈ conv(Y \ {x}), we have max_Y φ ≥ φ(x) = 0. If the only maximiser were x, then φ(x) would be strictly larger than φ at every other point of Y, which is impossible for a point of conv(Y \ {x}). So we may take z ≠ x with φ(z) ≥ 0.
5. Then |zy|² = |zx|² + |xy|² + 2φ(z) > |xy|².
6. For the corollary, apply the first part repeatedly to the deeper endpoint. Each application lowers d(x) + d(y) by 1 and strictly increases the distance. Reaching depths (1,1) takes d(x) + d(y) − 2 steps, and the final distance is ≤ Δ. So the rank satisfies j ≥ d(x) + d(y) − 1. ∎

For j = 1, 2 this recovers the facts proved in Lean: Δ-pairs lie in L₁, and Δ₂-pairs lie in L₁ ∪ L₂ with an endpoint in L₁.

For Δ₃ the possible depth types are (1,1), (1,2), (1,3) and (2,2).
- The equality structure of type (2,2): every z ≠ x in the half-plane H_x(y) lies in L₁ with |zy| = Δ₂.
- The equality structure of type (1,3): the witnesses of depth ≥ 2 have depth 2 and are at distance Δ₂ from y.
- Both follow from the same chain, because the chain must use exactly the ranks 3 → 2 → 1.
- They were checked exactly on random subsets of integer grids with collinear and cocircular coincidences (`r5_c_loccheck.py`: 20,507 instances of (L), 25,774 of (S), 58 of (T22), 5 of (T13); 0 failures).

## 3. Case II structure (route B)

Normalise Δ₂ = 1. Let p be extreme with G-neighbours w₁, …, w_h in angular order; they lie in an open half-plane. A neighbour w is **middle** if p has neighbours strictly on both sides of the line pw.

A **hook (p, w, x; b)** consists of:
- p extreme and w a middle neighbour of p;
- x ≠ p a Δ₂-neighbour of w;
- b the outer neighbour of p on the far side of line pw from x;
- |xb| = Δ.

The **orientation** of the hook is the side of p relative to the directed line x→w.

Σ_{p∈L₁′}(deg′ p − 2) equals the number of pairs (p, w) with w a middle core neighbour of p, and each such pair gives a hook whose x lies in the core. **So the Theorem A excess is at most the number of hooks.**

### 3.1 Theorem 1: local picture at p ∈ L₁ with h ≥ 3 (PROVED)

The inputs are Lemma M, Lemma F and `mid_pair_real` (E132Ve87).

**(a)** Only w₂ and w_{h−1} can have Δ₂-neighbours other than p. This is Lemma F.

**(b)** Let x ≠ p be a neighbour of w₂.
- x is never on the line pw₂. Otherwise x = 2w₂ − p and Δ = 2, and the neighbours a, c of p on the two sides would need cos∠ = 1/4 each. That gives |ac| = 2 sin 75.5° ≈ 1.94 ∈ (1, 2), a contradiction.
- If h ≥ 4:
  - x lies strictly on the w₃ side, by the argument of Lemma F.
  - |xw₁| = Δ, by Lemma M.
  - deg_G(w₂) = 2, by the middle lemma.
- If h = 3:
  - x is at distance Δ from whichever outer neighbour lies on the opposite side.
  - Two such x on the same side would both lie on C(w₂, 1) ∩ C(w_out, Δ), which `mid_pair_real` forbids.
  - So deg_G(w₂) ≤ 3.

**(c)** Consequences for the core degree of p.
- **deg′ p = 4.** The core neighbours sit at G-positions 1, 2, h−1 and h. The middle ones are degree-2 "servers" whose other endpoints x₂, x₃ are hull vertices with |x₂w₁| = |x₃w_h| = Δ. In particular w₁ and w_h are diameter endpoints.
- **deg′ p = 3.** At least one outer neighbour is a diameter endpoint.

**(d)** At a vertex of core degree 4, x₂ ≠ x₃. Suppose x₂ = x₃ = x, so x = w₂ + w₃ with p = 0.
- If ∠w₂w₃ ≤ 60°: then |px| ≥ √3, so |px| = Δ. The conditions |xw₁| = |xw₄| = Δ give cos∠(w₁, w₂) + cos∠(w₁, w₃) = 1/2 and the mirror identity. These force ∠w₁w₃ ≥ 120° and ∠w₂w₄ ≥ 120°, so the neighbours span ≥ 180°, which contradicts the half-plane fact.
- If ∠w₂w₃ > 60°: then |w₂w₃| > 1, so |w₂w₃| = Δ and |w₁w₃| > Δ, a contradiction.

### 3.2 Theorem 2: trapezoid lemma (PROVED, new; the algebra is in `r5_b_sympy.py`, and I re-derived it by hand)

**Statement.** Let (p, w, x; b) be a hook and u a Δ₂-neighbour of x strictly on the far side of line xw from p. Then:
1. |up| = Δ (Lemma M centred at x).
2. x, p, b, u form a concyclic isosceles trapezoid (Lemma T), with xp ∥ ub, legs xu = pb = 1 and diagonals xb = pu = Δ. Ptolemy gives **Δ² = 1 + |xp|·|ub|**.
3. w lies on the axis of symmetry, on the same side of xp as u and b.

**Proof of 3.**
1. Coordinates: x = (−σ, 0), p = (σ, 0), u = (−τ, −δ), b = (τ, −δ). The relation Δ² = 1 + 4στ gives τ > 0. Put w = (0, ±k) with k² = 1 − σ² and δ² = 1 − (τ − σ)².
2. Suppose w = (0, +k). The two side conditions give τ > σ.
3. Then |wu|² = 2 + 2kδ + 2σ(τ − σ) > 2, so |wu| = Δ, which gives **1 + 2kδ = 2σ(σ + τ)**.
4. Now split on the lengths 2σ = |xp| and 2τ = |ub|, each of which is ≤ 1 or equal to Δ:
   - **2σ, 2τ ≤ 1.** The right side is ≤ 1, but the left side is > 1.
   - **2τ = Δ.** Then 2σ = Δ − 1/Δ ≤ 1, so Δ ≤ φ. The right side is ≤ φ − 1/(2φ) ≈ 1.31. On the left side, k ≥ √3/2 and τ − σ = 1/(2Δ) ≤ 1/2 give δ ≥ √3/2, so the left side is ≥ 2.5. Contradiction.
   - **2σ = Δ.** Then 2τ = Δ − 1/Δ < 2σ, which contradicts τ > σ.
   - **2σ = 2τ = Δ** would require Δ² = 1 + Δ², which is impossible. ∎

**Corollaries.**
- **Reversed hooks.** If w is also a middle neighbour of x, then (x, w, p; u) is a hook, and the mirror-symmetric 5-point gadget is exactly the Reuleaux interleaving of the rings.
- If Δ > √2·Δ₂, then one of |xp|, |ub| equals Δ.

### 3.3 Theorem 3: charging at x (PROVED, partial)

Let x have Δ₂-neighbours u₁, …, u_k in angular order.

- **Lemma F′.** For a hook through u_i, at most one neighbour of x lies strictly beyond the line xu_i on the side away from p. The case with near side empty needs p = 2cos γ·e(γ) with γ > 90°, which makes x non-extreme.
- Hence hooks with p on the clockwise side go only through u_{k−1} or u_k.
- **Lemma D.** Two hooks through the same w have opposite orientations.
- `mid_pair_real` at x allows at most one hook of a given orientation through u_{k−1}.
- **Conclusion.** Each (x, orientation) carries ≤ 2 hooks. Equality holds only in the **core configuration**: hooks through both u_{k−1} and u_k with the same orientation. That configuration contains the trapezoid (x, p, b, u_k) with |pu_k| = Δ.

**Proved stability.**
- μ₂ ≥ (1+ε)n implies #hooks ≥ 2εn + 2m₃.
- Each hook carries two forced Δ-pairs.
- Each hook with a far-side neighbour carries a concyclic trapezoid.
- The hooks have at least (εn + m₃)/2 distinct endpoints x.

### 3.4 Charge Lemma (CONJECTURED)

**Conjecture.** The core configuration does not exist.

**Consequence.** Then t₃/2 + t₄ ≤ |V_Δ ∩ L₁′|, and therefore

  **μ(Δ₂) ≤ |L₁| + |L₂| + |V_Δ| = n − m₃ + |V_Δ|.**

- This is tight: odd rings give 3m = 2m + m, and even rings give 3m = 2m + m.
- It is not true with μ(Δ) in place of |V_Δ|: even rings have μ₂ = 3m > 2.5m.
- By Hopf–Pannwitz, |V_Δ| = μ(Δ) + #(acyclic components of the Δ-graph).

**Evidence.** Every check had 0 violations.
- Exact Z[ω] cliques with r² ≤ 49: 76,187 sets, 5,062 hooks and 2,904 trapezoid tests.
- Exact Z[i] cliques with r² ≤ 65: 128,827 sets and 755 hooks.
- Float data: rings m = 5..21 under six server patterns, and 3,997 greedy sets (3,596 of them in Case II, 31,339 hooks).
- Core-configuration scan (`r5_b_core.py`): all 697 partial completions die, because the second hook's p′ has no admissible third neighbour.

**What is left to prove.** The core configuration has 2 trapezoid parameters (σ, τ) plus p′, b′, c′, and Lemma M gives nothing more. Numerically the chain is:
1. b′ = b is forced;
2. p′ lies on the axis above xp (σ > 2τ);
3. this forces |c′p| = Δ;
4. which puts c′ on the wrong side of line p′u.

A rigorous version needs this chain proved, or an interval-arithmetic proof that includes the stratum b′ = b.

**Not proved.** Stability down to a near-regular polygon. Adjacent trapezoids share only one point. Greedy Case II sets had 98% of hull vertices concyclic, but a 10-point three-cluster Reuleaux-type set (μ₂ = 14) is not.

**Related, from angle_R2 (commit 2f1f194).** Conjecture C1 of angle_C is false: there are convex sets with no 4 concyclic points and μ(Δ₂) = 5n/4 (n = 4m ≥ 12). In those sets every other distance is simple, so (a) holds there, but the second rare distance is not Δ₂.

## 4. Negative results: Δ₃ can be frequent in Case II (exact)

**E1 (route A, independently re-verified by R5 in `r5_verify_n8.py`, exact sympy).**
- Construction: take the regular pentagon P_k = e(2πk/5). Put s₃ = √3, s₅ = √5, w = √(10 + 2s₅), w₂ = √(10 − 2s₅), and add three points:
  - p₅ = ((3 − s₅ + s₃w₂)/8, (5s₃ + s₃s₅ + w₂)/8);
  - p₆ = ((3 + s₅ − s₃w)/8, (5s₃ − s₃s₅ − w)/8);
  - p₇ = ((−1 − s₅ + s₃w₂)/4, 0).
- The points are defined by circle conditions: p₅ is the equilateral apex on P₀P₂; |p₆P₀| = |P₀P₁|; |p₆P₁| = |p₇P₁| = |P₁p₅|; |p₇P₀| = |P₂p₆|.
- Result: n = 8 with squared-distance spectrum (multiplicities, decreasing) **2, 9, 9, 5, 2, 1**. So μ₂ = μ₃ = 9 > 8.
- Route A found no such set at n = 7. That search is not a proof.

**E2 (route C family, exact via `r5_c_exact.py`).**
- Construction: take the regular odd m-gon V_j = e(2πj/m).
- Add the servers S_j = −t·e(2π(j+½)/m), with |S_jV_j| = |S_jV_{j+1}| = Δ₂(R_m).
- Add the depth-3 points P_j = −ρ·e(2π(j+½)/m) for j ∈ K, with |P_jV_j| = |P_jV_{j+1}| = Δ₃.
- With |K| = k: **μ₁ = m, μ₂ = 3m, μ₃ = 2m + 2k, μ₄ = m, and n = 2m + k.**
- This is certified exactly for m = 9 (k = 0, 1, 3, 4, 9), m = 11 (k = 1, 5, 11) and m = 13 (k = 1, 6, 13), with class gaps ≥ 6·10⁻³. General m is expected by the same orbit computation but is not proved here.
- Taking k = (m−1)/2 gives min(μ₂, μ₃) − n = (m−1)/2 and min(μ₂, μ₃)/n → **6/5**.
- So "min(μ₂, μ₃) ≤ n + o(n)" also fails.
- In every member of the family, Δ₄ (multiplicity m) is rare, and so are many others (about 18 rare distances at m = 9, k = 1).

## 5. Computational picture (route A)

Methods: rings, symmetric-orbit beams, layered concentric polygons, cyclotomic and lattice annealing, and constructible-pool annealing. Scripts: `r5_a_search.py`, `r5_a_rings.py`, `r5_a_cyclo.py`, `r5_a_poolsa.py`, plus the exact tower checker `r5_a_exact.py`.

- **J = 3.** Ring_m plus k points gives margin min(k, m − k). The margin grows linearly with n.
- **J = 4, 5, 6.** The best value of min_{2≤j≤J} μ_j − n is **0**, attained by odd regular polygons and by the triangular-lattice n = 12 set with spectrum [3, 12, 12, 15, 24]. Every search stayed ≤ 0. A gadget census found no admissible point of top-degree ≥ 3 near any ring.
- **First rare index.** Over about 3,500 states with μ₂ > n, it was always 3 or 4.
- **Budget heuristic (not a proof).**
  - Model: q polygon-type classes of size m each, plus k added points that each carry Δ_j-degree 2 in one top class.
  - Requiring K = J − 1 classes to exceed n = qm + k + 1 gives K(qm + k + 1) ≤ 2m(q − 1 + K) + Σ deg_top(added).
  - This is infeasible for K = 3 in all cases q ≤ 3, and K = 2 is the model's limit, which matches the data.
  - Beating it needs "arithmetic coincidences": added points with degree ≥ 3 in some top class, or points hitting several top classes at once.

**Conjecture R5.4.** For n ≥ 5, min(μ₂, μ₃, μ₄) ≤ n. This would prove (a). Weaker version: some fixed J has min_{2≤j≤J} μ_j ≤ n for n ≥ n₀.

## 6. Precise remaining gap and next steps

The reduction chain for (a) at n ≥ n₀:

1. **Case I** (μ₂ ≤ n): done.
2. **Case II with μ₃ ≤ n**: done.
3. **Case II with μ₃ ≥ n+1**: **open**.
   - Needed: Δ₄, or some j ≤ J, is rare.
   - Tools available: Lemma L (Δ₄-pairs have depth sum ≤ 5), and the rigid hook/trapezoid structure near the hull.
   - Missing: an analogue of Lemma M / Prop 3 for Δ₃ and Δ₄. Lemma M uses that every distance above Δ₂ is Δ, and with two or three distances above, the opposite-side argument yields only "∈ {Δ, Δ₂}".

Most promising next steps:
- **(i) Prove the Charge Lemma** by interval arithmetic on the 5-parameter core configuration. This gives the clean bound μ₂ ≤ n − m₃ + |V_Δ| and the structural corollary |V_Δ| ≥ m₃ + μ₂ − n.
- **(ii) Build a Δ₃-core theory** (was route C, killed by the outage): the depth-type analysis of Lemma L, plus core degrees in the Δ₃-graph.
- **(iii) Run J = 4 searches** in pools that contain the server radii, to stress-test Conjecture R5.4.

## Files

- `r5_profiles.py`: top-multiplicity profiles and `ring(m)`.
- `r5_augment.py`: greedy Δ_j-augmentation.
- `r5_verify_n8.py`: exact check of E1.
- `r5_a_*.py`: route A searches and the exact tower checker.
- `r5_b_*.py`: route B lemma checks (exact lattice, float, core scan, sympy).
- `r5_c_*.py`: route C (exact family E2, localisation checks, searches).

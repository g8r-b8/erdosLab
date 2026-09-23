import Erdos.E132Layer

/-!
# Erdős Problem 132: Vesztergombi 1987 — the second-largest distance occurs at most `3n/2` times

K. Vesztergombi, *On large distances in planar sets*, Discrete Math. 67 (1987) 191–198:
for every finite `X ⊆ ℝ²`, `2 μ(Δ₂) ≤ 3 |X|`.

We do **not** follow Vesztergombi's deletion/induction proof (deleting points can change `Δ` and
`Δ₂`).  Instead we work in the 2-core `G′` of the `Δ₂`-graph on `L₁ ∪ L₂`, reusing
`Erdos.E132Layer` (location of `Δ₂`-pairs, Prop 3, `deg′ ≤ 4` on `L₁′`, `esum_le_core`):

* (**middle lemma**, new; Ve87's "it is easy to see" in Prop 7) if `p` is extreme and `w` is a
  `Δ₂`-neighbour of `p` with one neighbour `b` of `p` strictly on one side of the line `pw` and two
  neighbours `a₁, a₂` strictly on the other side (in angular order), then `w` has at most one
  `Δ₂`-neighbour besides `p`.  (Lemma F puts every such neighbour `r` strictly on the `a`-side,
  Lemma M gives `|rb| = Δ`, and two such `r ≠ r'` are mirror images in the line `wb`, which is
  incompatible with `|pr|, |pr'| ∈ (0, Δ₂] ∪ {Δ}`.)
* hence every `p ∈ L₁′` of core degree `4` has two core neighbours (its middle neighbours) of core
  degree `2`;
* core degrees lie in `[2, 4]` (Prop 3 and `deg′ ≤ 4`), so a double count of the edges between
  degree-4 and degree-2 vertices gives `#{deg′ = 4} ≤ #{deg′ = 2}`, hence `Σ deg′ ≤ 3 |V(G′)|`;
* `2 μ(Δ₂) = esum(L₁ ∪ L₂) ≤ esum(G′) + 2 |(L₁ ∪ L₂) \ V(G′)| ≤ 3 |L₁ ∪ L₂| ≤ 3 |X|`.

The final statement `vesztergombi87` has the shape of `Erdos132Main.vesztergombi87`
(`E132MainDefs.lean`), with local copies `diam`, `dist2` of the definitions there.
-/

open Finset
open Erdos132Convex

namespace Erdos132Ve87

open Erdos132Layer

/-! ## The middle lemma -/

/-- **Middle lemma, real core.**  Frame: `p = 0`, `w = (1, 0)`, `b` a unit vector strictly above
the axis.  `r = w + u` and `s = w + v` (`u, v` unit, strictly below the axis) are both at squared
distance `D` from `b`, and each of `|r|², |s|²` is `≤ 1` or `= D`.  Then `r = s`.

TODO: prove.
What's missing: `r ≠ s` ⇒ `(u + v) × (w − b) = 0` ⇒ `u₀ + v₀ > 0`; case split on the gaps; in the
mixed case `UV = −B` (complex product) gives `b₀ = v₀ + 1/2 ≤ 0`, contradicting `u₀ + v₀ > 0`.
Acceptance: no `sorry`.
Depends on: nothing. -/
theorem mid_pair_real {u0 u1 v0 v1 b0 b1 D : ℝ} (hD : 1 < D)
    (hu : u0 ^ 2 + u1 ^ 2 = 1) (hv : v0 ^ 2 + v1 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 = 1)
    (hu1 : u1 < 0) (hv1 : v1 < 0) (hb1 : 0 < b1)
    (er : (1 + u0 - b0) ^ 2 + (u1 - b1) ^ 2 = D) (es : (1 + v0 - b0) ^ 2 + (v1 - b1) ^ 2 = D)
    (gr : (1 + u0) ^ 2 + u1 ^ 2 ≤ 1 ∨ (1 + u0) ^ 2 + u1 ^ 2 = D)
    (gs : (1 + v0) ^ 2 + v1 ^ 2 ≤ 1 ∨ (1 + v0) ^ 2 + v1 ^ 2 = D) :
    u0 = v0 ∧ u1 = v1 := by
  sorry

/-- **Middle lemma.**  Let `p` have `Δ₂`-neighbours `w, a₁, a₂, b` with (for a sign `σ = ±1`)
`a₁, a₂` strictly on one side of the line `pw`, `b` strictly on the other, and `b` after `a₁, a₂`
in angular order.  Then `w` has at most one `Δ₂`-neighbour other than `p`.

TODO: prove.
What's missing: frame at `p` with axis `w` and second coordinate multiplied by `σ`;
`lemmaF_real` puts every other neighbour strictly on the `a`-side, `lemmaM_real` (reflected)
gives distance `Δ` to `b`, then `mid_pair_real`.
Acceptance: no `sorry`.
Depends on: `mid_pair_real`, `Erdos132Layer.lemmaF_real`, `Erdos132Layer.lemmaM_real`. -/
theorem mid_nbr_unique {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {p w a₁ a₂ b : Pt}
    (hw : w ∈ X) (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X) (hb : b ∈ X)
    (dw : dist p w = Δ₂) (da₁ : dist p a₁ = Δ₂) (da₂ : dist p a₂ = Δ₂) (db : dist p b = Δ₂)
    (hna : a₁ ≠ a₂)
    (oa₁ : σ * orient p w a₁ < 0) (oa₂ : σ * orient p w a₂ < 0) (ob : 0 < σ * orient p w b)
    (o₁ : 0 < σ * orient p a₁ b) (o₂ : 0 < σ * orient p a₂ b)
    {r s : Pt} (hr : r ∈ X) (hs : s ∈ X) (hrp : r ≠ p) (hsp : s ≠ p)
    (dr : dist w r = Δ₂) (ds : dist w s = Δ₂) : r = s := by
  sorry

/-! ## Angular order and core vertices of degree 4 -/

/-- The `Δ₂`-neighbours (in a set `S` of size `k`) of an extreme point can be listed in strict
angular order.

TODO: prove.
What's missing: the slope-function sort of `Erdos132Layer.exists_median`, for general `k`.
Acceptance: no `sorry`.
Depends on: `Erdos132Layer.eq_of_orient_zero`. -/
theorem exists_sorted {X : Finset Pt} {Δ₂ : ℝ} {p : Pt} (hp : IsExt X p) {S : Finset Pt}
    (hSX : S ⊆ X) (hS : ∀ x ∈ S, dist p x = Δ₂) (hpos : 0 < Δ₂) {k : ℕ} (hk : S.card = k) :
    ∃ f : Fin k → Pt, (∀ i, f i ∈ S) ∧ Function.Injective f ∧
      ∀ i j, i < j → 0 < orient p (f i) (f j) := by
  sorry

/-- A core vertex `p ∈ L₁` of core degree `4` has at least two core neighbours of core degree
`2` (its two middle neighbours).

TODO: prove.
What's missing: sort the four neighbours `f 0, …, f 3`; apply `mid_nbr_unique` to `f 1`
(`σ = −1`) and `f 2` (`σ = 1`); core degree `≥ 2` from `minDeg2_core`.
Acceptance: no `sorry`.
Depends on: `exists_sorted`, `mid_nbr_unique`. -/
theorem two_le_mid {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p : Pt}
    (hp : p ∈ L1 X) (h4 : (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card = 4) :
    2 ≤ ((nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).filter
      (fun w => (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ w).card = 2)).card := by
  sorry

/-! ## Counting -/

/-- **Double count.**  In a graph with all degrees in `[2, 4]` in which every vertex of degree
`4` has two neighbours of degree `2`, the degree sum is at most `3 |K|`.

TODO: prove.
What's missing: count pairs (degree-4 vertex, adjacent degree-2 vertex) both ways:
`2 #{deg 4} ≤ … ≤ 2 #{deg 2}`; then `deg v + [deg v = 2] ≤ 3 + [deg v = 4]` pointwise.
Acceptance: no `sorry`.
Depends on: nothing. -/
theorem esum_le_three {K : Finset Pt} {d : ℝ}
    (hlo : ∀ v ∈ K, 2 ≤ (nbr K d v).card) (hhi : ∀ v ∈ K, (nbr K d v).card ≤ 4)
    (h4 : ∀ v ∈ K, (nbr K d v).card = 4 →
      2 ≤ ((nbr K d v).filter (fun w => (nbr K d w).card = 2)).card) :
    esum K d ≤ 3 * K.card := by
  sorry

/-- **Vesztergombi 1987** (for the two largest distances `Δ > Δ₂`): `2 μ(Δ₂) ≤ 3 |X|`.

TODO: prove.
What's missing: `two_mul_multS`, `esum_eq_esum_L12`, `esum_le_core`, `esum_le_three` on the core
(degrees from `deg_core_L2`, `deg_core_L1_le_four`, `two_le_mid`).
Acceptance: no `sorry`.
Depends on: `esum_le_three`, `two_le_mid`. -/
theorem ve87 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    2 * multS X Δ₂ ≤ 3 * X.card := by
  sorry

/-! ## The statement in the shape of `Erdos132Main.vesztergombi87` -/

section MainShape

open scoped Classical

/-- Diameter (copy of `Erdos132Main.diam`). -/
noncomputable def diam (X : Finset Pt) : ℝ :=
  if h : (distSetS X).Nonempty then (distSetS X).max' h else 0

/-- Second-largest distance (copy of `Erdos132Main.dist2`). -/
noncomputable def dist2 (X : Finset Pt) : ℝ :=
  if h : ((distSetS X).erase (diam X)).Nonempty then ((distSetS X).erase (diam X)).max' h else 0

/-- **[Ve87]** in the shape of `Erdos132Main.vesztergombi87`:
`μ(Δ₂) ≤ (3/2)|Y|` for every finite planar `Y` (with `Δ₂ = 0`, `μ = 0` if `Y` determines fewer
than two distances).

TODO: prove.
What's missing: if `distSetS Y` has `≥ 2` elements, `TwoLargest Y (diam Y) (dist2 Y)` and `ve87`;
otherwise `dist2 Y = 0` and `multS Y 0 = 0`.
Acceptance: no `sorry`.
Depends on: `ve87`. -/
theorem vesztergombi87 (Y : Finset Pt) : (multS Y (dist2 Y) : ℝ) ≤ 3 / 2 * Y.card := by
  sorry

end MainShape

end Erdos132Ve87

import Erdos.E132Main97Defs

/-!
# Erdős Problem 132, `τ > 1`: the `D`-part and the splitting `G = G[D] ⊔ G[X ∖ D]`

`problems/132/angle_R6.md` §5.3, steps 1–2.

* `t = Δ − Δ₂ > 1` ⇒ no unit distance between `D` and `X ∖ D` (`one_lt_dist_D_Y`): for `z ∈ D`
  with diametral partner `x`, every `y ∉ D` has `|y − x| ≤ Δ₂`, so `|z − y| ≥ Δ − Δ₂ > 1`.
  Hence `e(X) = e(D) + e(X ∖ D)` (`mult_split`).
* `Def(G[D]) ≥ 2|S ∩ D| − cBad` (`dpart`).  Deviation from the paper (which extends the
  T-edge machinery of WRITEUP_A2 to all of `D`): the repo's `DirField` lives on `S` only, so we
  use `deg ≤ 3` on `D` for the points of `D ∖ S`, and on `S ∩ D`: good edges are T-edges (no
  rungs for `τ > 1`), at most one left and one right T-neighbour each (`T1`), bad edges
  `≤ cBad` (`card_bad_le`).  So `e(D) ≤ |S ∩ D| + cBad + 3|D ∖ S|`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- A diametral point has `δ`-degree `≤ 3` (own copy: `degδ_le_three_of_D` of
`E132Main43Defs` is still a `sorry` there, and that file is not ours to edit).

TODO: prove.
What's missing: for a diametral partner `w` of `z` (`|zw| = Δ`) every `δ`-neighbour `q` has
`|q − w| ≤ Δ`, hence `(q − z)·(w − z) ≥ |q − z|²/2 > 0`: the unit vectors `q − z` lie in the
open half-circle around `(w − z)/Δ`; pairwise `≥ 1` apart means pairwise angle `≥ 60°`, so at
most 3.  Copy `card_sep_arc_le_four` (E132MainLocal / Main15N1) with the open half-circle cone.
Acceptance: no `sorry`.
Depends on: `dist_le_diam`, `one_le_dist`, `card_sep_arc_le_four` pattern. Difficulty M. -/
theorem degδ_le_three_of_D97 (hX : Normal X) {z : Pt} (hz : z ∈ Dset X) : degδ X z ≤ 3 := by
  sorry

/-- `t > 1` ⇒ points of `D` are at distance `> 1` from points of `X ∖ D`.

TODO: prove.
What's missing: partner `x ∈ X` of `z` with `dist z x = diam X`; `y ∉ D` gives
`dist y x ≤ dist2 X` (`dist_le_dist2`, `dist_ne_diam_of_not_mem_Dset`; if `x = y` then
`dist z y = diam X ≥ tgap X > 1` directly); triangle inequality.
Acceptance: no `sorry`.
Depends on: `dist_le_dist2`, `dist_ne_diam_of_not_mem_Dset`, `mem_partners`. Difficulty S. -/
theorem one_lt_dist_D_Y (ht : 1 < tgap X) {z y : Pt} (hz : z ∈ Dset X) (hy : y ∈ Yset X) :
    1 < dist z y := by
  sorry

/-- `e(X) = e(D) + e(X ∖ D)` when `t > 1`.

TODO: prove.
What's missing: every unit pair of `X` lies in `D` or in `Yset X` (by `one_lt_dist_D_Y`);
`mult_eq_card` and a filter/disjoint-union count on `pairsS`.  (`≤` suffices downstream.)
Acceptance: no `sorry`.
Depends on: `one_lt_dist_D_Y`, `mult_eq_card`, `mem_pairsAt`. Difficulty M. -/
theorem mult_split (ht : 1 < tgap X) :
    (mult X 1 : ℝ) ≤ mult (Dset X) 1 + mult (Yset X) 1 := by
  sorry

/-- Unit edges inside `S ∩ D` number `≤ |S ∩ D| + cBad` for `τ > 1`.

TODO: prove.
What's missing: unit pairs of `S ∩ D` are `edges X` whose both ends are in `D`; good ones are
T-edges (`good_subset_T_union_rungs`, `rungs_eq_empty`); a T-edge `pq` with both ends in `S ∩ D`
makes `q` the left or right T-neighbour of `p` (as in `card_tEdges_le`), each unique (`T1`), so
`two_mul_card_le_of_deg_le` with `V = S ∩ D`, `k = 2`; bad ones `≤ cBad` (`card_bad_le`).
Acceptance: no `sorry`.
Depends on: `dirField_nonempty`, `good_subset_T_union_rungs`, `rungs_eq_empty`, `T1`,
`card_bad_le`, `two_mul_card_le_of_deg_le`. Difficulty M. -/
theorem mult_SD_le (hX : Normal X) (hτ : 1 < tau X) :
    (mult (Sset X ∩ Dset X) 1 : ℝ) ≤ (Sset X ∩ Dset X).card + cBad := by
  sorry

/-- **The `D`-part** (§5.3 step 2): `Def(G[D]) ≥ 2|S ∩ D| − cBad`.

TODO: prove.
What's missing: `mult_le_add_sum (S ∩ D) D 1`: `e(D) ≤ e(S ∩ D) + Σ_{z ∈ D ∖ S} deg z`;
`deg ≤ 3` (`degδ_le_three_of_D97`; `partners (Dset X) 1 z ⊆ partners X (minDist X) z`);
`|D| = |S ∩ D| + |D ∖ S|`; `mult_SD_le`.
Acceptance: no `sorry`.
Depends on: `mult_le_add_sum`, `degδ_le_three_of_D97`, `mult_SD_le`. Difficulty M. -/
theorem dpart (hX : Normal X) (hτ : 1 < tau X) :
    2 * ((Sset X ∩ Dset X).card : ℝ) - cBad ≤ defc (Dset X) := by
  sorry

end

end Erdos132Main

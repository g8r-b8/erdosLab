import Erdos.E132Main97Defs

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A1: arcs of directions and Step 5

`problems/132/lean/L97_reports/RouteA_visiblepath_report.md` §2 Step 5 (per-vertex angular
counting, "replaces the angle sum of faces"), refereed in `L97_reports/REF_core_report.md` §2.6.
DAG and fill order: `problems/132/lean/MAIN97_PLAN.md`, section "Visible-path DAG".

* `arcO a b`: the open arc of directions from angle `a` counter-clockwise to angle `b`.
* `card_le_of_free_arcs` (Step 5): unit neighbours pairwise `≥ 60°` apart avoiding `k` open arcs
  of total (union) measure `μ` number at most `3(2π − μ)/π + k`.
* measure bookkeeping for unions of arcs (`dirMeasure` of `E132ConvexCurve.lean`).

Everything here is 1-dimensional (angles in `ℝ`, `dirVec`, Lebesgue measure on `[0, 2π)`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

open Curve (dirMeasure le_dirMeasure_of_Icc sum_dirMeasure_le)

noncomputable section

/-- The open arc of directions `{dirVec θ : a < θ < b}` (counter-clockwise from `a` to `b`). -/
def arcO (a b : ℝ) : Set Pt := dirVec '' Set.Ioo a b

/-- The preimage of an open arc under `dirVec` is measurable (it is open).

TODO: prove.
What's missing: `dirVec ⁻¹' arcO a b = ⋃ k : ℤ, Ioo (a + 2πk) (b + 2πk)` (use
`dirVec_add_int_mul` and the `2π`-periodic injectivity of `dirVec`), or directly: it is open since
`dirVec` restricted to a period is an open map onto the circle.
Acceptance: no `sorry`.
Depends on: `dirVec_add_int_mul`, `exists_angle`. Difficulty S–M. -/
theorem measurableSet_arcO (a b : ℝ) : MeasurableSet (dirVec ⁻¹' arcO a b) := by
  sorry

/-- An open arc of length `b − a ≤ 2π` has direction measure at least `b − a`.

TODO: prove.
What's missing: for `ε > 0` the closed arc `[a + ε, b − ε]` lies in `arcO a b`; apply
`le_dirMeasure_of_Icc` and let `ε → 0` (`le_of_forall_pos_le_add`).
Acceptance: no `sorry`.
Depends on: `le_dirMeasure_of_Icc`. Difficulty S. -/
theorem le_dirMeasure_arcO {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a + 2 * π) :
    b - a ≤ dirMeasure (arcO a b) := by
  sorry

/-- `dirMeasure` of any set is at most `2π`.

TODO: prove.
What's missing: the set measured is a subset of `Ico 0 (2π)` (`measure_mono`, `Real.volume_Ico`).
Acceptance: no `sorry`.
Depends on: definition of `dirMeasure`. Difficulty S. -/
theorem dirMeasure_le_two_pi (Q : Set Pt) : dirMeasure Q ≤ 2 * π := by
  sorry

/-- Union bound with one distinguished set: for pairwise disjoint `W j` (`j ∈ s`) and one more set
`H`, all with measurable `dirVec`-preimages,
`dirMeasure (⋃ W ∪ H) ≥ Σ dirMeasure (W j) + dirMeasure H − Σ dirMeasure (W j ∩ H)`.

TODO: prove.
What's missing: `μ(U ∪ H) = μ U + μ H − μ(U ∩ H)` (`measure_union_add_inter`), `μ U = Σ μ(W j)`
(`measure_biUnion_finset`, disjointness), `μ(U ∩ H) ≤ Σ μ(W j ∩ H)` (`measure_biUnion_finset_le`);
all measures are finite (`≤ 2π`), so `toReal` commutes with the sums.
Acceptance: no `sorry`.
Depends on: `dirMeasure_le_two_pi`. Difficulty M. -/
theorem dirMeasure_union_ge {ι : Type*} (s : Finset ι) (W : ι → Set Pt) (H : Set Pt)
    (hW : ∀ j ∈ s, MeasurableSet (dirVec ⁻¹' W j)) (hH : MeasurableSet (dirVec ⁻¹' H))
    (hdisj : (s : Set ι).PairwiseDisjoint W) :
    ∑ j ∈ s, dirMeasure (W j) + dirMeasure H - ∑ j ∈ s, dirMeasure (W j ∩ H) ≤
      dirMeasure ((⋃ j ∈ s, W j) ∪ H) := by
  sorry

/-- Pairwise disjoint version without a distinguished set:
`Σ dirMeasure (W j) ≤ dirMeasure (⋃ W j)`.

TODO: prove.
What's missing: `dirMeasure_union_ge` with `H = ∅` (or `measure_biUnion_finset` directly).
Acceptance: no `sorry`.
Depends on: `dirMeasure_union_ge`. Difficulty S. -/
theorem sum_dirMeasure_le_union {ι : Type*} (s : Finset ι) (W : ι → Set Pt)
    (hW : ∀ j ∈ s, MeasurableSet (dirVec ⁻¹' W j)) (hdisj : (s : Set ι).PairwiseDisjoint W) :
    ∑ j ∈ s, dirMeasure (W j) ≤ dirMeasure (⋃ j ∈ s, W j) := by
  sorry

/-- **Step 5 (per-vertex angular counting).**  Let `N` be unit neighbours of `v`, pairwise at
distance `≥ 1` (hence pairwise `≥ 60°` apart as seen from `v`), and let `k = |s|` open arcs of
directions (each of length `≤ 2π`) contain no direction `q − v`, `q ∈ N`.  Then
`|N| ≤ 3(2π − μ)/π + k`, `μ` the measure of the union of the arcs.

Why true: if `N = ∅` the right side is `≥ 0` (`μ ≤ 2π`).  Otherwise the neighbour angles cut the
circle into `|N|` open gaps of length `≥ π/3`; each arc lies inside one gap; a gap containing no arc
contributes `≥ π/3` to `2π − μ`, and at most `k` gaps contain arcs.  So
`2π − μ ≥ (|N| − k)π/3`.  (REF_core §2.6: also correct for touching arcs and empty arcs.)

TODO: prove.
What's missing: sort the neighbour angles (`exists_angle`, `Finset.sort`), 60° separation from
`dist = 1`, `dist ≥ 1` (chord `2 sin(θ/2) ≥ 1`), the gap decomposition of `[θ₁, θ₁ + 2π)`, and
measure of the arcs inside each gap (`dirMeasure` restricted to a gap).  Alternatively reuse the
cyclic packing in `card_sep_arc_le_three` (E132Main97DPart) / `card_le_of_sep` (E132ConvexCurve).
Acceptance: no `sorry`.
Depends on: `le_dirMeasure_arcO`, `dirMeasure_le_two_pi`, `measurableSet_arcO`, `exists_angle`.
Difficulty M–L (≈ 250 lines). -/
theorem card_le_of_free_arcs {v : Pt} {N : Finset Pt} (hN : ∀ q ∈ N, dist q v = 1)
    (hsep : ∀ q ∈ N, ∀ q' ∈ N, q ≠ q' → 1 ≤ dist q q')
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (hab : ∀ j ∈ s, a j ≤ b j ∧ b j ≤ a j + 2 * π)
    (hfree : ∀ q ∈ N, ∀ j ∈ s, q - v ∉ arcO (a j) (b j)) :
    (N.card : ℝ) ≤ 3 * (2 * π - dirMeasure (⋃ j ∈ s, arcO (a j) (b j))) / π + s.card := by
  sorry

end

end Erdos132Main

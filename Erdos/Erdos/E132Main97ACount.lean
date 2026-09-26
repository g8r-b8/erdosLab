import Erdos.E132Main97APath

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A7: counting A against pieces, collapse sum

`L97_reports/RouteA_visiblepath_report.md` §2 Step 8 (CL) and the collapse term of Step 7,
refereed in `REF_core_report.md` §2.7.  Arc length is replaced by `eVariationOn` of the exit map
`θ ↦ exitPt θ`; the constants are generous (`CoreE` allows `E(h) = 3·10⁶h²`, the proof needs
`O(h)`).

* `card_le_one_add_var`: `1`-separated values of a map on `[α, β]` number `≤ 1 + variation`.
* `cl_bound` (CL): `|A ∩ V| ≤ n + J + 50h`.
* `sum_alpha_le`: `Σ_{a ∈ A} α_a ≤ 10 + 100h` (from `α_a ≤ ψ_c`, `#(A ∩ Z_c) ≤ 1 + 5hψ_c`,
  `Σψ_c ≤ 2π`, `ψ_c ≤ 3`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical ENNReal

namespace Erdos132Main

open Curve (dirMeasure)

noncomputable section

variable {X : Finset Pt} {ρ : ℕ}

/-- **Chord ≤ variation, counted.**  If the values of `f` at the points of a finite `T ⊆ [α, β]`
are pairwise `≥ 1` apart and `f` has finite variation on `[α, β]`, then
`|T| ≤ 1 + Var(f, [α, β])`.

Why true: sort `T`; consecutive values are `≥ 1` apart and `edist (f t) (f t') ≤` the variation on
`[t, t']` (`eVariationOn.edist_le`); the variations on consecutive intervals add up
(`eVariationOn.Icc_add_Icc`) to at most the total.

TODO: prove.
Acceptance: no `sorry`.
Depends on: Mathlib `eVariationOn` API. Difficulty M (≈ 120 lines). -/
theorem card_le_one_add_var (f : ℝ → Pt) {α β : ℝ} {T : Finset ℝ}
    (hT : ∀ t ∈ T, t ∈ Set.Icc α β)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ dist (f t) (f t'))
    (hfin : eVariationOn f (Set.Icc α β) ≠ ⊤) :
    (T.card : ℝ) ≤ 1 + (eVariationOn f (Set.Icc α β)).toReal := by
  sorry

/-- **(CL) counting A against pieces** (report Step 8):
`|A ∩ V| ≤ n + J + 50h`.

Why true: every `a ∈ A ∩ V` is a vertex, so `ν(a)` is an event and `a = exitPt ν(a)`
(`exitPt_A`); A-points are `≥ 1` apart.  Each hit arc `[ev s, ev t]` (maximal run of hit
intervals; a single event between two escape intervals is a one-ray hit arc) is tiled by the
pieces; each piece is a sub-segment (length `≤ 1`) of one edge with a monotone lift of `ν`
(`nu_segment`), so `var_exit_piece` bounds its exit variation by `Δ₂/R′ + 5h·Δν`.  Summing
(`card_le_one_add_var` on each hit arc, or on one full turn if `J = 0`, which costs one extra piece
and one extra `1`): `|A ∩ V| ≤ J + 1 + (Δ₂/R′)(n + 1) + 10πh`.  If `n ≥ |A ∩ V|` the claim is
trivial; otherwise `(Δ₂/R′ − 1)(n + 1) = (h/R′)(n + 1) ≤ (h/R′)·7Δ₂ ≤ 7.04h` by
`card_A_le_seven`, and `2 + 7.04h + 10πh ≤ 50h` for `h ≥ 3/2`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `card_le_one_add_var`, `var_exit_piece`, `nu_segment`, `exitPt_A`, `nuAng_injOn_A`,
`card_A_le_seven`, `Valid` (`hit_edge`, `foot`, `L_spec`, `R_spec`, `vertex_ev`),
`eVariationOn.Icc_add_Icc`. Difficulty L (≈ 500 lines). -/
theorem cl_bound (hC : CoreHyp X (hh ρ)) {P : VisPath} (hP : P.Valid X (hh ρ) (Hv X ρ)) :
    ((Aset X ∩ Hv X ρ).card : ℝ) ≤ P.nP (Hv X ρ) + P.J + 50 * hh ρ := by
  sorry

/-- **Collapse sum** (report Step 7, last display): `Σ_{a ∈ A} α_a ≤ 10 + 100h`.

Why true: group `A` by `c = projK a`; `α_a ≤ ψ_c` (`alpha_le_ncone`), the group has
`≤ 1 + 5hψ_c` elements (`card_A_proj_le`), `ψ_c ≤ 3` (`dirMeasure_ncone_le`) and
`Σ_c ψ_c ≤ 2π` (`sum_dirMeasure_ncone_le`): `Σ α ≤ Σ_c ψ_c(1 + 15h) ≤ 2π(1 + 15h)`.

TODO: prove.
What's missing: `Finset.sum_fiberwise` over the image `(Aset X).image (projK X h)`, and the
arithmetic.
Acceptance: no `sorry`.
Depends on: `alpha_le_ncone`, `card_A_proj_le`, `dirMeasure_ncone_le`,
`sum_dirMeasure_ncone_le`, `A_normal_spec`. Difficulty S–M. -/
theorem sum_alpha_le {h : ℝ} (hC : CoreHyp X h) :
    ∑ a ∈ Aset X, alphaA X h a ≤ 10 + 100 * h := by
  sorry

end

end Erdos132Main

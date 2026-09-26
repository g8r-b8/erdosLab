import Erdos.E132Main97APath

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A6: the wedge lemma and the A-corners

`L97_reports/RouteA_visiblepath_report.md` §2 Step 4 (wedge lemma) and Step 6 (A-corners),
refereed in `REF_core_report.md` §2.5–2.6.

* `wedge_lemma` (Step 4, per occurrence — **G1**): for a direction `d` in the wedge of a vertex
  occurrence and small `s > 0`, the point `v + s d` is in `K′` or strictly below the first hit of
  its ray (`ClearTo`); if the occurrence is not an end, its ray is actually hit beyond it
  (`BelowHit`), so the point lies in `K`.
* `wedge_free`: no edge of the vertex points into the wedge (from the wedge lemma).
* `wedge_A_inner` / `wedge_A_end` (Step 6): at `a ∈ A` the wedge misses `H⁺_a`, resp. overlaps it
  in measure `≤ π/2 + α_a` (**G2** is used for `−ν(a)` being strictly inner).
* `half_free`: the chord inequality in terms of `halfArc`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical Topology

namespace Erdos132Main

open Curve (dirMeasure)

noncomputable section

variable {X : Finset Pt} {ρ : ℕ}

/-- `x` is strictly below the visible path: no drawing point on its ray up to `x`. -/
def ClearTo (X : Finset Pt) (h : ℝ) (V : Finset Pt) (x : Pt) : Prop :=
  ∀ t, 0 < t → t ≤ tPar X h x → rayPt X h (nuAng X h x) t ∉ drawing V

/-- `x` is strictly below the visible path and its ray is hit beyond `x`. -/
def BelowHit (X : Finset Pt) (h : ℝ) (V : Finset Pt) (x : Pt) : Prop :=
  ClearTo X h V x ∧ ∃ t, tPar X h x < t ∧ rayPt X h (nuAng X h x) t ∈ drawing V

/-- **Wedge lemma (Step 4), per occurrence.**  Let `o` be a vertex occurrence with wedge `W_o`
and `d ∈ W_o`.  For all small `s > 0` the point `o.pt + s d` is in `K′` or `ClearTo`; if `o` is not
an end (both sides of the path real), it is in `K′` or `BelowHit`.

Why true (report Step 4, REF_core §2.5): in polar coordinates about the pole of the relevant side
(N3; the pole lies on the line of the ray `ν₀`, behind `v`), a half-line from `v` with relative
angle `ψ ∈ (0, π)` meets the pole ray of polar angle `δ` at distance `D sin ψ / sin(ψ − δ)`,
decreasing in `ψ`; so directions beyond `ψout` (towards `−ν₀`) give points nearer than the path,
and likewise on the other side with `ψin`; outward-jump sides are farther still; the ray segment
below `v` is free (`v` is the first hit, or lies above a jump); on a virtual side all rays escape.
Different occurrences of one vertex (the dip) are handled separately — each wedge lies below its
own two path pieces.

TODO: prove.
What's missing: the local pole description (N3) at arc and corner ranges and at their
boundaries (`rayPt_coords`, `suppPt`), the sine-rule monotonicity, and the case analysis over the
three kinds of occurrence (`L`, `B`, `R`) using `Valid`.
Acceptance: no `sorry`.
Depends on: `Valid`, `rayPt_coords`, `ray_decomp`, `nu_segment`, `ang_dirVec_sub`,
`corner_on_ray`. Difficulty XL (≈ 900 lines). -/
theorem wedge_lemma (hC : CoreHyp X (hh ρ)) {P : VisPath} (hP : P.Valid X (hh ρ) (Hv X ρ))
    {o : Occ} (ho : o ∈ P.vOcc (Hv X ρ)) {d : Pt} (hd : d ∈ o.wedge) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (o.pt + s • d ∈ Kin X (hh ρ) ∨ ClearTo X (hh ρ) (Hv X ρ) (o.pt + s • d)) ∧
      (o.isEnd = false →
        o.pt + s • d ∈ Kin X (hh ρ) ∨ BelowHit X (hh ρ) (Hv X ρ) (o.pt + s • d)) := by
  sorry

/-- No edge of a vertex points into the wedge of any of its occurrences.

Why true: if `q − v ∈ W_o` for a unit neighbour `q`, the points `v + s(q − v)` (`0 < s ≤ 1`) are
drawing points off `K′` (`drawing_not_mem_Kin`), and each is the point of parameter `tPar` of
its own ray (`ray_decomp`), contradicting `ClearTo` from `wedge_lemma`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `wedge_lemma`, `drawing_not_mem_Kin`, `ray_decomp`, `Hv_spec`. Difficulty M. -/
theorem wedge_free (hC : CoreHyp X (hh ρ)) {P : VisPath} (hP : P.Valid X (hh ρ) (Hv X ρ))
    {o : Occ} (ho : o ∈ P.vOcc (Hv X ρ)) {q : Pt} (hq : q ∈ Hv X ρ) (hqo : dist q o.pt = 1) :
    q - o.pt ∉ o.wedge := by
  sorry

/-- A point below a hit lies in `K`: it is on the segment from `y(ν) ∈ K′ ⊆ K` to a drawing
point `∈ K` (`KBall_convex`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `ray_decomp`, `suppPt_spec`, `Kin_subset_KBall`, `drawing_subset_KBall_isCompact`,
`KBall_convex`. Difficulty S–M. -/
theorem mem_KBall_of_belowHit (hC : CoreHyp X (hh ρ)) {x : Pt} (hx : x ∉ Kin X (hh ρ))
    (hb : BelowHit X (hh ρ) (Hv X ρ) x) : x ∈ KBall X := by
  sorry

/-- **Chord inequality as a free arc**: unit neighbours `q ∈ K` of `a ∈ A` avoid `H⁺_a`
(`halfArc (φ_a)` is the set of unit directions `u` with `⟪u, n_a⟫ > 0`).

TODO: prove.
What's missing: `inner_nbr_neg`, `A_normal_spec`, `inner_dirVec`, and
`dirVec θ ∈ halfArc φ ↔ cos(θ − φ) > 0` (mod `2π`).
Acceptance: no `sorry`.
Depends on: `inner_nbr_neg`, `A_normal_spec`, `Yset_subset_KBall`, `Hv_spec`. Difficulty S–M. -/
theorem half_free (hC : CoreHyp X (hh ρ)) {a : Pt} (ha : a ∈ Aset X) {q : Pt}
    (hq : q ∈ Hv X ρ) (hqa : dist q a = 1) : q - a ∉ halfArc (phiA X a) := by
  sorry

/-- **Step 6, interior A-corner**: if `o` is a non-end occurrence at `a ∈ A`, then
`W_a ∩ H⁺_a = ∅`.

Why true (REF_core §2.6): the bounding directions of `W_a` are edge directions from `a` (strictly
inner by the chord inequality) or `−ν(a)` (strictly inner by G2, `inner_nuVec_pos`); there is no
outward jump from `a` and no inward-jump arrival at `a` (`a` is the last point of its ray in `K`,
`A_last_on_ray`).  `n_a ∉ W_a`: otherwise `a + s n_a ∈ K` for small `s` (`wedge_lemma` +
`mem_KBall_of_belowHit`), but `|a + s n_a − w_a| = Δ₂ + s`.  An arc of length `≤ 2π` with both
ends in the open inner half-circle and avoiding `n_a` misses `H⁺_a`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `wedge_lemma`, `mem_KBall_of_belowHit`, `inner_nuVec_pos`, `A_last_on_ray`,
`A_normal_spec`, `inner_nbr_neg`, `corner_on_ray`. Difficulty L (≈ 350 lines). -/
theorem wedge_A_inner (hC : CoreHyp X (hh ρ)) {P : VisPath} (hP : P.Valid X (hh ρ) (Hv X ρ))
    {o : Occ} (ho : o ∈ P.vOcc (Hv X ρ)) (hoA : o.pt ∈ Aset X) (hend : o.isEnd = false) :
    Disjoint o.wedge (halfArc (phiA X o.pt)) := by
  sorry

/-- **Step 6, A-endpoint**: if `o` is an end occurrence at `a ∈ A`, then
`|W_a ∩ H⁺_a| ≤ π/2 + α_a`.

Why true (REF_core §2.6): `o` is a `B`-corner with exactly one virtual side (both virtual would
make `a` the only drawing point of its ray with a non-radial edge — impossible); say the out-side
is virtual: `W_a = (ν₀, ν₀ + ψin + π)`, its far end `−d_in` is strictly inner, so
`W_a ∩ H⁺_a = (ν₀, φ_a + π/2)` of length `π/2 + (φ_a − ν₀) ≤ π/2 + α_a` (`|α_a| < π/2`, G2).
Symmetric for a virtual in-side.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `inner_nbr_neg`, `A_normal_spec`, `corner_on_ray`, `Valid`, `dirMeasure` of an arc
(`le_dirMeasure_arcO` and its upper-bound analogue). Difficulty M–L (≈ 250 lines). -/
theorem wedge_A_end (hC : CoreHyp X (hh ρ)) {P : VisPath} (hP : P.Valid X (hh ρ) (Hv X ρ))
    {o : Occ} (ho : o ∈ P.vOcc (Hv X ρ)) (hoA : o.pt ∈ Aset X) (hend : o.isEnd = true) :
    dirMeasure (o.wedge ∩ halfArc (phiA X o.pt)) ≤ π / 2 + alphaA X (hh ρ) o.pt := by
  sorry

end

end Erdos132Main

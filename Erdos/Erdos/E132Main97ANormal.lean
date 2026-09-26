import Erdos.E132Main97ALemma0
import Erdos.E132Main97AArcs
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A4: normal coordinates of `K′` (N1–N6)

`L97_reports/RouteA_visiblepath_report.md` §2 Step 1 (N1–N6), refereed in `REF_core_report.md`
§2.2 (fixes **G2** and **G3** are built into the statements below).

`K′ = ⋂_{w ∈ X} D(w, Δ₂ − h)` (`Kin`), compact, convex, with nonempty interior (Lemma 0, packed
into `CoreHyp.deep`).  Every `x ∉ K′` is `x = y(ν) + t·ν` with `y(ν) = suppPt ν` the (unique)
support point, `ν = nuVec x`, `t = tPar x > 0` (N2).  Angles are real numbers (`dirVec`), the ray
of angle `θ` is `t ↦ rayPt θ t`, and the exit point of that ray from `K` is `exitPt θ` (N5).

* **G3** (N4, `nu_segment`): along a segment avoiding `K′`, `ν` is constant (radial segment) or has
  a continuous strictly monotone lift whose direction of increase is the sign of
  `det2(ν, q − p)`.  Proof uses only injectivity + continuity (1-D topology).
* **G2** (`inner_nuVec_pos`): `⟪ν(x), x − w⟫ > 0` whenever `|x − w| = Δ₂`, because
  `D(projK x, h) ⊆ K`.  Consequently `α_a < π/2` and `−ν(a)` is strictly inner.
* N6 in discrete form: A-points with a common projection `c` number `≤ 1 + 5h·|N(c)|`
  (`card_A_proj_le`); the exit-point variation over a visible piece is
  `≤ (Δ₂/R′)·length + 5h·Δν` (`var_exit_piece`).  `eVariationOn` replaces arc length.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical ENNReal

namespace Erdos132Main

open Curve (dirMeasure)

noncomputable section

variable {X : Finset Pt}

/-! ## Definitions -/

/-- The inner parallel body `K′ = {depth ≥ h} = ⋂_w D(w, Δ₂ − h)`. -/
def Kin (X : Finset Pt) (h : ℝ) : Set Pt :=
  ⋂ w ∈ (X : Set Pt), Metric.closedBall w (dist2 X - h)

/-- The standing hypotheses of the core geometry (`CoreE` plus Lemma 0's conclusion). -/
structure CoreHyp (X : Finset Pt) (h : ℝ) : Prop where
  normal : Normal X
  h_ge : 3 / 2 ≤ h
  h_lt : h < dist2 X / 200
  deep : ∃ o, IsDeep X h o

/-- Support point of `K′` in direction `u` (a maximiser of `⟪·, u⟫`; junk `0` if none). -/
def suppPt (X : Finset Pt) (h : ℝ) (u : Pt) : Pt :=
  if hs : ∃ y ∈ Kin X h, ∀ z ∈ Kin X h, inner ℝ z u ≤ inner ℝ y u then hs.choose else 0

/-- Nearest point of `K′` (junk `x` if none). -/
def projK (X : Finset Pt) (h : ℝ) (x : Pt) : Pt :=
  if hs : ∃ y ∈ Kin X h, ∀ z ∈ Kin X h, dist x y ≤ dist x z then hs.choose else x

/-- Normal coordinate `t(x) = dist(x, K′)`. -/
def tPar (X : Finset Pt) (h : ℝ) (x : Pt) : ℝ := dist x (projK X h x)

/-- Normal direction `ν(x) = (x − P x)/|x − P x|` (unit for `x ∉ K′`). -/
def nuVec (X : Finset Pt) (h : ℝ) (x : Pt) : Pt := (tPar X h x)⁻¹ • (x - projK X h x)

/-- Normal angle of `x`, in `[0, 2π)`. -/
def nuAng (X : Finset Pt) (h : ℝ) (x : Pt) : ℝ :=
  if hs : ∃ θ ∈ Set.Ico 0 (2 * π), dirVec θ = nuVec X h x then hs.choose else 0

/-- The normal ray of angle `θ`: `rayPt θ t = y(θ) + t·dirVec θ`. -/
def rayPt (X : Finset Pt) (h : ℝ) (θ t : ℝ) : Pt := suppPt X h (dirVec θ) + t • dirVec θ

/-- Parameter of the exit point of the ray `θ` from `K`. -/
def exitT (X : Finset Pt) (h : ℝ) (θ : ℝ) : ℝ := sSup {t | 0 ≤ t ∧ rayPt X h θ t ∈ KBall X}

/-- The exit point `e(θ) ∈ ∂K` of the normal ray `θ` (N5). -/
def exitPt (X : Finset Pt) (h : ℝ) (θ : ℝ) : Pt := rayPt X h θ (exitT X h θ)

/-- Normal cone of `K′` at `c`, as a set of unit vectors: `N(c) = {u : y(u) = c}`. -/
def ncone (X : Finset Pt) (h : ℝ) (c : Pt) : Set Pt := {u | ‖u‖ = 1 ∧ suppPt X h u = c}

/-- A chosen `Δ₂`-partner of `a` (junk `a` if none). -/
def wA (X : Finset Pt) (a : Pt) : Pt :=
  if hs : ∃ w ∈ X, dist a w = dist2 X then hs.choose else a

/-- Angle of the outer disc normal `n_a = (a − w_a)/Δ₂`. -/
def phiA (X : Finset Pt) (a : Pt) : ℝ :=
  if hs : ∃ θ ∈ Set.Ico 0 (2 * π), dirVec θ = (dist2 X)⁻¹ • (a - wA X a) then hs.choose else 0

/-- `α_a`: the angle between the ray direction `ν(a)` and the disc normal `n_a`. -/
def alphaA (X : Finset Pt) (h : ℝ) (a : Pt) : ℝ := ang (nuVec X h a) (a - wA X a)

/-! ## N1–N2: the body `K′`, support points, the ray decomposition -/

/-- `K′ ⊆ K`.

TODO: prove.  What's missing: `closedBall_subset_closedBall` (`h ≥ 0`), `mem_KBall`.
Acceptance: no `sorry`.  Depends on: `mem_KBall`. Difficulty S. -/
theorem Kin_subset_KBall {h : ℝ} (hh : 0 ≤ h) : Kin X h ⊆ KBall X := by
  sorry

/-- `K′` is compact and convex.

TODO: prove.  What's missing: finite intersection of closed balls (`isCompact_closedBall`,
`IsCompact.inter_right`/`isClosed_biInter`, `convex_closedBall`, `convex_iInter₂`); `X ≠ ∅`.
Acceptance: no `sorry`.  Depends on: `Normal.four_le`. Difficulty S. -/
theorem Kin_isCompact_convex (hX : Normal X) (h : ℝ) :
    IsCompact (Kin X h) ∧ Convex ℝ (Kin X h) := by
  sorry

/-- An `h`-deep point lies in `K′`; in particular `K′ ≠ ∅` under `CoreHyp`.

TODO: prove.  What's missing: unfold `IsDeep`, `Kin`, `Metric.mem_closedBall`.
Acceptance: no `sorry`.  Depends on: definitions. Difficulty S. -/
theorem mem_Kin_of_deep {h : ℝ} {o : Pt} (ho : IsDeep X h o) : o ∈ Kin X h := by
  sorry

/-- A point with some centre farther than `Δ₂ − h` is not in `K′`.

TODO: prove.  What's missing: unfold `Kin`.
Acceptance: no `sorry`.  Depends on: definitions. Difficulty S. -/
theorem not_mem_Kin_of_far {h : ℝ} {x w : Pt} (hw : w ∈ X) (hxw : dist2 X - h < dist x w) :
    x ∉ Kin X h := by
  sorry

/-- The support point exists and maximises `⟪·, u⟫` on `K′`.

TODO: prove.  What's missing: `IsCompact.exists_isMaxOn` for the continuous map `⟪·, u⟫` on the
nonempty compact `K′`; then `dif_pos` and `Exists.choose_spec`.
Acceptance: no `sorry`.  Depends on: `Kin_isCompact_convex`, `mem_Kin_of_deep`. Difficulty S. -/
theorem suppPt_spec {h : ℝ} (hC : CoreHyp X h) (u : Pt) :
    suppPt X h u ∈ Kin X h ∧ ∀ z ∈ Kin X h, inner ℝ z u ≤ inner ℝ (suppPt X h u) u := by
  sorry

/-- **(N1) strict convexity**: for a unit `u` the maximiser of `⟪·, u⟫` on `K′` is unique.

Why true: two maximisers `y₁ ≠ y₂` give a midpoint `m` with `|m − w| < Δ₂ − h` for every `w`
(strict convexity of the Euclidean ball, `R′ = Δ₂ − h > 0`), so `m + εu ∈ K′` beats both.

TODO: prove.
What's missing: parallelogram law / `norm_add_lt_of_not_sameRay`-type strict convexity.
Acceptance: no `sorry`.  Depends on: `suppPt_spec`. Difficulty M. -/
theorem suppPt_unique {h : ℝ} (hC : CoreHyp X h) {u y : Pt} (hu : ‖u‖ = 1) (hy : y ∈ Kin X h)
    (hmax : ∀ z ∈ Kin X h, inner ℝ z u ≤ inner ℝ y u) : y = suppPt X h u := by
  sorry

/-- **(N2) ray decomposition**: every `x ∉ K′` is `x = rayPt (nuAng x) (tPar x)` with `tPar x > 0`,
`ν(x)` unit, `nuAng x ∈ [0, 2π)`, and the nearest point is the support point of `ν(x)`.

Why true: the nearest point `c` satisfies `⟪z − c, x − c⟫ ≤ 0` for all `z ∈ K′`
(`norm_eq_iInf_iff_real_inner_le_zero`), so `c` maximises `⟪·, ν⟫`; `suppPt_unique`.

TODO: prove.
What's missing: existence of the nearest point (`IsCompact.exists_isMinOn`), the variational
inequality, `exists_angle`.
Acceptance: no `sorry`.  Depends on: `suppPt_unique`, `exists_angle`. Difficulty M. -/
theorem ray_decomp {h : ℝ} (hC : CoreHyp X h) {x : Pt} (hx : x ∉ Kin X h) :
    0 < tPar X h x ∧ ‖nuVec X h x‖ = 1 ∧ nuAng X h x ∈ Set.Ico 0 (2 * π) ∧
      dirVec (nuAng X h x) = nuVec X h x ∧ projK X h x = suppPt X h (nuVec X h x) ∧
      x = rayPt X h (nuAng X h x) (tPar X h x) := by
  sorry

/-- **(N2) rays are disjoint and parametrised by `(θ mod 2π, t > 0)`**: the coordinates of
`rayPt θ t` are `ν = dirVec θ`, `t`, and angle `θ mod 2π`.

Why true: `y = suppPt (dirVec θ)` maximises `⟪·, dirVec θ⟫`, so `⟪z − y, (y + tν) − y⟫ ≤ 0` for
`z ∈ K′`: `y` is the nearest point of `y + tν`.

TODO: prove.
What's missing: the converse variational inequality, uniqueness of the nearest point, and
`dirVec` injectivity on `[0, 2π)` (`toIcoMod`).
Acceptance: no `sorry`.  Depends on: `suppPt_spec`, `ray_decomp`. Difficulty M. -/
theorem rayPt_coords {h : ℝ} (hC : CoreHyp X h) (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    rayPt X h θ t ∉ Kin X h ∧ nuVec X h (rayPt X h θ t) = dirVec θ ∧
      tPar X h (rayPt X h θ t) = t ∧
      nuAng X h (rayPt X h θ t) = toIcoMod Real.two_pi_pos 0 θ := by
  sorry

/-! ## N4 (G3): the normal angle along a segment -/

/-- **(N4), with the referee's proof (G3).**  Along a segment `[p, q]` avoiding `K′`, either `ν` is
constant (the segment lies in one ray), or `ν` has a continuous strictly monotone lift `Θ` on
`[0, 1]`, increasing iff `det2(ν, q − p) > 0` (the path direction is to the left of the ray),
with `det2(ν, q − p)` of constant nonzero sign.

Why true (REF_core §2.2): (i) `ν` is continuous off `K′` (the projection is 1-Lipschitz);
(ii) a segment not contained in one ray meets each ray at most once (two distinct lines meet
once; a point with `det2(ν(x), q − p) = 0` puts a neighbourhood of `x` in `σ` on the ray of `x`),
so `ν|σ` is injective and its continuous lift is strictly monotone
(`Continuous.strictMono_of_inj`-type, 1-D); (iii) the local pole picture (N3) gives the sign.

TODO: prove.
What's missing: continuity of `projK` (1-Lipschitz nearest-point map onto a convex set), a
continuous lift of a continuous unit-vector path on `[0, 1]` (e.g. via `Complex.arg` on a
half-plane containing `ν(σ)`: separate `σ` from `K′` by a line), injectivity ⇒ strict
monotonicity, and the sign computation.
Acceptance: no `sorry`.
Depends on: `ray_decomp`, `rayPt_coords`, `suppPt_spec`. Difficulty L (≈ 500 lines). -/
theorem nu_segment {h : ℝ} (hC : CoreHyp X h) {p q : Pt} (hpq : p ≠ q)
    (hσ : ∀ x ∈ segment ℝ p q, x ∉ Kin X h) :
    (∀ x ∈ segment ℝ p q, nuVec X h x = nuVec X h p) ∨
    ∃ Θ : ℝ → ℝ, ContinuousOn Θ (Set.Icc 0 1) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, dirVec (Θ s) = nuVec X h (p + s • (q - p))) ∧
      ((StrictMonoOn Θ (Set.Icc 0 1) ∧
          ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < det2 (dirVec (Θ s)) (q - p)) ∨
        (StrictAntiOn Θ (Set.Icc 0 1) ∧
          ∀ s ∈ Set.Icc (0 : ℝ) 1, det2 (dirVec (Θ s)) (q - p) < 0)) := by
  sorry

/-- **Relative angle telescopes** (Step 3's only analytic input): if `d` stays strictly to the
left of `dirVec θ` for all `θ ∈ [α, β]`, then `ψ(θ) = ang(dirVec θ, d)` decreases exactly as fast
as `θ` increases: `ψ(α) − ψ(β) = β − α`.

Why true: `sin(φ − θ) > 0` on `[α, β]` for an angle `φ` of `d`, so a single lift `φ` has
`φ − θ ∈ (0, π)` throughout (IVT), and `ang(dirVec θ, dirVec φ) = φ − θ` there.

TODO: prove.
What's missing: `inner_dirVec`, `InnerProductGeometry.angle` as `arccos`, `Real.arccos_cos`, the
branch argument.
Acceptance: no `sorry`.  Depends on: `inner_dirVec`, `exists_angle`. Difficulty M. -/
theorem ang_dirVec_sub {d : Pt} {α β : ℝ} (hαβ : α ≤ β)
    (hd : ∀ θ ∈ Set.Icc α β, 0 < det2 (dirVec θ) d) :
    ang (dirVec α) d - ang (dirVec β) d = β - α := by
  sorry

/-! ## N5 (G2): A-points on their rays -/

/-- **G2**: if `|x − w| = Δ₂` (`x ∉ K′`, `w ∈ X`), then `t(x)·⟪ν(x), x − w⟫ ≥ hΔ₂ > 0`.

Why true (REF_core §2.2): `c = projK x ∈ K′` has `|c − w| ≤ Δ₂ − h`, so with `n = (x − w)/Δ₂`,
`⟪c − x, n⟫ = ⟪c − w, n⟫ − Δ₂ ≤ −h`; and `x − c = t(x)·ν(x)`.

TODO: prove.
Acceptance: no `sorry`.  Depends on: `ray_decomp`, `real_inner_le_norm`. Difficulty S–M. -/
theorem inner_nuVec_pos {h : ℝ} (hC : CoreHyp X h) {x w : Pt} (hx : x ∉ Kin X h) (hw : w ∈ X)
    (hxw : dist x w = dist2 X) :
    h * dist2 X ≤ tPar X h x * inner ℝ (nuVec X h x) (x - w) := by
  sorry

/-- A-points are not in `K′` (they have depth `0 < h`).

TODO: prove.  Acceptance: no `sorry`.
Depends on: `exists_partner_of_mem_Aset`, `not_mem_Kin_of_far`. Difficulty S. -/
theorem A_not_mem_Kin {h : ℝ} (hC : CoreHyp X h) {a : Pt} (ha : a ∈ Aset X) : a ∉ Kin X h := by
  sorry

/-- **(N5) an A-point is the last point of its ray inside `K`**: beyond `t(a)` the ray leaves
`D(w, Δ₂)`.

Why true: `|a + sν − w|² = Δ₂² + 2s⟪ν, a − w⟫ + s² > Δ₂²` for `s > 0` by G2.

TODO: prove.
Acceptance: no `sorry`.  Depends on: `inner_nuVec_pos`, `ray_decomp`. Difficulty S–M. -/
theorem A_last_on_ray {h : ℝ} (hC : CoreHyp X h) {a : Pt} (ha : a ∈ Aset X) {t : ℝ}
    (ht : tPar X h a < t) : rayPt X h (nuAng X h a) t ∉ KBall X := by
  sorry

/-- **(N5)** every A-point is the exit point of its own ray: `e(ν(a)) = a`.

Why true: the set `{t ≥ 0 : rayPt t ∈ K}` is an interval containing `[0, t(a)]` (convexity,
`y(ν) ∈ K′ ⊆ K`) and nothing beyond `t(a)` (`A_last_on_ray`), so its `sSup` is `t(a)`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `A_last_on_ray`, `ray_decomp`, `Kin_subset_KBall`, `Yset_subset_KBall`. Difficulty M. -/
theorem exitPt_A {h : ℝ} (hC : CoreHyp X h) {a : Pt} (ha : a ∈ Aset X) :
    exitPt X h (nuAng X h a) = a := by
  sorry

/-- One A-point per ray: `nuAng` is injective on `A`.

TODO: prove.  What's missing: `exitPt_A` on both points.
Acceptance: no `sorry`.  Depends on: `exitPt_A`. Difficulty S. -/
theorem nuAng_injOn_A {h : ℝ} (hC : CoreHyp X h) : Set.InjOn (nuAng X h) (Aset X : Set Pt) := by
  sorry

/-- **Chord inequality**: a point `y ∈ K` at distance `1` from a point `a` of `C(w, Δ₂)` lies in the
open inner half-plane of `a`: `⟪y − a, a − w⟫ ≤ −1/2 < 0`.

TODO: prove.  What's missing: `|y − w|² = |y − a|² + 2⟪y − a, a − w⟫ + |a − w|²`, `mem_KBall`.
Acceptance: no `sorry`.  Depends on: `mem_KBall`. Difficulty S. -/
theorem inner_nbr_neg {a y w : Pt} (hy : y ∈ KBall X) (hw : w ∈ X) (haw : dist a w = dist2 X)
    (hya : dist y a = 1) : inner ℝ (y - a) (a - w) < 0 := by
  sorry

/-- The chosen partner, the normal angle and `α_a` behave: `w_a ∈ X`, `|a − w_a| = Δ₂`,
`dirVec (φ_a) = (a − w_a)/Δ₂`, `0 ≤ α_a < π/2` (the last by G2).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exists_partner_of_mem_Aset`, `exists_angle`, `inner_nuVec_pos`, `A_not_mem_Kin`.
Difficulty S–M. -/
theorem A_normal_spec {h : ℝ} (hC : CoreHyp X h) {a : Pt} (ha : a ∈ Aset X) :
    wA X a ∈ X ∧ dist a (wA X a) = dist2 X ∧
      dirVec (phiA X a) = (dist2 X)⁻¹ • (a - wA X a) ∧
      0 ≤ alphaA X h a ∧ alphaA X h a < π / 2 := by
  sorry

/-! ## N1/N6: normal cones and collapse zones -/

/-- Normal cones of distinct points are disjoint, so their direction measures sum to `≤ 2π`.

TODO: prove.
What's missing: `suppPt` is continuous on unit vectors (strict convexity), so each
`dirVec ⁻¹' ncone c` is closed; the sets are pairwise disjoint; `sum_dirMeasure_le` with `M = 1`.
Acceptance: no `sorry`.  Depends on: `suppPt_unique`, `sum_dirMeasure_le`. Difficulty M. -/
theorem sum_dirMeasure_ncone_le {h : ℝ} (hC : CoreHyp X h) (C : Finset Pt) :
    ∑ c ∈ C, dirMeasure (ncone X h c) ≤ 2 * π := by
  sorry

/-- **(N1) corner angles**: `ψ_c = |N(c)| ≤ 2 arcsin(194/199) < 3`.

Why true: `N(c)` is spanned by `(c − w₁)/R′, (c − w₂)/R′` for two active centres, and
`sin(ψ_c/2) = |w₁ − w₂|/(2R′) ≤ 0.97Δ₂/(199Δ₂/200) = 194/199` (`Δ ≤ 1.94Δ₂`, `h < Δ₂/200`).

TODO: prove.
What's missing: the description of the normal cone of a finite intersection of discs (active
constraints; Slater via `CoreHyp.deep`), `Real.arcsin` bound.
Acceptance: no `sorry`.  Depends on: `suppPt_spec`, `suppPt_unique`. Difficulty M–L. -/
theorem dirMeasure_ncone_le {h : ℝ} (hC : CoreHyp X h) (c : Pt) :
    dirMeasure (ncone X h c) ≤ 3 := by
  sorry

/-- **(N5) `α_a ≤ ψ_c`**: both `ν(a)` and the disc normal `n_a` lie in `N(c)`, `c = projK a`.

Why true: `ν(a) ∈ N(c)` by `ray_decomp`; `n_a ∈ N_K(a) ⊆ N(c)` (monotone Gauss map along the
collapse arc `Z_c = ∂K ∩ (c + N(c))`, whose ends `c + hν_i` have unique normals `ν_i`); `N(c)` is
a closed arc of length `< π`.

TODO: prove.
Acceptance: no `sorry`.  Depends on: `ray_decomp`, `A_normal_spec`, `dirMeasure_ncone_le`.
Difficulty L. -/
theorem alpha_le_ncone {h : ℝ} (hC : CoreHyp X h) {a : Pt} (ha : a ∈ Aset X) :
    alphaA X h a ≤ dirMeasure (ncone X h (projK X h a)) := by
  sorry

/-- **(N6) collapse count**: the A-points projecting to one point `c` of `∂K′` number at most
`1 + 5h·ψ_c`.

Why true (report N6 + P7): they lie on the collapse arc `Z_c`, consecutive ones are `≥ 1` apart,
chord `≤` arc, and `len Z_c ≤ κhψ_c` with `κ = 199/√1965 < 4.49` (support-function identity
`len Z_c = ∫_{N(c)} H`, and `Z_c` inside the kite `c, p₁, T, p₂`).  If `N(c)` is a single direction
there is one ray, hence at most one A-point.

TODO: prove.
What's missing: the kite containment and either the support-function integral or a discrete
chord-sum argument (sorted by angle about `c`); may share internals with `var_exit_piece`.
Acceptance: no `sorry`.
Depends on: `exitPt_A`, `nuAng_injOn_A`, `dirMeasure_ncone_le`. Difficulty L–XL (≈ 500 lines). -/
theorem card_A_proj_le {h : ℝ} (hC : CoreHyp X h) (c : Pt) :
    (((Aset X).filter (fun a => projK X h a = c)).card : ℝ) ≤
      1 + 5 * h * dirMeasure (ncone X h c) := by
  sorry

/-- **Exit-point variation over a visible piece** (report Step 8.4, arc-length-free).  Let a segment
`[x, y]` avoid `K′` with a continuous monotone lift `Θ` of `ν` along it.  Then the exit point moves
by at most `(Δ₂/R′)·|xy| + 5h·(Θ 1 − Θ 0)` (`R′ = Δ₂ − h`), measured by `eVariationOn`.

Why true: on an arc range (centre `w`), `e(θ) = w + Δ₂·dirVec θ` while the segment point is
`w + s(θ)·dirVec θ` with `s ≥ R′`, so `|de| = Δ₂ dθ ≤ (Δ₂/R′)|dx|`; on a corner range `e` runs
along `Z_c` with `|de| ≤ κh dθ`, `κ < 4.49` (N6).

TODO: prove.
What's missing: the arc/corner decomposition of the `θ`-range (finitely many ranges, N1), the
two local estimates on subintervals (`eVariationOn` of a Lipschitz-in-`θ` map, e.g.
`LipschitzOnWith.comp_eVariationOn_le`), additivity (`eVariationOn.Icc_add_Icc`).
Acceptance: no `sorry`.
Depends on: `rayPt_coords`, `nu_segment`, `card_A_proj_le` internals. Difficulty XL (≈ 800 lines). -/
theorem var_exit_piece {h : ℝ} (hC : CoreHyp X h) {x y : Pt}
    (hσ : ∀ z ∈ segment ℝ x y, z ∉ Kin X h) {Θ : ℝ → ℝ}
    (hΘc : ContinuousOn Θ (Set.Icc 0 1)) (hΘm : MonotoneOn Θ (Set.Icc 0 1))
    (hΘ : ∀ s ∈ Set.Icc (0 : ℝ) 1, dirVec (Θ s) = nuVec X h (x + s • (y - x))) :
    eVariationOn (exitPt X h) (Set.Icc (Θ 0) (Θ 1)) ≤
      ENNReal.ofReal (dist2 X / (dist2 X - h) * dist x y + 5 * h * (Θ 1 - Θ 0)) := by
  sorry

/-- **(P7) `|A| ≤ 7Δ₂`** (`|A| ≤ per K ≤ 2πΔ₂` without perimeter).

Why true: the exit map over one full turn has variation `≤ 2πΔ₂ + 10πh` (arc ranges: radius
`Δ₂`, total angle `≤ 2π`; corner ranges: `≤ 5h` per radian); consecutive A-points (cyclically, by
`nuAng`) are `≥ 1` apart.  `2πΔ₂ + 10πh ≤ 7Δ₂` since `h < Δ₂/200`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exitPt_A`, `nuAng_injOn_A`, the local estimates of `var_exit_piece`.
Difficulty L. -/
theorem card_A_le_seven {h : ℝ} (hC : CoreHyp X h) : ((Aset X).card : ℝ) ≤ 7 * dist2 X := by
  sorry

end

end Erdos132Main

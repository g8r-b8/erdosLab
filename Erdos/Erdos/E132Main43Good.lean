import Erdos.E132Main43Defs

/-!
# Erdős Problem 132, `4/3` theorem — good points: exceptions and the local frame

Paper: `angle_R6.md` §1.1–1.2.  Euclidean-local form (as for Theorem N1 in
`E132Main15N1`, see `MAIN15_PLAN.md` "Deviations"): no arc length, no graph function.

* **Exceptions** (`card_E43_le`): at most `cE43 = 10¹⁵` heavy points are not good.  A heavy
  point `y` is in `R ∖ D`, interior to `K`, and (not good) has two boundary points
  `b₁, b₂ ∈ B̄(y, Λ)` with unit normals `‖ν₁ − ν₂‖ > ε₀`.  Either the normals are nearly
  antipodal (`ν₁·ν₂ ≤ −(1 − 10⁻⁴)`: **thin**, Lemma T at scale `Λ`, `|X ∖ D| ≤ cThin43`), or
  every direction between them is the normal of a support point within `150Λ = 69600` of `y`
  (**big turning**, `turning(∂K ∩ B̄(y, 69600)) ≥ ε₀`, counted by `turning_sum_le`).
* **Frame** (`frame_of_good`): a good heavy point has a `Frame43`: nearest boundary point
  `p₀ = y + h n`, `h ∈ (0, 1]`, normals near `n` within distance `6`, and far points of `K` at
  abscissa `±463` (from goodness at radius `Λ`: the support point in a direction just outside
  the `ε₀`-cone is farther than `Λ`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- The boundary piece `∂K ∩ B̄(y, 150Λ)` whose turning is measured (`150·464 = 69600`). -/
def bdryNear43 (X : Finset Pt) (y : Pt) : Set Pt :=
  frontier (KBall X) ∩ Metric.closedBall y 69600

/-! ## Heavy points -/

/-- Heavy points are not diametral.

TODO: none — proved.
Acceptance: no `sorry` (inherits `degδ_le_three_of_D`).
Depends on: `vR_le_six_of_D`. Difficulty S. -/
theorem heavy_not_D (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) : y ∉ Dset X := fun hD => by
  have := vR_le_six_of_D hX hD
  have := (mem_filter.1 hy).2
  omega

/-- Heavy points are interior to `K`.

TODO: none — proved.
Acceptance: no `sorry` (inherits).
Depends on: `Rset_interior`, `heavy_not_D`. Difficulty S. -/
theorem heavy_interior (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) : y ∈ interior (KBall X) :=
  Rset_interior hX (mem_filter.1 hy).1 (heavy_not_D hX hy)

/-- Heavy points have depth `≤ 1` (they have an `S`-neighbour, `m_y ≥ 3`).

TODO: none — proved.
Acceptance: no `sorry` (inherits).
Depends on: `exists_near_normal`, `degδ_le_six`. Difficulty S. -/
theorem heavy_depth_le (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) : depth X y ≤ 1 := by
  have hm : 0 < mS X y := by
    have h9 := (mem_filter.1 hy).2
    unfold vR at h9
    have := degδ_le_six X y
    omega
  obtain ⟨b, hb, hd, -⟩ := exists_near_normal hX (heavy_interior hX hy) hm
  exact (Metric.infDist_le_dist_of_mem hb).trans hd

/-! ## The frame at a good point -/

/-- **Nearest boundary point.**  For `y` interior to `K`, `h = depth X y > 0` is attained at
`p₀ = y + h n` for a unit `n`, and `n` is an outer normal of `K` at `p₀`.

TODO: prove.
What's missing: `frontier K` is compact (closed subset of the compact `K`) and nonempty (`K` is
bounded, `≠ univ`), so `IsCompact.exists_infDist_eq_dist` gives `p₀` with `dist y p₀ = h`;
`h > 0` since `y ∉ frontier K` (interior) and the frontier is closed
(`Metric.infDist_pos_iff_not_mem_closure` or similar).  Put `n = h⁻¹ (p₀ − y)`.  Normal: the
open ball `B(y, h)` lies in `K` (a point of it outside `K` gives, by `exists_frontier_seg`, a
frontier point closer than `h`), so for a unit normal `ν` at `p₀` (`exists_unit_normal`)
`⟨y + h ν − p₀, ν⟩ ≤ 0` (limit of points of the ball), i.e. `⟨p₀ − y, ν⟩ ≥ h = ‖p₀ − y‖`,
and equality in Cauchy–Schwarz forces `ν = n`.
Acceptance: no `sorry`.
Depends on: `KBall_isCompact`, `KBall_convex`, `exists_unit_normal`, `exists_frontier_seg`.
Difficulty M. -/
theorem exists_foot (hX : Normal X) {y : Pt} (hy : y ∈ interior (KBall X)) :
    ∃ n : Pt, ‖n‖ = 1 ∧ 0 < depth X y ∧ y + depth X y • n ∈ frontier (KBall X) ∧
      n ∈ normalCone (KBall X) (y + depth X y • n) := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hKc := KBall_isCompact hne
  have hyK : y ∈ KBall X := interior_subset hy
  have hFc : IsCompact (frontier (KBall X)) :=
    hKc.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (KBall_isClosed X).closure_eq.subset)
  obtain ⟨x, hxK, hxmax⟩ := hKc.exists_isMaxOn ⟨y, hyK⟩
    (continuous_id.inner continuous_const :
      Continuous fun z : Pt => inner ℝ z (dirVec 0)).continuousOn
  have hxF : x ∈ frontier (KBall X) :=
    mem_frontier_of_max hxK (norm_dirVec 0) (fun z hz => hxmax hz)
  obtain ⟨p, hpF, hpd⟩ := hFc.exists_infDist_eq_dist ⟨x, hxF⟩ y
  have hdep : depth X y = dist y p := hpd
  have hyp : y ≠ p := by rintro rfl; exact hpF.2 hy
  have hpos : 0 < depth X y := by rw [hdep]; exact dist_pos.2 hyp
  set h := depth X y with hh
  set n : Pt := h⁻¹ • (p - y) with hndef
  have hpy : ‖p - y‖ = h := by rw [← dist_eq_norm, dist_comm, ← hdep]
  have hn : ‖n‖ = 1 := by
    rw [hndef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, hpy,
      inv_mul_cancel₀ hpos.ne']
  have hp : y + h • n = p := by
    rw [hndef, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  refine ⟨n, hn, hpos, ?_⟩
  rw [hp]
  refine ⟨hpF, ?_⟩
  -- the open ball `B(y, h)` lies in `K`
  have hball : ∀ z, dist z y < h → z ∈ KBall X := by
    intro z hz
    by_contra hzK
    have hzI : z ∉ interior (KBall X) := fun hi => hzK (interior_subset hi)
    obtain ⟨l, hl0, hl1, hb⟩ := exists_frontier_seg (KBall_isClosed X) hy hzI
    have h1 : h ≤ dist y (y + l • (z - y)) := by
      rw [hh]; exact Metric.infDist_le_dist_of_mem hb
    have h2 : dist y (y + l • (z - y)) = l * dist z y := by
      rw [dist_eq_norm, show y - (y + l • (z - y)) = -(l • (z - y)) by abel, norm_neg,
        norm_smul, Real.norm_eq_abs, abs_of_pos hl0, dist_eq_norm]
    have : l * dist z y ≤ dist z y := by nlinarith [dist_nonneg (x := z) (y := y)]
    linarith
  obtain ⟨ν, hν1, hν⟩ := exists_unit_normal (KBall_convex X) ⟨y, hy⟩ hpF
  have hge : h ≤ inner ℝ (p - y) ν := by
    by_contra hlt
    push Not at hlt
    have hcs : -h ≤ inner ℝ (p - y) ν := by
      have := neg_abs_le (inner ℝ (p - y) ν)
      have := abs_real_inner_le_norm (p - y) ν
      rw [hpy, hν1, mul_one] at this
      linarith
    set a := inner ℝ (p - y) ν with ha
    set t := (a / h + 1) / 2 with htdef
    have has : a = a / h * h := by field_simp
    have hs1 : a / h < 1 := by rw [div_lt_one hpos]; exact hlt
    have hsm : -1 ≤ a / h := by rw [le_div_iff₀ hpos]; linarith
    have hz : y + (t * h) • ν ∈ KBall X := hball _ (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hν1, mul_one, Real.norm_eq_abs,
        abs_lt]
      constructor <;> nlinarith)
    have := hν _ hz
    have e : y + (t * h) • ν - p = (t * h) • ν - (p - y) := by abel
    rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν1, ← ha] at this
    nlinarith
  have hnν : 1 ≤ inner ℝ n ν := by
    rw [hndef, real_inner_smul_left, le_inv_mul_iff₀ hpos, mul_one]; exact hge
  have hsq := norm_sub_sq_real n ν
  rw [hn, hν1] at hsq
  have h0 : ‖n - ν‖ = 0 := by
    have : ‖n - ν‖ ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
  rw [norm_eq_zero, sub_eq_zero] at h0
  rw [h0]; exact hν

/-- Goodness gives the frame's normal control (radius `6`) around a boundary point `b₀` within
distance `1` carrying the unit normal `n`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `IsGood43`. Difficulty S. -/
theorem good_normals {y b₀ n : Pt} (hg : IsGood43 X y) (hb₀ : b₀ ∈ frontier (KBall X))
    (hd₀ : dist y b₀ ≤ 1) (hn : n ∈ normalCone (KBall X) b₀) (hn1 : ‖n‖ = 1) :
    ∀ b ∈ frontier (KBall X), dist y b ≤ 6 → ∀ ν ∈ normalCone (KBall X) b, ‖ν‖ = 1 →
      ‖ν - n‖ ≤ ε₀43 := fun b hb hd ν hν hν1 =>
  hg b hb b₀ hb₀ (by unfold Lam43; linarith) (by unfold Lam43; linarith) ν hν n hn hν1 hn1

/-- **Far points** (input of Lemma DN): at a good `y ∈ K` with foot `p₀ = y + h n`
(`0 ≤ h ≤ 1`, `n` a unit normal at `p₀`), `K` contains points at abscissa `σ·463` and height
`≥ h − 9.31`, for `σ = ±1`.

TODO: prove.
What's missing (Euclidean replacement of the paper's graph points `g± = (±463, f(±463))`):
let `d = (n + σ κ perp n)/‖·‖` with `κ = 201/10000`, so `‖d − n‖ > 1/50`, and let `x` maximise
`⟨·, d⟩` on `K` (compact; `mem_frontier_of_max`), so `d ∈ normalCone K x`.  Goodness with
`b₁ = x`, `b₂ = p₀` (`dist y p₀ = h ≤ 1 ≤ Λ`, `n ∈ N(p₀)`) forces `dist y x > Λ = 464`.  With
`A = σ⟨x − y, perp n⟩`, `C = ⟨x − y, n⟩`: `⟨p₀ − x, d⟩ ≤ 0` gives `h − C ≤ κ A`; `C ≤ h`
(`Frame43.top`-style, from `n ∈ N(p₀)`) gives `A ≥ 0` and `|C| ≤ 1 + κ A`.  If `A ≤ 463` then
`A² + C² ≤ 463² + (1 + 463κ)² < 464²`, contradiction; so `A > 463`, and
`g = p₀ + (463/A)(x − p₀) ∈ K` (convexity) has abscissa `σ·463` and height
`h + (463/A)(C − h) ≥ h − 463κ ≥ h − 9.31`.
Acceptance: no `sorry`.
Depends on: `KBall_isCompact`, `KBall_convex`, `mem_frontier_of_max`, `IsGood43`,
`norm_perp`, `inner_pt`. Difficulty M–L. -/
theorem far_points (hX : Normal X) {y n : Pt} (hg : IsGood43 X y) (hyK : y ∈ KBall X)
    (hn : ‖n‖ = 1) (hh0 : 0 ≤ depth X y) (hh : depth X y ≤ 1)
    (hfoot : y + depth X y • n ∈ frontier (KBall X))
    (hnorm : n ∈ normalCone (KBall X) (y + depth X y • n)) :
    ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ g ∈ KBall X,
      inner ℝ (g - y) (perp n) = σ * 463 ∧ depth X y - 931 / 100 ≤ inner ℝ (g - y) n := by
  sorry

/-- **The frame at a good heavy point** (§1.2).

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `heavy_interior`, `exists_foot`, `heavy_depth_le`, `good_normals`, `far_points`. -/
theorem frame_of_good (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) (hg : IsGood43 X y) :
    ∃ n, Frame43 X y n := by
  have hint := heavy_interior hX hy
  obtain ⟨n, hn, hpos, hfoot, hnorm⟩ := exists_foot hX hint
  have hle := heavy_depth_le hX hy
  have hd : dist y (y + depth X y • n) ≤ 1 := by
    rw [dist_eq_norm, show y - (y + depth X y • n) = -(depth X y • n) by abel, norm_neg,
      norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
    exact hle
  exact ⟨n, ⟨hn, hint, hpos, hle, hfoot, hnorm, good_normals hg hfoot hd hnorm hn,
    far_points hX hg (interior_subset hint) hn hpos.le hle hfoot hnorm⟩⟩

/-! ## Exceptions: thin case -/

/-- **Box packing**: points pairwise `≥ 1` apart in a box `[c₀, c₀ + L] × [c₁, c₁ + W]` of the
orthonormal frame `(e, perp e)` number at most `(2L + 1)(2W + 1)`.

TODO: prove.
What's missing: grid pigeonhole with cells of side `1/2` (diameter `√2/2 < 1`), as in
`card_sep_box_le`/`card_sep_ball_le`: `x ↦ (⌊2(⟨x,e⟩ − c₀)⌋, ⌊2(⟨x,perp e⟩ − c₁)⌋)` is
injective into `[0, ⌊2L⌋] × [0, ⌊2W⌋]`; `‖x − x'‖² = ⟨x−x',e⟩² + ⟨x−x',perp e⟩²`
(`n1_norm_sq_frame`).
Acceptance: no `sorry`.
Depends on: `n1_norm_sq_frame`, `card_le_card_of_injOn`. Difficulty M. -/
theorem card_sep_box_le43 {P : Finset Pt} (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → 1 ≤ dist a b)
    {e : Pt} (he : ‖e‖ = 1) {c₀ c₁ L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hbox : ∀ x ∈ P, c₀ ≤ inner ℝ x e ∧ inner ℝ x e ≤ c₀ + L ∧
      c₁ ≤ inner ℝ x (perp e) ∧ inner ℝ x (perp e) ≤ c₁ + W) :
    (P.card : ℝ) ≤ (2 * L + 1) * (2 * W + 1) := by
  let f : Pt → ℕ × ℕ := fun a =>
    (⌊2 * (inner ℝ a e - c₀)⌋₊, ⌊2 * (inner ℝ a (perp e) - c₁)⌋₊)
  have hmaps : ∀ a ∈ P, f a ∈ (range (⌊2 * L⌋₊ + 1)) ×ˢ (range (⌊2 * W⌋₊ + 1)) := by
    intro a ha
    obtain ⟨h1, h2, h3, h4⟩ := hbox a ha
    simp only [f, mem_product, mem_range, Nat.lt_succ_iff]
    exact ⟨Nat.floor_mono (by linarith), Nat.floor_mono (by linarith)⟩
  have hclose : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → ⌊u⌋₊ = ⌊v⌋₊ → |u - v| < 1 := by
    intro u v hu hv huv
    have a1 := Nat.floor_le hu
    have a2 := Nat.lt_floor_add_one u
    have b1 := Nat.floor_le hv
    have b2 := Nat.lt_floor_add_one v
    rw [huv] at a1 a2
    rw [abs_lt]; constructor <;> linarith
  have := card_le_card_of_injOn f hmaps (fun a ha b hb hfe => by
    by_contra hab
    have h1 := hsep a ha b hb hab
    simp only [f, Prod.mk.injEq] at hfe
    obtain ⟨a1, -, a3, -⟩ := hbox a ha
    obtain ⟨b1, -, b3, -⟩ := hbox b hb
    have d0 := hclose _ _ (by linarith) (by linarith) hfe.1
    have d1 := hclose _ _ (by linarith) (by linarith) hfe.2
    have e0 : 2 * (inner ℝ a e - c₀) - 2 * (inner ℝ b e - c₀) = 2 * inner ℝ (a - b) e := by
      rw [inner_sub_left]; ring
    have e1 : 2 * (inner ℝ a (perp e) - c₁) - 2 * (inner ℝ b (perp e) - c₁) =
        2 * inner ℝ (a - b) (perp e) := by
      rw [inner_sub_left]; ring
    rw [e0, abs_mul, abs_two] at d0; rw [e1, abs_mul, abs_two] at d1
    have hn := n1_norm_sq_frame he (a - b)
    rw [← dist_eq_norm] at hn
    have := sq_abs (inner ℝ (a - b) e); have := sq_abs (inner ℝ (a - b) (perp e))
    have : dist a b ^ 2 < 1 := by
      rw [hn]
      nlinarith [abs_nonneg (inner ℝ (a - b) e), abs_nonneg (inner ℝ (a - b) (perp e))]
    nlinarith [dist_nonneg (x := a) (y := b)])
  rw [card_product, card_range, card_range] at this
  have hc : (P.card : ℝ) ≤ ((⌊2 * L⌋₊ : ℝ) + 1) * ((⌊2 * W⌋₊ : ℝ) + 1) := by
    exact_mod_cast this
  have fL := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * L)
  have fW := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * W)
  refine hc.trans (mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith))

/-- **Lemma T at scale `Λ`** (fatness step, §1.1 Lemma T* with `|b₁b₂| ≤ 2Λ`): if two boundary
points within `Λ = 464` of `y ∈ K` have nearly antipodal unit normals and `Δ₂ ≥ 10⁶`, then
`K` lies in a box of length `2·10⁵` and width `5000`.

TODO: prove.
What's missing: rerun the proof of `thin_box` with `1 ↦ Λ`.  Frame `e = −perp ν₁`
(`perp e = ν₁`), heights `H = ⟨·, ν₁⟩`, lengths `S = ⟨·, e⟩`, `L = max S − min S` on `K`.
`K ⊂ {H ≤ H(b₁)}`; `‖ν₁ + ν₂‖ ≤ √(2·10⁻⁴) < 1/70` and `⟨x − b₂, ν₂⟩ ≤ 0` give
`H(x) ≥ H(b₂) − |S(x) − S(b₂)|/69`; `H(b₁) − H(b₂) ≤ |b₁b₂| ≤ 2Λ`.  So the height range is
`W ≤ 928 + L/69`.  If `L ≥ 146400` then `W ≤ L/48`, and the middle-slice argument
(`n1_mid_interior`, `n1_slice_extreme`, `n1_circle_normal`, `n1_tilt`) gives circle centres
`w_top, w_bot ∈ X` with `|w_bot − w_top| ≥ 1.998Δ₂ − W`; since `L ≤ diam K ≤ 2Δ₂` and
`Δ₂ ≥ 10⁶`, `W ≤ 928 + 2Δ₂/69 < 0.058Δ₂`, so `|w_bot − w_top| > 1.94Δ₂ ≥ Δ`, contradiction.
Hence `L < 146400 ≤ 2·10⁵` and `W ≤ 928 + 146400/69 < 5000`.  (Why `Δ₂ ≥ 10⁶`: with only
`Δ₂ ≥ 10⁴` the width `W ≈ 4000` is not `≪ Δ₂`; the small-`Δ₂` case is handled by packing in
`thin_card_le43`.)
Acceptance: no `sorry`.
Depends on: `thin_box` (proof pattern), `n1_tilt`, `n1_slice_extreme`, `n1_circle_normal`,
`n1_mid_interior`, `frontier_on_circle`, `KBall_isCompact`. Difficulty L. -/
theorem thin_box43 (hX : Normal X) (hlarge : 10 ^ 6 ≤ dist2 X) {y b₁ b₂ ν₁ ν₂ : Pt}
    (hy : y ∈ KBall X) (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ Lam43) (h₂ : dist y b₂ ≤ Lam43)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ∃ e : Pt, ‖e‖ = 1 ∧ ∃ c₀ c₁ : ℝ, ∀ x ∈ KBall X,
      c₀ ≤ inner ℝ x e ∧ inner ℝ x e ≤ c₀ + 2 * 10 ^ 5 ∧
        c₁ ≤ inner ℝ x (perp e) ∧ inner ℝ x (perp e) ≤ c₁ + 5000 := by
  sorry

/-- Small `Δ₂`: `X ∖ D ⊂ K ⊂ B̄(w, Δ₂)` for any `w ∈ X`, so packing bounds `|X ∖ D|`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `ball_polygon_a`, `card_sep_ball_le`, `one_le_dist`. Difficulty S. -/
theorem card_notD_le_of_small (hX : Normal X) (hs : dist2 X < 10 ^ 6) :
    ((X \ Dset X).card : ℝ) ≤ (4 * 10 ^ 6 + 1) ^ 2 := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  obtain ⟨w, hw⟩ := hne
  have h := card_sep_ball_le (P := X \ Dset X)
    (fun a ha b hb hab => one_le_dist hX.minDist_eq (mem_sdiff.1 ha).1 (mem_sdiff.1 hb).1 hab)
    w (10 ^ 6) (fun a ha => by
      have hK := ball_polygon_a (mem_sdiff.1 ha).1 (mem_sdiff.1 ha).2
      have := Set.mem_iInter₂.1 hK w (by simpa using hw)
      rw [Metric.mem_closedBall] at this
      push_cast; linarith)
  exact_mod_cast h

/-- **Thin case count**: nearly antipodal normals at two boundary points within `Λ` of
`y ∈ K` give `|X ∖ D| ≤ cThin43 = 10¹⁴`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `card_notD_le_of_small`, `thin_box43`, `card_sep_box_le43`, `ball_polygon_a`. -/
theorem thin_card_le43 (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ Lam43) (h₂ : dist y b₂ ≤ Lam43)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ((X \ Dset X).card : ℝ) ≤ cThin43 := by
  by_cases hs : dist2 X < 10 ^ 6
  · have := card_notD_le_of_small hX hs
    norm_num [cThin43] at this ⊢
    linarith
  · push Not at hs
    obtain ⟨e, he, c₀, c₁, hbox⟩ :=
      thin_box43 hX hs hy hb₁ hb₂ h₁ h₂ hν₁ hν₂ hn₁ hn₂ hthin
    have hsep : ∀ a ∈ X \ Dset X, ∀ b ∈ X \ Dset X, a ≠ b → 1 ≤ dist a b :=
      fun a ha b hb hab =>
        one_le_dist hX.minDist_eq (mem_sdiff.1 ha).1 (mem_sdiff.1 hb).1 hab
    have := card_sep_box_le43 hsep he (by norm_num : (0 : ℝ) ≤ 2 * 10 ^ 5)
      (by norm_num : (0 : ℝ) ≤ 5000) (c₀ := c₀) (c₁ := c₁)
      (fun x hx => hbox x (ball_polygon_a (mem_sdiff.1 hx).1 (mem_sdiff.1 hx).2))
    norm_num [cThin43] at this ⊢
    linarith

/-! ## Exceptions: big turning -/

/-- **Non-good, non-thin ⇒ big turning** (Lemma BT at scale `Λ`): if two boundary points within
`Λ` of `y ∈ K` carry unit normals with `‖ν₁ − ν₂‖ > ε₀` and `ν₁·ν₂ > −(1 − 10⁻⁴)`, then
`turning(K, ∂K ∩ B̄(y, 69600)) ≥ ε₀`.

TODO: prove.
What's missing: copy `turning_ge_of_nonflat` / `n1_support_near` with `1 ↦ Λ`:
`|ν₁·ν₂| ≤ 1 − 10⁻⁴` (upper side: `‖ν₁ − ν₂‖² > 1/2500` gives `ν₁·ν₂ < 1 − 1/5000`); a support
point `x` in a direction `d = aν₁ + bν₂` (`a, b ≥ 0`) has `|⟨x − y, ν_i⟩| ≤ Λ`, hence
`‖x − y‖ ≤ 150Λ = 69600` (`norm_le_of_inner_bounds` applied to `(x − y)/Λ`); the short arc
between `ν₁, ν₂` has length `∠(ν₁,ν₂) ≥ ‖ν₁ − ν₂‖ > ε₀` (`norm_sub_le_ang`);
`le_turning_of_Icc`.
Acceptance: no `sorry`.
Depends on: `norm_le_of_inner_bounds`, `n1_dirVec_arc`, `le_turning_of_Icc`,
`mem_frontier_of_max`, `exists_dirVec_pair`, `norm_sub_le_ang`, `KBall_isCompact`.
Difficulty M. -/
theorem turning_ge43 (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ Lam43) (h₂ : dist y b₂ ≤ Lam43)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hfar : ε₀43 < ‖ν₁ - ν₂‖)
    (hnt : -(1 - 1 / 10 ^ 4) < inner ℝ ν₁ ν₂) :
    ε₀43 ≤ turning (KBall X) (bdryNear43 X y) := by
  sorry

/-- **Lemma BT count at scale `Λ`**: at most `100π·278401²` points `y ∈ X` have
`turning(K, ∂K ∩ B̄(y, 69600)) ≥ ε₀` (`278401 = 4·69600 + 1`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `turning_sum_le`, `card_sep_ball_le`, `KBall_convex`, `KBall_isCompact`,
`one_le_dist`. Difficulty S. -/
theorem card_bigTurning_le43 (hX : Normal X) (Y : Finset Pt) (hY : Y ⊆ X)
    (hbig : ∀ y ∈ Y, ε₀43 ≤ turning (KBall X) (bdryNear43 X y)) :
    (Y.card : ℝ) ≤ 100 * π * 278401 ^ 2 := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hsep : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → 1 ≤ dist a b := fun a ha b hb hab =>
    one_le_dist hX.minDist_eq (hY ha) (hY hb) hab
  have hsum := turning_sum_le (KBall_convex X) (KBall_isCompact hne) Y
    (fun y => bdryNear43 X y) (fun y _ => Set.inter_subset_left)
    (fun y _ => isClosed_frontier.inter Metric.isClosed_closedBall) (278401 ^ 2)
    (fun b => by
      have := card_sep_ball_le (P := Y.filter (fun y => b ∈ bdryNear43 X y))
        (fun a ha c hc hac => hsep a (mem_filter.1 ha).1 c (mem_filter.1 hc).1 hac) b 69600
        (fun a ha => by
          have h := (mem_filter.1 ha).2.2
          rw [Metric.mem_closedBall, dist_comm] at h
          push_cast; exact h)
      simpa using this)
  have hle : ∑ y ∈ Y, ε₀43 ≤ ∑ y ∈ Y, turning (KBall X) (bdryNear43 X y) :=
    sum_le_sum hbig
  rw [sum_const, nsmul_eq_mul] at hle
  push_cast at hsum
  unfold ε₀43 at hle
  linarith

/-- `100π·278401² + cThin43 ≤ cE43`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem cE43_check : 100 * π * 278401 ^ 2 + cThin43 ≤ cE43 := by
  have := Real.pi_lt_d2
  norm_num [cThin43, cE43]
  nlinarith

/-- **Exceptions** (§1.1): at most `cE43` heavy points are not good.

TODO: none — proved from the statements (wiring, as `N1`).
Acceptance: no `sorry` (inherits).
Depends on: `heavy_not_D`, `heavy_interior`, `thin_card_le43`, `turning_ge43`,
`card_bigTurning_le43`, `cE43_check`. -/
theorem card_E43_le (hX : Normal X) : ((E43 X).card : ℝ) ≤ cE43 := by
  set E := E43 X with hE
  have hRX : Rset X ⊆ X := sdiff_subset
  have hEX : ∀ z ∈ E, z ∈ X := fun z hz => hRX (mem_filter.1 (mem_filter.1 hz).1).1
  have key : ∀ y ∈ E, y ∉ Dset X ∧ y ∈ interior (KBall X) ∧
      ∃ b₁ ∈ frontier (KBall X), ∃ b₂ ∈ frontier (KBall X), dist y b₁ ≤ Lam43 ∧
        dist y b₂ ≤ Lam43 ∧ ∃ ν₁ ∈ normalCone (KBall X) b₁, ∃ ν₂ ∈ normalCone (KBall X) b₂,
          ‖ν₁‖ = 1 ∧ ‖ν₂‖ = 1 ∧ ε₀43 < ‖ν₁ - ν₂‖ := by
    intro y hy
    obtain ⟨hyh, hg⟩ := mem_filter.1 hy
    refine ⟨heavy_not_D hX hyh, heavy_interior hX hyh, ?_⟩
    unfold IsGood43 at hg
    push Not at hg
    exact hg
  have hc := cE43_check
  have hπ := Real.pi_pos
  by_cases hthin : ∃ y ∈ E, ∃ b₁ ∈ frontier (KBall X), ∃ b₂ ∈ frontier (KBall X),
      dist y b₁ ≤ Lam43 ∧ dist y b₂ ≤ Lam43 ∧ ∃ ν₁ ∈ normalCone (KBall X) b₁,
        ∃ ν₂ ∈ normalCone (KBall X) b₂, ‖ν₁‖ = 1 ∧ ‖ν₂‖ = 1 ∧
          inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)
  · obtain ⟨y, hy, b₁, hb₁, b₂, hb₂, hd₁, hd₂, ν₁, hν₁, ν₂, hν₂, hn₁, hn₂, hin⟩ := hthin
    have hyK := interior_subset (key y hy).2.1
    have h := thin_card_le43 hX hyK hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hin
    have hsub : E ⊆ X \ Dset X := fun z hz => mem_sdiff.2 ⟨hEX z hz, (key z hz).1⟩
    have : (E.card : ℝ) ≤ (X \ Dset X).card := by exact_mod_cast card_le_card hsub
    have : (0 : ℝ) ≤ 100 * π * 278401 ^ 2 := by positivity
    linarith
  · push Not at hthin
    have hbig : ∀ y ∈ E, ε₀43 ≤ turning (KBall X) (bdryNear43 X y) := by
      intro y hy
      obtain ⟨-, hint, b₁, hb₁, b₂, hb₂, hd₁, hd₂, ν₁, hν₁, ν₂, hν₂, hn₁, hn₂, hfar⟩ := key y hy
      have hnt := hthin y hy b₁ hb₁ b₂ hb₂ hd₁ hd₂ ν₁ hν₁ ν₂ hν₂ hn₁ hn₂
      exact turning_ge43 hX (interior_subset hint) hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hfar hnt
    have := card_bigTurning_le43 hX E (fun z hz => hEX z hz) hbig
    have : (0 : ℝ) ≤ cThin43 := by norm_num [cThin43]
    linarith

end

end Erdos132Main

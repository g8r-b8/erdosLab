import Erdos.E132Main2116Defs

/-!
# Erdős Problem 132, `21/16` — good′ points at scale `Λ = 10⁹`: exceptions and frames

Paper §10 "Parameters, good points and the flat model": lem:fewbad2 and lem:frame with
`ε₀ = 10⁻⁶`, `Λ = 10⁹`.  Euclidean-local form as in `E132Main43Good` (see `MAIN43_PLAN.md`
"Deviations" 1–3): no arc length, no graph function.

* **Exceptions** (`card_EP_le`): at most `cEP = 10³²` points of `R` of weight `≥ 8` are not
  good′.  Such a point is in `R ∖ D`, interior to `K`, and has two boundary points within `Λ`
  with unit normals `‖ν₁ − ν₂‖ > ε₀`: either **thin** (`ν₁·ν₂ ≤ −(1 − 10⁻⁴)`, then
  `|X ∖ D| ≤ cThinP`; this needs `Δ₂ ≥ 2·10¹⁵`), or **big turning** of `∂K ∩ B̄(y, 150Λ)`.
* **Frame** (`frameP_of_good`): a good′ point of weight `≥ 8` has a `FrameP`.

All wiring here is proved; the sorries are the copies of the `4/3` geometric lemmas at the new
scale: `far_pointsP`, `thin_boxP`, `turning_geP`, `card_bigTurning_leP`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- The boundary piece `∂K ∩ B̄(y, 150Λ)` whose turning is measured. -/
def bdryNearP (X : Finset Pt) (y : Pt) : Set Pt :=
  frontier (KBall X) ∩ Metric.closedBall y (150 * 10 ^ 9)

/-! ## Points of weight `≥ 8` -/

/-- Points of weight `≥ 8` are not diametral (`v ≤ 6` on `D`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `vR_le_six_of_D`. Difficulty S. -/
theorem heavyP_not_D (hX : Normal X) {y : Pt} (h8 : 8 ≤ vR X y) : y ∉ Dset X := fun hD => by
  have := vR_le_six_of_D hX hD
  omega

/-- Points of `R` of weight `≥ 8` are interior to `K`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `Rset_interior`, `heavyP_not_D`. Difficulty S. -/
theorem heavyP_interior (hX : Normal X) {y : Pt} (hy : y ∈ Rset X) (h8 : 8 ≤ vR X y) :
    y ∈ interior (KBall X) :=
  Rset_interior hX hy (heavyP_not_D hX h8)

/-- Points of `R` of weight `≥ 8` have depth `≤ 1` (`m_y ≥ 2 > 0`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `exists_near_normal`, `degδ_le_six`. Difficulty S. -/
theorem heavyP_depth_le (hX : Normal X) {y : Pt} (hy : y ∈ Rset X) (h8 : 8 ≤ vR X y) :
    depth X y ≤ 1 := by
  have hm : 0 < mS X y := by
    unfold vR at h8
    have := degδ_le_six X y
    omega
  obtain ⟨b, hb, hd, -⟩ := exists_near_normal hX (heavyP_interior hX hy h8) hm
  exact (Metric.infDist_le_dist_of_mem hb).trans hd

/-! ## The frame at a good′ point -/

/-- **Far points at scale `Λ`** (input of Lemma DN): at a good′ `y ∈ K` with foot
`p₀ = y + h n` (`0 ≤ h ≤ 1`), `K` contains points at abscissa `σ(Λ − 1)` and height
`≥ h − 1011`.

TODO: prove.
What's missing: copy `far_points` (`E132Main43Good`) with `Λ = 10⁹`, `ε₀ = 10⁻⁶`:
`d = (n + σκ perp n)/‖·‖` with `κ = 101/10⁸` (so `‖d − n‖ > 10⁻⁶`), `x` a maximiser of `⟨·, d⟩`
on `K` (`mem_frontier_of_max`); goodness with `b₁ = x`, `b₂ = p₀` forces `dist y x > Λ`; with
`A = σ⟨x − y, perp n⟩`, `C = ⟨x − y, n⟩`: `h − C ≤ κA`, `C ≤ h`, so `|C| ≤ 1 + κA`; if
`A ≤ Λ − 1` then `A² + C² ≤ (Λ − 1)² + (1 + 1010.1)² < Λ²`, contradiction; so `A > Λ − 1` and
`g = p₀ + ((Λ − 1)/A)(x − p₀) ∈ K` has height `≥ h − (Λ − 1)κ ≥ h − 1011`.
Acceptance: no `sorry`.
Depends on: `KBall_isCompact`, `KBall_convex`, `mem_frontier_of_max`, `IsGoodP`, `norm_perp`,
`inner_pt`. Difficulty M–L (copy). -/
theorem far_pointsP (hX : Normal X) {y n : Pt} (hg : IsGoodP X y) (hyK : y ∈ KBall X)
    (hn : ‖n‖ = 1) (hh0 : 0 ≤ depth X y) (hh : depth X y ≤ 1)
    (hfoot : y + depth X y • n ∈ frontier (KBall X))
    (hnorm : n ∈ normalCone (KBall X) (y + depth X y • n)) :
    ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ g ∈ KBall X,
      inner ℝ (g - y) (perp n) = σ * (LamP - 1) ∧ depth X y - 1011 ≤ inner ℝ (g - y) n := by
  sorry

/-- **Frame at a good′ point** (paper lem:frame, (G1)–(G5) in Euclidean form).

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits `far_pointsP`).
Depends on: `heavyP_interior`, `heavyP_depth_le`, `exists_foot`, `far_pointsP`. -/
theorem frameP_of_good (hX : Normal X) {y : Pt} (hy : y ∈ Rset X) (h8 : 8 ≤ vR X y)
    (hg : IsGoodP X y) : ∃ n, FrameP X y n := by
  have hint := heavyP_interior hX hy h8
  obtain ⟨n, hn, hpos, hfoot, hnorm⟩ := exists_foot hX hint
  have hle := heavyP_depth_le hX hy h8
  have hd : dist y (y + depth X y • n) ≤ 1 := by
    rw [dist_eq_norm, show y - (y + depth X y • n) = -(depth X y • n) by abel, norm_neg,
      norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
    exact hle
  refine ⟨n, ⟨hn, hint, hpos, hle, hfoot, hnorm, ?_,
    far_pointsP hX hg (interior_subset hint) hn hpos.le hle hfoot hnorm⟩⟩
  intro b hb hdb ν hν hν1
  refine hg b hb _ hfoot ?_ ?_ ν hν n hnorm hν1 hn
  · unfold LamP; linarith
  · unfold LamP; linarith

/-! ## Exceptions -/

/-- **Thin box at scale `Λ`** (lem:thinK / lem:Tstar at scale `Λ`): nearly antipodal unit
normals at two boundary points within `Λ` of `y ∈ K`, with `Δ₂ ≥ 2·10¹⁵`, put `K` in a box
`4·10¹¹ × 10¹⁰`.

TODO: prove.
What's missing: rerun `thin_box43` (`E132Main43Good`) with `Λ = 10⁹`: the two support lines
make a wedge of opening `≤ 0.83°` (`‖ν₁ + ν₂‖ ≤ 0.01415`), the cross-section at `y` is
`≤ 2Λ/cos`, so the width is `W ≤ 2.1·10⁹ + L/69`; if the length `L ≥ 3.3·10¹¹` then `W ≤ L/48`
and the fatness step (`n1_tilt`: normals at the top/bottom of the middle section are within
`0.999` of vertical, their `Δ₂`-partners are `≥ 1.99Δ₂ − W > 1.94Δ₂ ≥ Δ` apart; here
`W ≤ 2.1·10⁹ + 2Δ₂/69 < 0.058Δ₂` because `Δ₂ ≥ 2·10¹⁵`) is a contradiction; so
`L < 3.3·10¹¹ ≤ 4·10¹¹` and `W ≤ 7·10⁹ ≤ 10¹⁰`.
Acceptance: no `sorry`.
Depends on: proof of `thin_box43`, `n1_tilt`, `n1_slice_extreme`, `n1_circle_normal`.
Difficulty L (rerun of an existing proof with new constants). -/
theorem thin_boxP (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y b₁ b₂ ν₁ ν₂ : Pt}
    (hy : y ∈ KBall X) (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ LamP) (h₂ : dist y b₂ ≤ LamP)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ∃ e : Pt, ‖e‖ = 1 ∧ ∃ c₀ c₁ : ℝ, ∀ x ∈ KBall X,
      c₀ ≤ inner ℝ x e ∧ inner ℝ x e ≤ c₀ + 4 * 10 ^ 11 ∧
        c₁ ≤ inner ℝ x (perp e) ∧ inner ℝ x (perp e) ≤ c₁ + 10 ^ 10 := by
  sorry

/-- **Thin case count at scale `Λ`**: `|X ∖ D| ≤ cThinP = 10²³`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits `thin_boxP`).
Depends on: `thin_boxP`, `card_sep_box_le43`, `ball_polygon_a`, `one_le_dist`. -/
theorem thin_card_leP (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y b₁ b₂ ν₁ ν₂ : Pt}
    (hy : y ∈ KBall X) (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ LamP) (h₂ : dist y b₂ ≤ LamP)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ((X \ Dset X).card : ℝ) ≤ cThinP := by
  obtain ⟨e, he, c₀, c₁, hbox⟩ :=
    thin_boxP hX hL hy hb₁ hb₂ h₁ h₂ hν₁ hν₂ hn₁ hn₂ hthin
  have h := card_sep_box_le43 (P := X \ Dset X)
    (fun a ha b hb hab => one_le_dist hX.minDist_eq (mem_sdiff.1 ha).1 (mem_sdiff.1 hb).1 hab)
    he (L := 4 * 10 ^ 11) (W := 10 ^ 10) (by norm_num) (by norm_num)
    (fun x hx => hbox x (ball_polygon_a (mem_sdiff.1 hx).1 (mem_sdiff.1 hx).2))
  unfold cThinP
  linarith [show (2 * (4 * 10 ^ 11 : ℝ) + 1) * (2 * 10 ^ 10 + 1) ≤ 10 ^ 23 by norm_num]

/-- **Non-good, non-thin ⇒ big turning at scale `Λ`**: two unit normals at boundary points
within `Λ` of `y ∈ K` with `‖ν₁ − ν₂‖ > ε₀` and `ν₁·ν₂ > −(1 − 10⁻⁴)` give
`turning(K, ∂K ∩ B̄(y, 150Λ)) ≥ ε₀`.

TODO: prove.
What's missing: copy `turning_ge43` with `464 ↦ 10⁹`, `1/50 ↦ 10⁻⁶`: every direction on the
short arc between `ν₁, ν₂` is the normal of a support point `x` with `|⟨x − y, ν_i⟩| ≤ Λ`,
hence `‖x − y‖ ≤ 150Λ` (`norm_le_of_inner_bounds` on `(x − y)/Λ`); the arc has length
`≥ ‖ν₁ − ν₂‖ > ε₀`; `le_turning_of_Icc`.
Acceptance: no `sorry`.
Depends on: `norm_le_of_inner_bounds`, `n1_dirVec_arc`, `le_turning_of_Icc`,
`mem_frontier_of_max`, `exists_dirVec_pair`, `norm_sub_le_ang`. Difficulty M (copy). -/
theorem turning_geP (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ LamP) (h₂ : dist y b₂ ≤ LamP)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hfar : ε₀P < ‖ν₁ - ν₂‖)
    (hnt : -(1 - 1 / 10 ^ 4) < inner ℝ ν₁ ν₂) :
    ε₀P ≤ turning (KBall X) (bdryNearP X y) := by
  sorry

/-- **Big-turning count at scale `Λ`**: at most `2π·10⁶·(6·10¹¹ + 1)²` points `y ∈ X` have
`turning(K, ∂K ∩ B̄(y, 150Λ)) ≥ ε₀` (`6·10¹¹ + 1 = 4·150Λ + 1`).

TODO: prove.
What's missing: copy `card_bigTurning_le43`: `turning_sum_le` with multiplicity
`(4·150Λ + 1)²` (`card_sep_ball_le`) gives `|Y|·ε₀ ≤ 2π·(6·10¹¹ + 1)²`.
Acceptance: no `sorry`.
Depends on: `turning_sum_le`, `card_sep_ball_le`, `KBall_convex`, `KBall_isCompact`,
`one_le_dist`. Difficulty S–M (copy). -/
theorem card_bigTurning_leP (hX : Normal X) (Y : Finset Pt) (hY : Y ⊆ X)
    (hbig : ∀ y ∈ Y, ε₀P ≤ turning (KBall X) (bdryNearP X y)) :
    (Y.card : ℝ) ≤ 2 * π * 10 ^ 6 * (6 * 10 ^ 11 + 1) ^ 2 := by
  sorry

/-- `2π·10⁶·(6·10¹¹ + 1)² + cThinP ≤ cEP`.

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem cEP_check : 2 * π * 10 ^ 6 * (6 * 10 ^ 11 + 1) ^ 2 + cThinP ≤ cEP := by
  have := Real.pi_lt_d2
  unfold cThinP cEP
  nlinarith

/-- **lem:fewbad2** (Euclidean form): at most `cEP` points of `R` of weight `≥ 8` are not good′.

TODO: none — proved from the statements (wiring, as `card_E43_le`).
Acceptance: no `sorry` (inherits).
Depends on: `heavyP_not_D`, `heavyP_interior`, `thin_card_leP`, `turning_geP`,
`card_bigTurning_leP`, `cEP_check`. -/
theorem card_EP_le (hX : Normal X) (hL : bigD2 ≤ dist2 X) : ((EP X).card : ℝ) ≤ cEP := by
  set E := EP X with hE
  have hRX : Rset X ⊆ X := sdiff_subset
  have hEX : ∀ z ∈ E, z ∈ X := fun z hz => hRX (mem_filter.1 hz).1
  have key : ∀ y ∈ E, y ∉ Dset X ∧ y ∈ interior (KBall X) ∧
      ∃ b₁ ∈ frontier (KBall X), ∃ b₂ ∈ frontier (KBall X), dist y b₁ ≤ LamP ∧
        dist y b₂ ≤ LamP ∧ ∃ ν₁ ∈ normalCone (KBall X) b₁, ∃ ν₂ ∈ normalCone (KBall X) b₂,
          ‖ν₁‖ = 1 ∧ ‖ν₂‖ = 1 ∧ ε₀P < ‖ν₁ - ν₂‖ := by
    intro y hy
    obtain ⟨hyR, h8, hg⟩ := mem_filter.1 hy
    refine ⟨heavyP_not_D hX h8, heavyP_interior hX hyR h8, ?_⟩
    unfold IsGoodP at hg
    push Not at hg
    exact hg
  have hc := cEP_check
  have hπ := Real.pi_pos
  by_cases hthin : ∃ y ∈ E, ∃ b₁ ∈ frontier (KBall X), ∃ b₂ ∈ frontier (KBall X),
      dist y b₁ ≤ LamP ∧ dist y b₂ ≤ LamP ∧ ∃ ν₁ ∈ normalCone (KBall X) b₁,
        ∃ ν₂ ∈ normalCone (KBall X) b₂, ‖ν₁‖ = 1 ∧ ‖ν₂‖ = 1 ∧
          inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)
  · obtain ⟨y, hy, b₁, hb₁, b₂, hb₂, hd₁, hd₂, ν₁, hν₁, ν₂, hν₂, hn₁, hn₂, hin⟩ := hthin
    have hyK := interior_subset (key y hy).2.1
    have h := thin_card_leP hX hL hyK hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hin
    have hsub : E ⊆ X \ Dset X := fun z hz => mem_sdiff.2 ⟨hEX z hz, (key z hz).1⟩
    have : (E.card : ℝ) ≤ (X \ Dset X).card := by exact_mod_cast card_le_card hsub
    have : (0 : ℝ) ≤ 2 * π * 10 ^ 6 * (6 * 10 ^ 11 + 1) ^ 2 := by positivity
    linarith
  · push Not at hthin
    have hbig : ∀ y ∈ E, ε₀P ≤ turning (KBall X) (bdryNearP X y) := by
      intro y hy
      obtain ⟨-, hint, b₁, hb₁, b₂, hb₂, hd₁, hd₂, ν₁, hν₁, ν₂, hν₂, hn₁, hn₂, hfar⟩ := key y hy
      have hnt := hthin y hy b₁ hb₁ b₂ hb₂ hd₁ hd₂ ν₁ hν₁ ν₂ hν₂ hn₁ hn₂
      exact turning_geP hX (interior_subset hint) hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hfar hnt
    have := card_bigTurning_leP hX E (fun z hz => hEX z hz) hbig
    have : (0 : ℝ) ≤ cThinP := by norm_num [cThinP]
    linarith

end

end Erdos132Main

import Erdos.E132Main15N1

/-!
# Erdős Problem 132, `4/3` theorem — definitions, the charging lemma, the LP

Improves `erdos132_main15` (`15/11`) to `min{μ(Δ₂), μ(δ)} ≤ (4/3)n + C`
(`problems/132/angle_R6.md` §1: Theorem N3 and Corollary `L ≤ 4/3`).  Everything of the
`54/37` and `15/11` developments is reused unchanged.  This file adds

* `vR X y = deg y + m_y` (the R-weight), `nbδ` (the `δ`-neighbours), `depth` (distance to
  `∂K`), the **receivers** `Low X y` (neighbours at least `2/3` deeper than `y`), `heavy`
  (`v ≥ 9`), the Euclidean-local **goodness** `IsGood43` and the exceptional set `E43`;
* the **local frame** `Frame43 X y n` at a good heavy point (unit normal `n` at a nearest
  boundary point, all nearby normals within `ε₀ = 1/50` of `n`, two far points of `K` at
  horizontal offsets `±463`), and the two heavy types `IsFan43`, `IsCap43` consumed by the
  charging argument (`E132Main43Charge`) and produced by the classification
  (`E132Main43Classify`);
* the purely combinatorial **charging lemma** `charge_sum` (proved);
* the LP with weights `2/3, 1/3` (`lp43`) and the constants (`consts43`).

Plan, deviations and DAG: `problems/132/lean/MAIN43_PLAN.md`.

Coordinates in a frame `(y, n)`: for a point `q`, *height* `Z q = ⟨q − y, n⟩` and *abscissa*
`X q = ⟨q − y, perp n⟩`; a unit neighbour at angle `ψ` from `n` is `y + dirF n ψ`
(`dirF n ψ = sin ψ · perp n + cos ψ · n`), so `Z = cos ψ` is the paper's `c(q)` and the paper's
`h` is `depth X y`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Definitions -/

/-- The **R-weight** `v(y) = deg_δ y + m_y` (summand of the exact identity). -/
def vR (X : Finset Pt) (y : Pt) : ℕ := degδ X y + mS X y

/-- The `δ`-neighbours of `y` (so `degδ X y = (nbδ X y).card` by definition). -/
def nbδ (X : Finset Pt) (y : Pt) : Finset Pt := partners X (minDist X) y

/-- **Depth** of `y`: the distance from `y` to `∂K` (the paper's `h` for `y ∈ K`). -/
def depth (X : Finset Pt) (y : Pt) : ℝ := Metric.infDist y (frontier (KBall X))

/-- **Receivers** of `y` (§1.4): `δ`-neighbours `a ∈ K` at least `2/3` deeper than `y`.
Intrinsic (no frame).  For a good heavy `y` these are exactly the "lower points" of the paper
(fan: `a±` at `≈ ±150°`, F5's `a`; cap: `b` at `≈ 180°`), whose height is `≤ −0.8`; the cap's
points at `±120°` (height `≈ −1/2`) are *not* receivers.  (Threshold `2/3`, not the `3/4`
suggested in the brief: F5's lower point is only known to have height `≤ −0.85`, and the
depth estimate loses `3ε ≈ 0.061`.) -/
def Low (X : Finset Pt) (y : Pt) : Finset Pt :=
  (nbδ X y).filter (fun a => a ∈ KBall X ∧ depth X y + 2 / 3 ≤ depth X a)

/-- **Heavy** points: `y ∈ R` with `v(y) ≥ 9`. -/
def heavy (X : Finset Pt) : Finset Pt := (Rset X).filter (fun y => 9 ≤ vR X y)

/-- `Λ = 464` (paper §1.0). -/
def Lam43 : ℝ := 464

/-- `ε₀ = 1/50` (paper §1.0), used as a bound on `‖ν − ν'‖` for unit normals. -/
def ε₀43 : ℝ := 1 / 50

/-- The slope bound `ε = 1/49 ≥ (1/50)/(1 − 1/5000)` (paper: `ε = tan ε₀ < 0.02001`). -/
def ε43 : ℝ := 1 / 49

/-- **Good** (Euclidean-local replacement of the paper's §1.1 (i)–(iii)): all unit outer normals
of `K` at boundary points within distance `Λ = 464` of `y` lie pairwise within `ε₀ = 1/50`. -/
def IsGood43 (X : Finset Pt) (y : Pt) : Prop :=
  ∀ b₁ ∈ frontier (KBall X), ∀ b₂ ∈ frontier (KBall X), dist y b₁ ≤ Lam43 → dist y b₂ ≤ Lam43 →
    ∀ ν₁ ∈ normalCone (KBall X) b₁, ∀ ν₂ ∈ normalCone (KBall X) b₂, ‖ν₁‖ = 1 → ‖ν₂‖ = 1 →
      ‖ν₁ - ν₂‖ ≤ ε₀43

/-- The **exceptional** heavy points (not good).  `card_E43_le`: at most `cE43` of them. -/
def E43 (X : Finset Pt) : Finset Pt := (heavy X).filter (fun y => ¬ IsGood43 X y)

/-- Unit vector at angle `ψ` from `n` (towards `perp n` for `ψ > 0`). -/
def dirF (n : Pt) (ψ : ℝ) : Pt := Real.sin ψ • perp n + Real.cos ψ • n

/-- `q` lies within `η` of the slot `y + dirF n ψ`. -/
def Slot (y n : Pt) (ψ η : ℝ) (q : Pt) : Prop := ‖q - y - dirF n ψ‖ ≤ η

/-- **Local frame** at `y` (paper §1.2, Euclidean form): `n` is the unit outer normal at a
nearest boundary point `p₀ = y + h n` (`h = depth X y ∈ (0, 1]`), all unit normals at boundary
points within distance `6` of `y` are within `ε₀` of `n`, and `K` contains two far points at
abscissa `±463` and height `≥ h − 9.31` (used for Lemma DN).  Produced by `frame_of_good`
(`E132Main43Good`); all frame facts (F′0–F′4, DN) are derived from these fields in
`E132Main43Frame`. -/
structure Frame43 (X : Finset Pt) (y n : Pt) : Prop where
  unit : ‖n‖ = 1
  mem_int : y ∈ interior (KBall X)
  depth_pos : 0 < depth X y
  depth_le : depth X y ≤ 1
  foot_mem : y + depth X y • n ∈ frontier (KBall X)
  foot_normal : n ∈ normalCone (KBall X) (y + depth X y • n)
  normals : ∀ b ∈ frontier (KBall X), dist y b ≤ 6 → ∀ ν ∈ normalCone (KBall X) b, ‖ν‖ = 1 →
    ‖ν - n‖ ≤ ε₀43
  far : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ g ∈ KBall X,
    inner ℝ (g - y) (perp n) = σ * 463 ∧ depth X y - 931 / 100 ≤ inner ℝ (g - y) n

/-- The **fan slots** (F6, F5, HF1, HF2 of §1.3): a K-row neighbour `p ∈ S ∖ D` in the slot
`−σ·90°`, a neighbour `q` in the slot `σ·90°`, a D-neighbour `z₁` in the slot `σ·30°`; and
either `q ∈ S` (F6, F5, HF1), or (HF2) a second D-neighbour `z₂` in the slot `−σ·30°` with
`|z₁ z₂| = δ` (consecutive vertices of the exact hexagon).  Slots within `1/20`. -/
def FanSlots (X : Finset Pt) (y n : Pt) : Prop :=
  ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ p ∈ nbδ X y, ∃ q ∈ nbδ X y, ∃ z₁ ∈ nbδ X y,
    p ∈ Sset X ∧ p ∉ Dset X ∧ z₁ ∈ Dset X ∧
    Slot y n (-(σ * (π / 2))) (1 / 20) p ∧ Slot y n (σ * (π / 2)) (1 / 20) q ∧
    Slot y n (σ * (π / 6)) (1 / 20) z₁ ∧
    (q ∈ Sset X ∨ ∃ z₂ ∈ nbδ X y, z₂ ∈ Dset X ∧ Slot y n (-(σ * (π / 6))) (1 / 20) z₂ ∧
      dist z₁ z₂ = minDist X)

/-- **Fan type** (output of the classification + Lemma Pin): `t ≥ 0.7`, every receiver lies
within `≈ 37°` of straight below `y` (`⟨y − a, n⟩ ≥ 4/5`), and the fan slots. -/
def IsFan43 (X : Finset Pt) (y n : Pt) : Prop :=
  7 / 10 ≤ tgap X ∧ (∀ a ∈ Low X y, 4 / 5 ≤ inner ℝ (y - a) n) ∧ FanSlots X y n

/-- **Cap type**: `t ≤ 0.6` and every receiver lies within `1/20` of `y − n` (straight below). -/
def IsCap43 (X : Finset Pt) (y n : Pt) : Prop :=
  tgap X ≤ 3 / 5 ∧ ∀ a ∈ Low X y, ‖a - y + n‖ ≤ 1 / 20

/-! ## Constants -/

/-- Thin-case bound on `|X ∖ D|` (Lemma T at scale `Λ`; see `thin_card_le43`). -/
def cThin43 : ℝ := 10 ^ 14

/-- Bound on the number of non-good heavy points: `100π·278401² + cThin43 < 10¹⁵`. -/
def cE43 : ℝ := 10 ^ 15

/-- Additive constant of the `4/3` theorem. -/
def C43 : ℝ := 10 ^ 16

/-! ## Elementary facts -/

/-- `v(y) ≤ 12`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `degδ_le_six`, `mS_le_degδ`. Difficulty S. -/
theorem vR_le_twelve (X : Finset Pt) (y : Pt) : vR X y ≤ 12 := by
  unfold vR
  have := degδ_le_six X y
  have := mS_le_degδ X y
  omega

/-- A diametral point has `δ`-degree `≤ 3`.

TODO: prove.
What's missing: as in `mS_le_four_of_D`: for a diametral partner `w` of `z`, every
`δ`-neighbour `q` has `(q − z)·(w − z) ≥ |q − z|²/2 > 0` (`|q − w| ≤ Δ`), i.e. the unit vectors
`q − z` lie in the *open* half-circle around `u = (w − z)/Δ`; pairwise `≥ 1` apart means
pairwise `≥ 60°`, so at most 3 (span `≥ 60(k−1)° < 180°`).  Copy `card_sep_arc_le_four` with
the cone `0 < (q − z)·u` (arc length `< π`) instead of `−1/4 < …` (`< 4π/3`).
Acceptance: no `sorry`.
Depends on: `dist_le_diam`, `one_le_dist`, `card_le_of_sep_real`, `exists_angle` (as in
`card_sep_arc_le_four`). Difficulty M. -/
theorem degδ_le_three_of_D (hX : Normal X) {z : Pt} (hz : z ∈ Dset X) : degδ X z ≤ 3 := by
  sorry

/-- Points of `D` have `v ≤ 6` (paper §1.1: "Points of `R ∩ D` have `v ≤ 6`").

TODO: none — proved.
Acceptance: no `sorry` (inherits `degδ_le_three_of_D`).
Depends on: `degδ_le_three_of_D`, `mS_le_degδ`. Difficulty S. -/
theorem vR_le_six_of_D (hX : Normal X) {z : Pt} (hz : z ∈ Dset X) : vR X z ≤ 6 := by
  unfold vR
  have := degδ_le_three_of_D hX hz
  have := mS_le_degδ X z
  omega

/-- (F′0) In a frame, `K` lies below the support line at `p₀`: `⟨k − y, n⟩ ≤ h`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `Frame43.foot_normal`. Difficulty S. -/
theorem Frame43.top {y n : Pt} (hF : Frame43 X y n) {k : Pt} (hk : k ∈ KBall X) :
    inner ℝ (k - y) n ≤ depth X y := by
  have h := hF.foot_normal k hk
  have e : k - (y + depth X y • n) = (k - y) - depth X y • n := by abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hF.unit] at h
  linarith

/-- Two frames at points at distance `≤ 2` have normals within `ε₀` (paper §1.4: "Two good
points `y, y′` with `|y − y′| ≤ 2` have frames with `∠(n₀(y), n₀(y′)) ≤ ε₀`"): the foot `p₀′` of
`y′` is within `3` of `y`, and `n′` is a unit normal there.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `Frame43.normals`, `Frame43.foot_mem`. Difficulty S. -/
theorem frame_normal_close {y y' n n' : Pt} (hF : Frame43 X y n) (hF' : Frame43 X y' n')
    (hd : dist y y' ≤ 2) : ‖n' - n‖ ≤ ε₀43 := by
  refine hF.normals _ hF'.foot_mem ?_ n' hF'.foot_normal hF'.unit
  have h1 : dist y' (y' + depth X y' • n') = depth X y' := by
    rw [dist_eq_norm, show y' - (y' + depth X y' • n') = -(depth X y' • n') by abel, norm_neg,
      norm_smul, hF'.unit, mul_one, Real.norm_eq_abs, abs_of_pos hF'.depth_pos]
  have := dist_triangle y y' (y' + depth X y' • n')
  have := hF'.depth_le
  linarith

/-! ## The charging lemma (§1.4, combinatorial core) -/

/-- **Charging lemma.**  Let `v ≤ 12` on `R`, `E ⊆ R` (exceptions), and let every
`y ∈ R ∖ E` with `v y ≥ 9` have a set `rec y ⊆ R` of receivers with `v y ≤ 8 + |rec y|` and
`v ≤ 7` on `rec y`, the receiver sets of distinct such `y` being disjoint.  Then
`Σ_R v ≤ 8|R| + 4|E|`.  (Each heavy `y` passes its excess `v y − 8` to its receivers, which have
deficit `≥ 1` each and receive from one owner only; exceptions keep excess `≤ 4`.)

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S–M. -/
theorem charge_sum {R E : Finset Pt} (v : Pt → ℕ) (rec : Pt → Finset Pt)
    (hv : ∀ y ∈ R, v y ≤ 12) (hER : E ⊆ R)
    (hrec : ∀ y ∈ R \ E, 9 ≤ v y →
      rec y ⊆ R ∧ v y ≤ 8 + (rec y).card ∧ ∀ a ∈ rec y, v a ≤ 7)
    (hdisj : ∀ y ∈ R \ E, 9 ≤ v y → ∀ y' ∈ R \ E, 9 ≤ v y' → y ≠ y' →
      Disjoint (rec y) (rec y')) :
    ∑ y ∈ R, v y ≤ 8 * R.card + 4 * E.card := by
  set H := (R \ E).filter (fun y => 9 ≤ v y) with hH
  set U := H.biUnion rec with hU
  have hHmem : ∀ y ∈ H, y ∈ R \ E ∧ 9 ≤ v y := fun y hy => mem_filter.1 hy
  have hUR : U ⊆ R := by
    intro a ha
    obtain ⟨y, hy, hay⟩ := mem_biUnion.1 ha
    obtain ⟨hy1, hy2⟩ := hHmem y hy
    exact (hrec y hy1 hy2).1 hay
  have hUv : ∀ a ∈ U, v a ≤ 7 := by
    intro a ha
    obtain ⟨y, hy, hay⟩ := mem_biUnion.1 ha
    obtain ⟨hy1, hy2⟩ := hHmem y hy
    exact (hrec y hy1 hy2).2.2 a hay
  have hcardU : U.card = ∑ y ∈ H, (rec y).card := by
    rw [hU]
    apply card_biUnion
    intro y hy y' hy' hne
    exact hdisj y (hHmem y hy).1 (hHmem y hy).2 y' (hHmem y' hy').1 (hHmem y' hy').2 hne
  have hHR : H ⊆ R := fun y hy => (mem_sdiff.1 (hHmem y hy).1).1
  have key : ∀ y ∈ R, v y + (if y ∈ U then 1 else 0) ≤
      8 + (if y ∈ H then (rec y).card else 0) + (if y ∈ E then 4 else 0) := by
    intro y hyR
    by_cases hyU : y ∈ U
    · have h7 := hUv y hyU
      have hyH : y ∉ H := fun hyH => by have := (hHmem y hyH).2; omega
      rw [ite_eq_left hyU, ite_eq_right hyH]
      split_ifs <;> omega
    · rw [ite_eq_right hyU]
      by_cases hyH : y ∈ H
      · obtain ⟨hy1, hy2⟩ := hHmem y hyH
        have := (hrec y hy1 hy2).2.1
        have hyE : y ∉ E := (mem_sdiff.1 hy1).2
        rw [ite_eq_left hyH, ite_eq_right hyE]
        omega
      · rw [ite_eq_right hyH]
        by_cases hyE : y ∈ E
        · rw [ite_eq_left hyE]; have := hv y hyR; omega
        · rw [ite_eq_right hyE]
          have : ¬ 9 ≤ v y := fun h9 => hyH (mem_filter.2 ⟨mem_sdiff.2 ⟨hyR, hyE⟩, h9⟩)
          omega
  have hsum := sum_le_sum key
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul,
    sum_ite_mem, sum_ite_mem, sum_ite_mem, inter_eq_right.2 hUR, inter_eq_right.2 hHR,
    inter_eq_right.2 hER] at hsum
  simp only [sum_const, smul_eq_mul, mul_one] at hsum
  rw [← hcardU] at hsum
  omega

/-! ## The linear programme (weights `2/3, 1/3`) -/

/-- **LP with weights `2/3, 1/3`**: from `μ₂ ≤ p + (3/2)(s − p)`, `μ_δ ≤ e + 4r + C₁`,
`e ≤ s + p + C₂`: `min{μ₂, μ_δ} ≤ (4/3)(s + r) + (1/3)(C₁ + C₂)`.
(`(2/3)(3s/2 − p/2) + (1/3)(s + p + 4r) = (4/3)(s + r)`.)

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp43 {μ₂ μδ s r e p C₁ C₂ : ℝ} (h₂ : μ₂ ≤ p + 3 / 2 * (s - p))
    (hδ : μδ ≤ e + 4 * r + C₁) (he : e ≤ s + p + C₂) :
    min μ₂ μδ ≤ 4 / 3 * (s + r) + 1 / 3 * (C₁ + C₂) := by
  have h1 := min_le_left μ₂ μδ
  have h2 := min_le_right μ₂ μδ
  linarith

/-- The constants fit: `3N₀ + (1/3)(2cE43 + cReg) + cReg ≤ C43`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem consts43 : 3 * N₀ + 1 / 3 * (2 * cE43 + cReg) + cReg ≤ C43 := by
  norm_num [N₀, cE43, cReg, cBad, C43]

end

end Erdos132Main

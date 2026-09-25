import Erdos.E132Main43Frame

/-!
# Erdős Problem 132, `4/3` theorem — classification of heavy points (Lemmas P, M, H, Pin)

Paper: `angle_R6.md` §1.3.  Let `y ∈ R` have a frame `(n, h)` (`Frame43`) and `v(y) ≥ 9`.
Neighbours are unit vectors pairwise `≥ 60°` apart.  *Kinds*: K-row (`S ∖ D`, height
`∈ [h − ε|X|, h]`), D (height `≥ h + t − ε|X|`), interior (`< h`).

* `mS_le_four_of_frame`: `S`-neighbours have height `> −1/4`, so `m_y ≤ 4`; hence
  `(deg, m) ∈ {(5,4), (6,4), (6,3)}`.
* **Lemma P** (`pair_sym`, `pair_K`, `pair_D`): two neighbours of the same kind are
  mirror-symmetric (`|X₁ + X₂|` small); three of one kind are impossible.
* **Lemma M** (`lemmaM`): `m = 4` ⇒ K at `±90°`, D at `±30°` (within `1.2°`).
* **Lemma H** (`lemmaH`): `deg = 6`, `m = 3` ⇒ the hexagon (`hexagon_exact`) is HF1, HF2 or a
  cap.
* **Lemma Pin** (`pin_fan`, `pin_cap`): fans force `t ≥ 0.7`, caps force `t ≤ 0.6`.
* Outputs: `heavy_type : IsFan43 ∨ IsCap43` (consumed by `E132Main43Charge`) and
  `heavy_low : v(y) ≤ 8 + |Low X y|` (both proved from the statements).

Shapes (`FanShape`, `CapShape`) record, besides the slots, the two facts used downstream:
every neighbour of height `≤ −2/3` has height `≤ −4/5` (fan) resp. is within `1/20` of
`y − n` (cap), and `v(y) ≤ 8 + #{neighbours of height ≤ −4/5}`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Shapes -/

/-- **Fan shape** (F6, F5, HF1, HF2): the fan slots, lower neighbours are well below
(`height ≤ −2/3 ⇒ height ≤ −4/5`), and `v ≤ 8 + #{neighbours of height ≤ −4/5}`
(F6: `10 ≤ 8 + 2`; F5, HF: `9 ≤ 8 + 1`). -/
def FanShape (X : Finset Pt) (y n : Pt) : Prop :=
  FanSlots X y n ∧
    (∀ a ∈ nbδ X y, inner ℝ (a - y) n ≤ -(2 / 3) → inner ℝ (a - y) n ≤ -(4 / 5)) ∧
    vR X y ≤ 8 + ((nbδ X y).filter (fun a => inner ℝ (a - y) n ≤ -(4 / 5))).card

/-- **Cap shape**: a K-row neighbour at `σ·60°`, a D-neighbour at `0°`; the only neighbour of
height `≤ −2/3` is `b ≈ y − n` (the points at `±120°` have height `≈ −1/2`); `v = 9 ≤ 8 + 1`. -/
def CapShape (X : Finset Pt) (y n : Pt) : Prop :=
  (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ p ∈ nbδ X y, ∃ z ∈ nbδ X y,
      p ∈ Sset X ∧ p ∉ Dset X ∧ z ∈ Dset X ∧
      Slot y n (σ * (π / 3)) (1 / 20) p ∧ Slot y n 0 (1 / 20) z) ∧
    (∀ a ∈ nbδ X y, inner ℝ (a - y) n ≤ -(2 / 3) → ‖a - y + n‖ ≤ 1 / 20) ∧
    vR X y ≤ 8 + ((nbδ X y).filter (fun a => inner ℝ (a - y) n ≤ -(4 / 5))).card

/-! ## Frame toolkit (private helpers) -/

private theorem c43_np (n : Pt) : inner ℝ n (perp n) = 0 := by
  rw [← det2_eq_inner_perp]; unfold det2; ring

private theorem c43_pn (n : Pt) : inner ℝ (perp n) n = 0 := by
  rw [real_inner_comm]; exact c43_np n

/-- Squared norm in the frame `(n, perp n)`. -/
private theorem c43_sq {n : Pt} (hn : ‖n‖ = 1) (v : Pt) :
    ‖v‖ ^ 2 = inner ℝ v n ^ 2 + inner ℝ v (perp n) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, n1_inner_frame hn v v]; ring

private theorem c43_dirF_n {n : Pt} (hn : ‖n‖ = 1) (ψ : ℝ) :
    inner ℝ (dirF n ψ) n = Real.cos ψ := by
  unfold dirF
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, c43_pn,
    real_inner_self_eq_norm_sq, hn]; ring

private theorem c43_dirF_p {n : Pt} (hn : ‖n‖ = 1) (ψ : ℝ) :
    inner ℝ (dirF n ψ) (perp n) = Real.sin ψ := by
  unfold dirF
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, c43_np,
    real_inner_self_eq_norm_sq, norm_perp, hn]; ring

private theorem c43_abs_n {n : Pt} (hn : ‖n‖ = 1) (v : Pt) : |inner ℝ v n| ≤ ‖v‖ := by
  have := abs_real_inner_le_norm v n; rwa [hn, mul_one] at this

private theorem c43_abs_p {n : Pt} (hn : ‖n‖ = 1) (v : Pt) : |inner ℝ v (perp n)| ≤ ‖v‖ := by
  have := abs_real_inner_le_norm v (perp n); rwa [norm_perp, hn, mul_one] at this

/-- A slot gives both coordinates within `η`. -/
private theorem c43_slot_coords {y n q : Pt} (hn : ‖n‖ = 1) {ψ η : ℝ} (h : Slot y n ψ η q) :
    |inner ℝ (q - y) n - Real.cos ψ| ≤ η ∧
      |inner ℝ (q - y) (perp n) - Real.sin ψ| ≤ η := by
  unfold Slot at h
  constructor
  · have := c43_abs_n hn (q - y - dirF n ψ)
    rw [inner_sub_left, c43_dirF_n hn] at this; linarith
  · have := c43_abs_p hn (q - y - dirF n ψ)
    rw [inner_sub_left, c43_dirF_p hn] at this; linarith

/-- A slot from the coordinates. -/
private theorem c43_slot_of {y n q : Pt} (hn : ‖n‖ = 1) {ψ η : ℝ} (hη : 0 ≤ η)
    (h : (inner ℝ (q - y) n - Real.cos ψ) ^ 2 + (inner ℝ (q - y) (perp n) - Real.sin ψ) ^ 2 ≤
      η ^ 2) : Slot y n ψ η q := by
  unfold Slot
  have e := c43_sq hn (q - y - dirF n ψ)
  rw [inner_sub_left (q - y) (dirF n ψ), inner_sub_left (q - y) (dirF n ψ) (perp n),
    c43_dirF_n hn, c43_dirF_p hn] at e
  nlinarith [norm_nonneg (q - y - dirF n ψ)]

private theorem c43_slot_mono {y n q : Pt} {ψ η η' : ℝ} (h : Slot y n ψ η q) (hle : η ≤ η') :
    Slot y n ψ η' q := le_trans h hle

/-- Neighbours are unit vectors: `Z² + X² = 1`. -/
private theorem c43_unit (hX : Normal X) {y n q : Pt} (hn : ‖n‖ = 1) (hq : q ∈ nbδ X y) :
    inner ℝ (q - y) n ^ 2 + inner ℝ (q - y) (perp n) ^ 2 = 1 := by
  rw [← c43_sq hn, ← dist_eq_norm, dist_of_mem_nbδ hX hq]; norm_num

/-- Distinct neighbours are `≥ 1` apart, in coordinates. -/
private theorem c43_sep (hX : Normal X) {y n q q' : Pt} (hn : ‖n‖ = 1) (hq : q ∈ nbδ X y)
    (hq' : q' ∈ nbδ X y) (hne : q ≠ q') :
    1 ≤ (inner ℝ (q - y) n - inner ℝ (q' - y) n) ^ 2 +
      (inner ℝ (q - y) (perp n) - inner ℝ (q' - y) (perp n)) ^ 2 := by
  have h1 := one_le_dist hX.minDist_eq (mem_nbδ.1 hq).1 (mem_nbδ.1 hq').1 hne
  have e := c43_sq hn ((q - y) - (q' - y))
  rw [inner_sub_left (q - y) (q' - y), inner_sub_left (q - y) (q' - y) (perp n),
    sub_sub_sub_cancel_right] at e
  rw [dist_eq_norm] at h1
  nlinarith

private theorem c43_abs_le_one {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : |b| ≤ 1 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, sq_nonneg (b - 1), sq_nonneg (b + 1)]

private theorem c43_r_lo : (1732 / 1000 : ℝ) < √3 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg 3]

private theorem c43_r_hi : √3 < (17321 / 10000 : ℝ) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg 3]

private theorem c43_r_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- Height lower bound for `S`-neighbours (`frame_outside`). -/
private theorem c43_S_low (hX : Normal X) {y n q : Pt} (hF : Frame43 X y n) (hq : q ∈ nbδ X y)
    (hS : q ∈ Sset X) :
    depth X y - 1 / 49 * |inner ℝ (q - y) (perp n)| ≤ inner ℝ (q - y) n := by
  have := frame_outside hX hF (by rw [dist_of_mem_nbδ hX hq]; norm_num) (Sset_not_interior hX hS)
  unfold ε43 at this; exact this

/-- Height upper bound for K-row neighbours (`Frame43.top`). -/
private theorem c43_K_top {y n q : Pt} (hF : Frame43 X y n) (hq : q ∈ nbδ X y)
    (hD : q ∉ Dset X) : inner ℝ (q - y) n ≤ depth X y :=
  hF.top (ball_polygon_a (mem_nbδ.1 hq).1 hD)

/-- Height lower bound for D-neighbours (`frame_D`). -/
private theorem c43_D_low (hX : Normal X) {y n q : Pt} (hF : Frame43 X y n) (hq : q ∈ nbδ X y)
    (hD : q ∈ Dset X) :
    depth X y + tgap X - 1 / 49 * |inner ℝ (q - y) (perp n)| ≤ inner ℝ (q - y) n := by
  have := frame_D hX hF hD (by rw [dist_of_mem_nbδ hX hq]; norm_num)
  unfold ε43 at this; exact this

private theorem c43_tgap_pos (hX : Normal X) : 0 < tgap X := by
  have hT := two_of_pos hX.dist2_pos
  unfold tgap; linarith [hT.lt]

/-! ## Counting `S`-neighbours -/

/-- At a framed point `m_y ≤ 4`: `S`-neighbours are not interior, so their height is
`≥ h − 1/49 > −1/4` (`frame_outside`), and an open arc of length `< 240°` holds at most four
points `60°` apart.

TODO: prove.
What's missing: `card_sep_arc_le_four` with `n`; cone from `frame_outside`
(`|Xq| ≤ ‖q − y‖ = 1`, `h > 0`) and `Sset_not_interior`; separation `one_le_dist`.
Acceptance: no `sorry`.
Depends on: `card_sep_arc_le_four`, `frame_outside`, `Sset_not_interior`, `one_le_dist`,
`norm_perp`. Difficulty S–M. -/
theorem mS_le_four_of_frame (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) : mS X y ≤ 4 := by
  have hn := hF.unit
  unfold mS
  apply card_sep_arc_le_four (y := y) hn
  · intro q hq; exact dist_of_mem_nbδ hX (mem_filter.1 hq).1
  · intro q hq q' hq' hne
    exact one_le_dist hX.minDist_eq (mem_nbδ.1 (mem_filter.1 hq).1).1
      (mem_nbδ.1 (mem_filter.1 hq').1).1 hne
  · intro q hq
    have h1 := mem_filter.1 hq
    have hlow := c43_S_low hX hF h1.1 h1.2
    have hu := c43_abs_le_one (c43_unit hX hn h1.1)
    have := hF.depth_pos
    nlinarith

/-! ## Lemma P (pairs) -/

/-- **Lemma P, core identity**: two unit vectors at distance `≥ 1` (angle `≥ 60°`) satisfy
`|X₁ + X₂| ≤ √3·|Z₁ − Z₂|` in any orthonormal frame `(perp n, n)`.
(With `e_i = (sin ψ_i, cos ψ_i)`: `(X₁+X₂)²‖e₁−e₂‖² = (Z₁−Z₂)²‖e₁+e₂‖²`, and
`‖e₁+e₂‖² = 4 − ‖e₁−e₂‖² ≤ 3 ≤ 3‖e₁−e₂‖²`.)  Together with `|Z₁ − Z₂|` this is the paper's
Lemma P: the distance from `e₂` to the mirror image `(−X₁, Z₁)` of `e₁` is
`√((X₁+X₂)² + (Z₁−Z₂)²) = 2|sin((ψ₁+ψ₂)/2)| ≤ 2|Z₁ − Z₂|`.  (For a pair at `≈ ±90°`,
`X₁ + X₂ ≈ 0` automatically and the mirror error is all in `Z₁ − Z₂`.)

TODO: prove.
What's missing: coordinates (`n1_inner_frame`/`inner_pt`, `unit_sq`); the identity above is a
polynomial identity under `X_i² + Z_i² = 1`; then `nlinarith`/`sq_le_sq'`.
Acceptance: no `sorry`.
Depends on: `n1_inner_frame`, `norm_perp`, `inner_pt`. Difficulty M. -/
theorem pair_sym {n e₁ e₂ : Pt} (hn : ‖n‖ = 1) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (hsep : 1 ≤ ‖e₁ - e₂‖) :
    |inner ℝ e₁ (perp n) + inner ℝ e₂ (perp n)| ≤ √3 * |inner ℝ e₁ n - inner ℝ e₂ n| := by
  have e1 := c43_sq hn e₁
  have e2 := c43_sq hn e₂
  have e3 := c43_sq hn (e₁ - e₂)
  rw [h₁] at e1
  rw [h₂] at e2
  rw [inner_sub_left, inner_sub_left] at e3
  set X1 := inner ℝ e₁ (perp n)
  set X2 := inner ℝ e₂ (perp n)
  set Z1 := inner ℝ e₁ n
  set Z2 := inner ℝ e₂ n
  have hs : 1 ≤ ‖e₁ - e₂‖ ^ 2 := by nlinarith [norm_nonneg (e₁ - e₂)]
  have hid : (X1 + X2) ^ 2 * ((X1 - X2) ^ 2 + (Z1 - Z2) ^ 2) =
      (Z1 - Z2) ^ 2 * ((X1 + X2) ^ 2 + (Z1 + Z2) ^ 2) := by
    have hab : (X1 + X2) * (X1 - X2) + (Z1 - Z2) * (Z1 + Z2) = 0 := by nlinarith
    linear_combination ((X1 + X2) * (X1 - X2) - (Z1 - Z2) * (Z1 + Z2)) * hab
  have hsum : (X1 + X2) ^ 2 + (Z1 + Z2) ^ 2 ≤ 3 := by nlinarith
  have hB : 1 ≤ (X1 - X2) ^ 2 + (Z1 - Z2) ^ 2 := by nlinarith
  have key : (X1 + X2) ^ 2 ≤ 3 * (Z1 - Z2) ^ 2 := by
    by_contra hc
    push Not at hc
    have h1 : (Z1 - Z2) ^ 2 * ((X1 + X2) ^ 2 + (Z1 + Z2) ^ 2) ≤ 3 * (Z1 - Z2) ^ 2 :=
      by nlinarith [sq_nonneg (Z1 - Z2)]
    have h2 : 3 * (Z1 - Z2) ^ 2 * ((X1 - X2) ^ 2 + (Z1 - Z2) ^ 2) <
        (X1 + X2) ^ 2 * ((X1 - X2) ^ 2 + (Z1 - Z2) ^ 2) :=
      mul_lt_mul_of_pos_right hc (by linarith)
    nlinarith [sq_nonneg (Z1 - Z2)]
  have h3 : |X1 + X2| ≤ |√3 * (Z1 - Z2)| := by
    rw [← sq_le_sq, mul_pow, c43_r_sq]; exact key
  rwa [abs_mul, abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))] at h3

/-- **Lemma P (K)**: two distinct K-row neighbours are mirror-symmetric: heights within
`1/49` (both in `[h − 1/49, h]`) and `|X₁ + X₂| ≤ √3/49 < 1/25`.

TODO: prove.
What's missing: heights from `Frame43.top` (`ball_polygon_a`) and `frame_outside`
(`Sset_not_interior`), `|X_i| ≤ 1`; `pair_sym` with `e_i = q_i − y`
(`dist_of_mem_nbδ`, `one_le_dist`).
Acceptance: no `sorry`.
Depends on: `pair_sym`, `frame_outside`, `Frame43.top`, `ball_polygon_a`, `Sset_not_interior`.
Difficulty M. -/
theorem pair_K (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q₁ q₂ : Pt}
    (h₁ : q₁ ∈ nbδ X y) (h₂ : q₂ ∈ nbδ X y) (hne : q₁ ≠ q₂)
    (hS₁ : q₁ ∈ Sset X) (hD₁ : q₁ ∉ Dset X) (hS₂ : q₂ ∈ Sset X) (hD₂ : q₂ ∉ Dset X) :
    |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 1 / 49 ∧
      |inner ℝ (q₁ - y) (perp n) + inner ℝ (q₂ - y) (perp n)| ≤ 1 / 25 := by
  have hn := hF.unit
  have l1 := c43_S_low hX hF h₁ hS₁
  have l2 := c43_S_low hX hF h₂ hS₂
  have t1 := c43_K_top hF h₁ hD₁
  have t2 := c43_K_top hF h₂ hD₂
  have a1 := c43_abs_le_one (c43_unit hX hn h₁)
  have a2 := c43_abs_le_one (c43_unit hX hn h₂)
  have hZ : |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 1 / 49 := by
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨hZ, ?_⟩
  have hu1 : ‖q₁ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₁]
  have hu2 : ‖q₂ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₂]
  have hsep : 1 ≤ ‖(q₁ - y) - (q₂ - y)‖ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact one_le_dist hX.minDist_eq (mem_nbδ.1 h₁).1 (mem_nbδ.1 h₂).1 hne
  have hs := pair_sym hn hu1 hu2 hsep
  have := c43_r_hi
  nlinarith [abs_nonneg (inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n)]

/-- **Lemma P (D)**: two distinct D-neighbours are mirror-symmetric: heights differ by
`≤ (9/400)|X₁ − X₂| ≤ 9/200` and `|X₁ + X₂| ≤ √3·(9/200) < 2/25`.

TODO: prove.
What's missing: `dd_heights`, `|X₁ − X₂| ≤ 2`, `pair_sym`.
Acceptance: no `sorry`.
Depends on: `dd_heights`, `pair_sym`, `dist_of_mem_nbδ`, `one_le_dist`. Difficulty M. -/
theorem pair_D (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q₁ q₂ : Pt}
    (h₁ : q₁ ∈ nbδ X y) (h₂ : q₂ ∈ nbδ X y) (hne : q₁ ≠ q₂)
    (hD₁ : q₁ ∈ Dset X) (hD₂ : q₂ ∈ Dset X) :
    |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 9 / 200 ∧
      |inner ℝ (q₁ - y) (perp n) + inner ℝ (q₂ - y) (perp n)| ≤ 2 / 25 := by
  have hn := hF.unit
  have hdd := dd_heights hX hF hD₁ hD₂ (dist_of_mem_nbδ hX h₁).le (dist_of_mem_nbδ hX h₂).le
  have a1 := c43_abs_le_one (c43_unit hX hn h₁)
  have a2 := c43_abs_le_one (c43_unit hX hn h₂)
  have hd2 : |inner ℝ (q₁ - y) (perp n) - inner ℝ (q₂ - y) (perp n)| ≤ 2 := by
    have := abs_sub (inner ℝ (q₁ - y) (perp n)) (inner ℝ (q₂ - y) (perp n)); linarith
  have hZ : |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 9 / 200 := by nlinarith
  refine ⟨hZ, ?_⟩
  have hu1 : ‖q₁ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₁]
  have hu2 : ‖q₂ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₂]
  have hsep : 1 ≤ ‖(q₁ - y) - (q₂ - y)‖ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact one_le_dist hX.minDist_eq (mem_nbδ.1 h₁).1 (mem_nbδ.1 h₂).1 hne
  have hs := pair_sym hn hu1 hu2 hsep
  have := c43_r_hi
  nlinarith [abs_nonneg (inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n)]

/-! ## The exact hexagon -/

/-- **Exact hexagon**: if `y` has six `δ`-neighbours, they form a regular hexagon: the set of
neighbours is invariant under rotation by `60°` about `y`.

TODO: prove.
What's missing: write `q − y = dirVec(θ_q)`; distinct neighbours are `≥ 1` apart, i.e. the
angles are pairwise `≥ π/3` apart on the circle; six such angles have all six consecutive gaps
`≥ π/3` summing to `2π`, so every gap equals `π/3`; hence `rot (π/3)` maps each neighbour to
the next one (`rot`, `dirVec_add`).
Acceptance: no `sorry`.
Depends on: `exists_angle`, `rot`, `one_le_dist`, `dist_of_mem_nbδ`. Difficulty M–L. -/
theorem hexagon_exact (hX : Normal X) {y : Pt} (h6 : degδ X y = 6) :
    ∀ q ∈ nbδ X y, y + rot (π / 3) (q - y) ∈ nbδ X y := by
  sorry

/-! ## Lemma M and Lemma H -/

/-- **Lemma M** (`m_y = 4`): the four `S`-neighbours are K-row points within `1/40` of the
slots `±90°` and D-points (in `S`) within `1/40` of the slots `±30°`.

TODO: prove.
What's missing (paper §1.3): all four have angle in `[−91.17°, 91.17°]` (height
`≥ −1/49`) and are pairwise `≥ 60°` apart, so their angles are within `1.17°` of
`−90°, −30°, 30°, 90°` (chord `≤ 0.0204 < 1/40`).  By `pair_K`/`pair_D` at most two of each
kind and same-kind pairs are mirror pairs, so the kinds pair up as `{±90°}`, `{±30°}`.  K at
`±30°` would force `h ≥ cos 31.2° > 0.85` (`Frame43.top`) while D at `±90°` needs height
`≥ h + t − 1/49` (`frame_D`) but has height `≤ 0.021`: contradiction.
Acceptance: no `sorry`.
Depends on: `mS_le_four_of_frame`-style angle bounds, `pair_K`, `pair_D`, `frame_outside`,
`frame_D`, `Frame43.top`, `Sset_not_interior`, `exists_angle`. Difficulty L. -/
theorem lemmaM (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (hm : mS X y = 4) :
    ∃ p₁ ∈ nbδ X y, ∃ p₂ ∈ nbδ X y, ∃ z₁ ∈ nbδ X y, ∃ z₂ ∈ nbδ X y,
      p₁ ∈ Sset X ∧ p₁ ∉ Dset X ∧ p₂ ∈ Sset X ∧ p₂ ∉ Dset X ∧
      z₁ ∈ Sset X ∧ z₁ ∈ Dset X ∧ z₂ ∈ Sset X ∧ z₂ ∈ Dset X ∧
      Slot y n (π / 2) (1 / 40) p₁ ∧ Slot y n (-(π / 2)) (1 / 40) p₂ ∧
      Slot y n (π / 6) (1 / 40) z₁ ∧ Slot y n (-(π / 6)) (1 / 40) z₂ := by
  sorry

/-- **F6 / F5** (`m = 4`, `deg ≥ 5`) have fan shape.

TODO: prove.
What's missing: `lemmaM`; slots with `σ = 1`, `p = p₂`, `q = p₁ ∈ S`, `z₁`.  Remaining
neighbours (one for F5, two for F6) are `≥ 60°` from the slots `±90°` (within `1.17°`), so
their angle is in `[148.8°, 211.2°]`: height `≤ −cos 31.2° < −0.85`; all other neighbours have
height `≥ −0.03`.  Count: `v = deg + 4 ≤ 8 + (deg − 4)`.
Acceptance: no `sorry`.
Depends on: `lemmaM`, `hexagon_exact` (F6), `dist_of_mem_nbδ`, `one_le_dist`.
Difficulty M. -/
theorem fanShape_of_m4 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (hm : mS X y = 4) (hd : 5 ≤ degδ X y) : FanShape X y n := by
  sorry

/-- **Lemma H** (`deg = 6`, `m = 3`): the exact hexagon is within `1.3°` of
`{±30°, ±90°, ±150°}` (HF1: K pair at `±90°` + D at `±30°`; HF2: D pair at `±30°` + K at
`±90°`) or of `{0°, ±60°, ±120°, 180°}` (cap: K pair at `±60°` + D at `0°`).

TODO: prove.
What's missing (paper §1.3 enumeration): two of the three `S`-neighbours have the same kind
(`pair_K`/`pair_D`: mirror pair), which pins the hexagon offset (`hexagon_exact`) to `≈ 0°` or
`≈ 30°`; only slots with height `> −1/49` can hold `S`-points; excluded cases (K pair at
`±30°` + D at `±90°`; D pair at `±60°` + K at `0°`; D pair at `±90°` + K at `±30°`; three of
one kind) by `Frame43.top`, `frame_outside`, `frame_D` as in the paper.  Offsets from the
mirror error `≤ 2|Z₁ − Z₂|` (`pair_sym`): `≤ 1.2°` for a K pair (HF1 at `±90°`, cap at `±60°`),
`≤ 2.6°` for the D pair of HF2 (`≤ 1.3°` using `dd_heights` with `|X₁ − X₂| ≈ 1`); all
chords `≤ 0.046 < 1/20`.
Fan: slots with `σ` chosen so that the K-row point is at `−σ·90°` (HF2: `q` = hexagon vertex at
`σ·90°`, `z₂` at `−σ·30°`, `dist z₁ z₂ = 1` from `hexagon_exact`); lower points at `≈ ±150°`
(height `≤ −cos 32.6° < −0.84`).  Cap: the point at `180°` has height `≤ −0.99`, those at
`±120°` height `≥ −0.53 > −2/3`.
Acceptance: no `sorry`.
Depends on: `hexagon_exact`, `pair_K`, `pair_D`, `frame_outside`, `frame_D`, `Frame43.top`,
`Sset_not_interior`. Difficulty L. -/
theorem lemmaH (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (hd : degδ X y = 6) (hm : mS X y = 3) : FanShape X y n ∨ CapShape X y n := by
  sorry

/-! ## Lemma Pin -/

/-- **Lemma Pin (fan)**: fan slots force `t ≥ 0.7` (paper: `t ∈ [0.74, 0.99]`, referee exact
window `[0.751, 0.950]`).

TODO: prove.
What's missing: `p` (K-row, slot `−σ·90°`, height `≤ 1/20`) and `z₁` (D, slot `σ·30°`, height
`≥ √3/2 − 1/20`): `Δc ≥ 0.766`.  Take `w` from `n1_circle_normal` (`|p − w| = Δ₂`,
`ν = (p − w)/Δ₂` an outer unit normal at `p ∈ ∂K`, `ball_polygon_b`); `‖ν − n‖ ≤ 1/50`
(`Frame43.normals`), so `⟨z₁ − p, w − p⟩/Δ₂ ≤ −Δc + 2/50 < 0`: `z₁` is not normal for `p`,
hence `|z₁ − w| = Δ` (`dist_le_dist2`: otherwise `≤ Δ₂` and the inner product is
`≥ |z₁ − p|²/2 > 0`).  Law of cosines: `⟨z₁ − p, w − p⟩/Δ₂ = −t + (d² − t²)/(2Δ₂)`, `d ≤ 2`,
`t ≤ 1` (`ball_polygon_c`): `t ≥ 0.766 − 0.04 − 10⁻⁴ > 0.7`.
Acceptance: no `sorry`.
Depends on: `n1_circle_normal`, `ball_polygon_b`, `ball_polygon_c`, `dist_le_dist2`,
`Frame43.normals`, `n1_inner_frame`. Difficulty M. -/
theorem pin_fan (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hs : FanSlots X y n) :
    7 / 10 ≤ tgap X := by
  sorry

/-- **Lemma Pin (cap)**: cap shape forces `t ≤ 0.6` (paper: `[0.43, 0.57]`, referee
`[0.442, 0.558]`).

TODO: prove.
What's missing: `frame_D` at `z` (slot `0°`: height `≤ 1`, `|Xz| ≤ 1/20`) and `Frame43.top` at
`p` (slot `σ·60°`: height `≥ 1/2 − 1/20`): `t ≤ Z z − Z p + |Xz|/49 ≤ 0.551`.
Acceptance: no `sorry`.
Depends on: `frame_D`, `Frame43.top`, `ball_polygon_a`, `n1_inner_frame`. Difficulty S–M. -/
theorem pin_cap (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hc : CapShape X y n) :
    tgap X ≤ 3 / 5 := by
  obtain ⟨⟨σ, hσ, p, hp, z, hz, -, hpD, hzD, hsp, hsz⟩, -, -⟩ := hc
  have hn := hF.unit
  have htop := c43_K_top hF hp hpD
  have hfD := c43_D_low hX hF hz hzD
  obtain ⟨hpZ, -⟩ := c43_slot_coords hn hsp
  obtain ⟨-, hzX⟩ := c43_slot_coords hn hsz
  have hcos : Real.cos (σ * (π / 3)) = 1 / 2 := by
    rcases hσ with rfl | rfl
    · rw [one_mul, Real.cos_pi_div_three]
    · rw [neg_one_mul, Real.cos_neg, Real.cos_pi_div_three]
  rw [hcos] at hpZ
  rw [Real.sin_zero, sub_zero] at hzX
  have hz1 := c43_unit hX hn hz
  have hzZ : inner ℝ (z - y) n ≤ 1 := by nlinarith [sq_nonneg (inner ℝ (z - y) (perp n))]
  have h1 := (abs_le.1 hpZ).1
  nlinarith [abs_nonneg (inner ℝ (z - y) (perp n))]

/-! ## Outputs -/

/-- Heavy framed points have fan or cap shape.

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `mS_le_four_of_frame`, `degδ_le_six`, `fanShape_of_m4`, `lemmaH`. -/
theorem heavy_shape (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (h9 : 9 ≤ vR X y) : FanShape X y n ∨ CapShape X y n := by
  have hm := mS_le_four_of_frame hX hF
  have hd := degδ_le_six X y
  unfold vR at h9
  by_cases h4 : mS X y = 4
  · exact Or.inl (fanShape_of_m4 hX hF hy h4 (by omega))
  · exact lemmaH hX hF hy (by omega) (by omega)

/-- **Classification output (types)**: a heavy framed point is of fan or cap type.

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `heavy_shape`, `pin_fan`, `pin_cap`, `Low_Z`, `Low_subset`. -/
theorem heavy_type (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (h9 : 9 ≤ vR X y) : IsFan43 X y n ∨ IsCap43 X y n := by
  rcases heavy_shape hX hF hy h9 with ⟨hs, hlow, -⟩ | hc
  · refine Or.inl ⟨pin_fan hX hF hs, fun a ha => ?_, hs⟩
    have hZ := Low_Z hX hF ha
    have := hlow a (Low_subset X y ha) hZ
    rw [show y - a = -(a - y) by abel, inner_neg_left]
    linarith
  · exact Or.inr ⟨pin_cap hX hF hc, fun a ha => hc.2.1 a (Low_subset X y ha) (Low_Z hX hF ha)⟩

/-- **Classification output (excess)**: `v(y) ≤ 8 + |Low X y|` at a heavy framed point.

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `heavy_shape`, `lower_mem_Low`. -/
theorem heavy_low (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (h9 : 9 ≤ vR X y) : vR X y ≤ 8 + (Low X y).card := by
  have hsub : (nbδ X y).filter (fun a => inner ℝ (a - y) n ≤ -(4 / 5)) ⊆ Low X y :=
    fun a ha => lower_mem_Low hX hF (mem_filter.1 ha).1 (mem_filter.1 ha).2
  have hc := card_le_card hsub
  rcases heavy_shape hX hF hy h9 with ⟨-, -, hv⟩ | ⟨-, -, hv⟩ <;> omega

end

end Erdos132Main

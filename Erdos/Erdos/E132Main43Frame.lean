import Erdos.E132Main43Defs

/-!
# Erdős Problem 132, `4/3` theorem — facts in the local frame (Lemma F′, Lemma DN)

Paper: `angle_R6.md` §1.2.  Everything is derived from the fields of `Frame43 X y n`
(`E132Main43Defs`); no arc length and no graph function `f` (see `MAIN43_PLAN.md`,
"Deviations").  Notation: `h = depth X y`, `Z q = ⟨q − y, n⟩` (height), `Xq = ⟨q − y, perp n⟩`
(abscissa), `t = tgap X`, `ε = ε43 = 1/49`.

| paper | here |
|---|---|
| (F′0) `K` below the support line at `p₀` | `Frame43.top` (Defs): `Z k ≤ h` |
| (F′1) `q ∉ int K` ⇒ `q_z ≥ f(q_x) ≥ −ε|q_x|` | `frame_outside`: `Z q ≥ h − ε|Xq|` |
| (F′0) `U′ ⊂ int K` | `frame_mem_interior` (contrapositive) |
| (F′3) D-points are `t` above the graph | `frame_D`: `Z z ≥ h + t − ε|Xz|` |
| (F′4) inward normals within `ε₀` of `−n₀` | `Frame43.normals` |
| Lemma DN (`τ₃ < 0.0267`, `τ* < 0.0224`) | `frame_dn` (`3/100`), `frame_dn1` (`9/400`) |
| Corollary D–D heights | `dd_heights` |

Plus the receiver facts used by `E132Main43Classify` and `E132Main43Charge`:
`Low_Z` (receivers have height `≤ −2/3`), `lower_mem_Low` (neighbours of height `≤ −4/5` are
receivers), `card_cone_le_two` (window packing).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Neighbours and receivers: bookkeeping -/

/-- Membership in `nbδ`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `mem_partners`. Difficulty S. -/
theorem mem_nbδ {y q : Pt} : q ∈ nbδ X y ↔ q ∈ X ∧ q ≠ y ∧ dist y q = minDist X :=
  mem_partners

/-- `δ`-neighbours are at distance `1` (normalised).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `mem_nbδ`. Difficulty S. -/
theorem dist_of_mem_nbδ (hX : Normal X) {y q : Pt} (hq : q ∈ nbδ X y) : dist q y = 1 := by
  rw [dist_comm, (mem_nbδ.1 hq).2.2, hX.minDist_eq]

/-- Receivers are neighbours.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem Low_subset (X : Finset Pt) (y : Pt) : Low X y ⊆ nbδ X y := filter_subset _ _

/-- Receivers are interior to `K` (depth `≥ 2/3 > 0`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem Low_interior {y a : Pt} (ha : a ∈ Low X y) : a ∈ interior (KBall X) := by
  obtain ⟨-, haK, hd⟩ := mem_filter.1 ha
  have h0 : 0 ≤ depth X y := Metric.infDist_nonneg
  by_contra hint
  have hfr : a ∈ frontier (KBall X) := ⟨subset_closure haK, hint⟩
  have : depth X a = 0 := Metric.infDist_zero_of_mem hfr
  linarith

/-! ## Lemma F′ -/

/-- Helper: `⟨n, perp n⟩ = 0`. -/
private theorem inner_self_perp (n : Pt) : inner ℝ n (perp n) = 0 := by
  rw [← det2_eq_inner_perp]; unfold det2; ring

/-- Helper: a unit vector within `1/50` of the unit vector `n` has frame coefficients
`⟨ν, n⟩ ≥ 4999/5000` and `|⟨ν, perp n⟩| ≤ 1/50`. -/
private theorem near_coeffs {n ν : Pt} (hn : ‖n‖ = 1) (hν : ‖ν‖ = 1) (h : ‖ν - n‖ ≤ 1 / 50) :
    4999 / 5000 ≤ inner ℝ ν n ∧ |inner ℝ ν (perp n)| ≤ 1 / 50 := by
  have e := norm_sub_sq_real ν n
  rw [hν, hn] at e
  have h2 : ‖ν - n‖ ^ 2 ≤ (1 / 50) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hα : 4999 / 5000 ≤ inner ℝ ν n := by nlinarith
  have hf := n1_norm_sq_frame hn ν
  rw [hν] at hf
  have hα1 : inner ℝ ν n ≤ 1 := by nlinarith [sq_nonneg (inner ℝ ν (perp n))]
  refine ⟨hα, abs_le.2 ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg (inner ℝ ν (perp n))]

/-- **(F′1)** A point within `6` of `y` that is not interior to `K` is not below the frame's
tangent cone: `Z q ≥ h − ε|Xq|`.

TODO: prove.
What's missing: `exists_frontier_seg` (from `y ∈ int K` to `q`) gives `b = y + l(q − y)`,
`l ∈ (0, 1]`, on `∂K` with `dist y b ≤ 6`; a unit normal `ν` at `b` (`exists_unit_normal`) has
`‖ν − n‖ ≤ 1/50` (`hF.normals`).  `⟨q − b, ν⟩ = ((1−l)/l)⟨b − y, ν⟩ ≥ 0` (`y ∈ K`) and
`⟨b − p₀, ν⟩ ≥ 0` (`p₀ = y + h n ∈ K`), so `⟨q − p₀, ν⟩ ≥ 0`.  With `α = ⟨ν, n⟩ ≥ 1 − 1/5000`,
`|β| = |⟨ν, perp n⟩| ≤ 1/50` (from `‖ν − n‖ ≤ 1/50`; frame decomposition `n1_inner_frame`):
`α(Z q − h) + β Xq ≥ 0`, so `h − Z q ≤ |Xq|·(1/50)/(1 − 1/5000) ≤ |Xq|/49`.
Acceptance: no `sorry`.
Depends on: `exists_frontier_seg`, `exists_unit_normal`, `KBall_convex`, `KBall_isClosed`,
`Frame43` fields, `n1_inner_frame`, `norm_perp`. Difficulty M. -/
theorem frame_outside (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q : Pt}
    (hq : dist q y ≤ 6) (hqi : q ∉ interior (KBall X)) :
    depth X y - ε43 * |inner ℝ (q - y) (perp n)| ≤ inner ℝ (q - y) n := by
  obtain ⟨l, hl0, hl1, hb⟩ := exists_frontier_seg (KBall_isClosed X) hF.mem_int hqi
  obtain ⟨ν, hν1, hν⟩ := exists_unit_normal (KBall_convex X) ⟨y, hF.mem_int⟩ hb
  have hdb : dist y (y + l • (q - y)) ≤ 6 := by
    rw [dist_eq_norm, show y - (y + l • (q - y)) = -(l • (q - y)) by abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hl0, ← dist_eq_norm]
    nlinarith [dist_nonneg (x := q) (y := y)]
  have hνn := hF.normals _ hb hdb ν hν hν1
  obtain ⟨hα, hβ⟩ := near_coeffs hF.unit hν1 hνn
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν1
  have hpos := inner_pos_of_seg hF.mem_int hl0 hν hν0
  have hp0 : y + depth X y • n ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hF.foot_mem.1
  have h2 := hν _ hp0
  have e : y + depth X y • n - (y + l • (q - y)) = depth X y • n - l • (q - y) := by abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm ν n] at h2
  have hfr := n1_inner_frame hF.unit (q - y) ν
  have hlI : l * inner ℝ (q - y) ν ≤ inner ℝ (q - y) ν := by nlinarith
  have hXb : inner ℝ (q - y) (perp n) * inner ℝ ν (perp n) ≤
      |inner ℝ (q - y) (perp n)| * (1 / 50) := by
    calc _ ≤ |inner ℝ (q - y) (perp n) * inner ℝ ν (perp n)| := le_abs_self _
      _ = |inner ℝ (q - y) (perp n)| * |inner ℝ ν (perp n)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hβ (abs_nonneg _)
  have hh0 : 0 ≤ depth X y := hF.depth_pos.le
  unfold ε43
  by_contra hc
  push Not at hc
  have hA := abs_nonneg (inner ℝ (q - y) (perp n))
  have hD : 0 ≤ depth X y - inner ℝ (q - y) n := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hα hD]

/-- **(F′0, `U′ ⊂ int K`)** A point within `6` of `y` strictly below the tangent cone is
interior to `K`.

TODO: none — proved.
Acceptance: no `sorry` (inherits `frame_outside`).
Depends on: `frame_outside`. Difficulty S. -/
theorem frame_mem_interior (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q : Pt}
    (hq : dist q y ≤ 6)
    (hlt : inner ℝ (q - y) n < depth X y - ε43 * |inner ℝ (q - y) (perp n)|) :
    q ∈ interior (KBall X) := by
  by_contra h
  have := frame_outside hX hF hq h
  linarith

/-- **(F′3)** Diametral points near `y` are `t` above the tangent cone:
`Z z ≥ h + t − ε|Xz|`.

TODO: prove.
What's missing: `t ≤ dist z y ≤ 3` (`ball_polygon_c`, `y ∈ K`).  For `0 ≤ s < t` the point
`w = z − s n` has `dist w z = s < t ≤ dist(z, K)` (`ball_polygon_c`), so `w ∉ K`, and
`dist w y ≤ 3 + t ≤ 6`; `frame_outside` at `w` (same abscissa, height `Z z − s`) gives
`Z z ≥ h + s − ε|Xz|`; let `s → t` (or argue by contradiction with a suitable `s`).
Acceptance: no `sorry`.
Depends on: `frame_outside`, `ball_polygon_c`, `norm_perp`. Difficulty M. -/
theorem frame_D (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 3) :
    depth X y + tgap X - ε43 * |inner ℝ (z - y) (perp n)| ≤ inner ℝ (z - y) n := by
  sorry

/-- **Lemma 3.2(a), general form**: for a diametral pair `(z, w)` every `k ∈ X` has
`⟨k − z, w − z⟩ ≥ ‖k − z‖²/2` (as `|k − w| ≤ Δ = |z − w|`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `dist_le_diam`. Difficulty S. -/
theorem D_inner {z w k : Pt} (hw : w ∈ X) (hk : k ∈ X) (hzw : dist z w = diam X) :
    ‖k - z‖ ^ 2 / 2 ≤ inner ℝ (k - z) (w - z) := by
  have e := norm_sub_sq_real (k - z) (w - z)
  rw [show k - z - (w - z) = k - w by abel] at e
  have h1 : ‖k - w‖ ≤ diam X := by rw [← dist_eq_norm]; exact dist_le_diam hk hw
  have h2 : ‖w - z‖ = diam X := by rw [← dist_eq_norm, dist_comm]; exact hzw
  have h3 : ‖k - w‖ ^ 2 ≤ diam X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [h2] at e
  linarith

/-! ## Lemma DN -/

/-- **Lemma DN** (D-normals are nearly vertical): for `z ∈ D` within `3` of `y` and a diametral
partner `w`, `u = w − z` points downwards and `|⟨u, perp n⟩| ≤ (3/100)·(−⟨u, n⟩)`
(paper: `τ₃ = (463ε + 3)/460 < 0.0267`).

TODO: prove.
What's missing: every `k ∈ K` has `⟨k − z, u⟩ > 0` (`|k − w| ≤ Δ₂ < Δ`; `dist2 < diam`).
(i) `⟨u, n⟩ < 0`: the point `G = z − s n` with `s = Z z − h + ε|Xz| + 1/100 > 0` (`frame_D`)
has height `< h − ε|XG|` and `dist G y ≤ 6`, so `G ∈ int K` (`frame_mem_interior`) and
`0 < ⟨G − z, u⟩ = −s⟨u, n⟩`.  (ii) With `c = −⟨u,n⟩ > 0`, `a₁ = ⟨u, perp n⟩`, the far points
`g±` (`hF.far`, abscissa `±463`, height `≥ h − 9.31`) give
`(±463 − Xz) a₁ > (Z g± − Z z) c ≥ −(9.31 + 3) c` (`Z z ≤ 3`, `h ≥ 0`), so
`|a₁| ≤ 12.31 c/460 < 0.0268 c`.  Decompose with `n1_inner_frame`.
Acceptance: no `sorry`.
Depends on: `frame_D`, `frame_mem_interior`, `Frame43.far`, `Frame43.top`, `n1_inner_frame`,
`dist_le_dist2`. Difficulty M. -/
theorem frame_dn (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z w : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 3) (hw : w ∈ X) (hzw : dist z w = diam X) :
    inner ℝ (w - z) n < 0 ∧ |inner ℝ (w - z) (perp n)| ≤ 3 / 100 * -inner ℝ (w - z) n := by
  sorry

/-- **Lemma DN for D-neighbours** (`dist z y ≤ 1`): `|⟨u, perp n⟩| ≤ (9/400)·(−⟨u, n⟩)`
(paper: `τ* = (463ε + 1)/462 < 0.0224`; here `(9.31 + 1)/462 < 0.02232 ≤ 9/400`).

TODO: prove.
What's missing: as `frame_dn` with `|Xz| ≤ 1`, `Z z ≤ 1`: `|a₁| ≤ 10.31 c/462`.
Acceptance: no `sorry`.
Depends on: as `frame_dn` (or share a helper). Difficulty M. -/
theorem frame_dn1 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z w : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 1) (hw : w ∈ X) (hzw : dist z w = diam X) :
    inner ℝ (w - z) n < 0 ∧ |inner ℝ (w - z) (perp n)| ≤ 9 / 400 * -inner ℝ (w - z) n := by
  sorry

/-- **Corollary (D–D heights)**: two diametral points within `1` of `y` have
`|Z z₁ − Z z₂| ≤ (9/400)|Xz₁ − Xz₂|`.

TODO: prove.
What's missing: Lemma 3.2(a) both ways (`D_inner` with `k = z₂` and the partner `w₁` of `z₁`,
and vice versa): `⟨z₂ − z₁, w₁ − z₁⟩ ≥ 0` with `w₁ − z₁ = a₁ perp n − c₁ n`, `c₁ > 0`,
`|a₁| ≤ (9/400) c₁` (`frame_dn1`) gives `(Z z₂ − Z z₁) c₁ ≤ (Xz₂ − Xz₁) a₁`; symmetric.
Decompose with `n1_inner_frame`.
Acceptance: no `sorry`.
Depends on: `D_inner`, `frame_dn1`, `n1_inner_frame`. Difficulty M. -/
theorem dd_heights (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z₁ z₂ : Pt}
    (hz₁ : z₁ ∈ Dset X) (hz₂ : z₂ ∈ Dset X) (h₁ : dist z₁ y ≤ 1) (h₂ : dist z₂ y ≤ 1) :
    |inner ℝ (z₁ - y) n - inner ℝ (z₂ - y) n| ≤
      9 / 400 * |inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)| := by
  sorry

/-! ## Depth and receivers -/

/-- Depth is at most the vertical distance to the support line: `depth a ≤ h − Z a` for
`a ∈ K`.

TODO: prove.
What's missing: if `a ∈ ∂K` the depth is `0 ≤ h − Z a` (`Frame43.top`).  Otherwise the ray
`a + s n` leaves `K` for `s > h − Z a` (`Frame43.top`), so `exists_frontier_seg` from `a` to
`a + (h − Z a + η) n` gives a frontier point at distance `≤ h − Z a + η`; let `η → 0`
(`Metric.infDist_le_dist_of_mem`).
Acceptance: no `sorry`.
Depends on: `Frame43.top`, `exists_frontier_seg`, `KBall_isClosed`. Difficulty M. -/
theorem frame_depth_le (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a : Pt}
    (ha : a ∈ KBall X) : depth X a ≤ depth X y - inner ℝ (a - y) n := by
  sorry

/-- Receivers have height `≤ −2/3`.

TODO: none — proved.
Acceptance: no `sorry` (inherits `frame_depth_le`).
Depends on: `frame_depth_le`. Difficulty S. -/
theorem Low_Z (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a : Pt} (ha : a ∈ Low X y) :
    inner ℝ (a - y) n ≤ -(2 / 3) := by
  obtain ⟨-, haK, hd⟩ := mem_filter.1 ha
  have := frame_depth_le hX hF haK
  linarith

/-- A neighbour of height `≤ −4/5` is a receiver.

TODO: prove.
What's missing: `a ∈ int K` by `frame_mem_interior` (`Z a ≤ −0.8 < h − |Xa|/49`, `h > 0`).
Depth: for `b ∈ ∂K`, either `dist a b > 2 ≥ h + 2/3` (`h ≤ 1`), or `dist b y ≤ 3`, `b ∉ int K`,
so `Z b ≥ h − 3/49` (`frame_outside`) and `dist a b ≥ Z b − Z a ≥ h + 0.8 − 0.0613 ≥ h + 2/3`;
`Metric.le_infDist` (frontier nonempty, e.g. the foot).
Acceptance: no `sorry`.
Depends on: `frame_outside`, `frame_mem_interior`, `dist_of_mem_nbδ`, `Frame43.foot_mem`,
`Metric.le_infDist`. Difficulty M. -/
theorem lower_mem_Low (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a : Pt}
    (ha : a ∈ nbδ X y) (hz : inner ℝ (a - y) n ≤ -(4 / 5)) : a ∈ Low X y := by
  sorry

/-- **Window packing**: unit vectors `q − a`, pairwise `≥ 1` apart (i.e. `≥ 60°`), all strictly
within `60°` of `n` (`⟨q − a, n⟩ > 1/2`), number at most `2`.

TODO: prove.
What's missing: as `card_sep_arc_le_four` with the cone `1/2 < ⟨·, n⟩` (open arc of length
`2π/3`): three points pairwise `≥ π/3` apart span `≥ 2π/3`.  Or directly: angles `ψ_i ∈
(−π/3, π/3)`, sorted, `ψ₃ − ψ₁ ≥ 2π/3` impossible.
Acceptance: no `sorry`.
Depends on: `exists_angle`, `card_le_of_sep_real` (as in `card_sep_arc_le_four`).
Difficulty M. -/
theorem card_cone_le_two {a n : Pt} (hn : ‖n‖ = 1) (P : Finset Pt)
    (h1 : ∀ q ∈ P, dist q a = 1) (hsep : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → 1 ≤ dist q q')
    (hcone : ∀ q ∈ P, 1 / 2 < inner ℝ (q - a) n) : P.card ≤ 2 := by
  sorry

end

end Erdos132Main

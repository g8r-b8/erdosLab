import Erdos.E132Main2116Defs

/-!
# Erdős Problem 132, `21/16` — the flat model at a good′ point (radius-6 frame layer)

Paper §10, lem:frame and lem:DN at scale `ε₀ = 10⁻⁶`, `Λ = 10⁹`, `ρ = 6`, and **lem:flatmodel**
(a)–(d), with the consequences listed after tab:margins (neighbour kinds, mirror pairs,
hexagons).  Everything is stated for a `FrameP X y n` (`E132Main2116Defs`); heights are
`Z q = ⟨q − y, n⟩`, abscissae `⟨q − y, perp n⟩`, `h = depth X y`; the *level* of `q` is
`Z q − h`.

Design: the `4/3` frame layer (`E132Main43Frame`) is proved for the fixed constants of
`Frame43` (`ε₀ = 1/50`, `Λ = 464`); rather than parametrising (which would have meant
changing proved files), this file restates the few facts needed at the new scale and the fill
agent copies the `4/3` proofs with the constants replaced.  `FrameP.toFrame43` lets every
coarse `4/3` frame lemma (`frame_outside`, `frame_D`, `dd_heights`, …) be used directly.

Constants: slope `εP = 2·10⁻⁶` (so `6εP ≤ δ₀/5`), DN slope `κD = 2·10⁻⁶`, level error
`δ₀ = 10⁻⁴`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Frame basics -/

/-- (F′0) `K` lies below the support line at `p₀`: `Z k ≤ h` for `k ∈ K`.

TODO: none — proved (copy of `Frame43.top`).
Acceptance: no `sorry`. Difficulty S. -/
theorem FrameP.top {y n : Pt} (hF : FrameP X y n) {k : Pt} (hk : k ∈ KBall X) :
    inner ℝ (k - y) n ≤ depth X y := by
  have h := hF.foot_normal k hk
  have e : k - (y + depth X y • n) = (k - y) - depth X y • n := by abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hF.unit] at h
  linarith

/-- A `FrameP` is a `Frame43` (normals within `10⁻⁶ ≤ 1/50` on radius `10 ≥ 6`; the far point
at abscissa `±463` is the convex combination `p₀ + (463/(Λ − 1))(g − p₀)`, of height
`≥ h − 463·1011/(Λ − 1) ≥ h − 9.31`).  So all `4/3` frame lemmas apply at a good′ point.

TODO: prove.
What's missing: fields `unit … foot_normal` copy; `normals`: `dist ≤ 6 ≤ 10` and
`ε₀P ≤ ε₀43`; `far`: from `hF.far σ` get `g`; put `g′ = p₀ + λ(g − p₀)` with
`λ = 463/(10⁹ − 1)`, `p₀ = y + h n`; `g′ ∈ K` (`KBall_convex`, `p₀ ∈ K` as the frontier of a
closed set), `⟨g′ − y, perp n⟩ = λσ(10⁹ − 1) = 463σ` (`⟨n, perp n⟩ = 0`), and
`⟨g′ − y, n⟩ = h + λ(⟨g − y, n⟩ − h) ≥ h − 1011λ ≥ h − 9.31`.
Acceptance: no `sorry`.
Depends on: `KBall_convex`, `KBall_isClosed`, definitions. Difficulty S. -/
theorem FrameP.toFrame43 {y n : Pt} (hF : FrameP X y n) : Frame43 X y n := by
  sorry

/-- **(F′1) at scale `Λ`** (G1, G4): a point within `6` of `y` that is not interior to `K` lies
above the tangent cone of slope `εP`: `Z q ≥ h − εP |X q|`.

TODO: prove.
What's missing: copy `frame_outside` (`E132Main43Frame`) with `1/50 ↦ ε₀P`, `1/49 ↦ εP`
(the exit point `b` of `[y, q]` is within `6 ≤ 10` of `y`, its unit normal `ν` has
`‖ν − n‖ ≤ 10⁻⁶`, and `⟨q − y, ν⟩ > 0`, `⟨p₀ − b, ν⟩ ≤ 0`); `near_coeffs` must be recopied
with the new constant.
Acceptance: no `sorry`.
Depends on: `exists_frontier_seg`, `exists_unit_normal`, `inner_pos_of_seg`,
`n1_inner_frame`, `FrameP.normals`. Difficulty M (copy). -/
theorem frameP_outside (hX : Normal X) {y n : Pt} (hF : FrameP X y n) {q : Pt}
    (hq : dist q y ≤ 6) (hqi : q ∉ interior (KBall X)) :
    depth X y - εP * |inner ℝ (q - y) (perp n)| ≤ inner ℝ (q - y) n := by
  sorry

/-- **(G3) at scale `Λ`**: a diametral point within `6` of `y` has level
`≥ t − εP |X z|`.

TODO: prove.
What's missing: copy `frame_D` (`E132Main43Frame`) with radius `6`: `dist(z, K) ≥ t`
(`ball_polygon_c`), so `z − s n ∉ int K` for `0 ≤ s < t`; apply `frameP_outside` to these
points (they are within `6` of `y`: `Z z ≥ −6εP > −t/2` unless … — if the radius becomes an
issue, first note `t ≤ dist z y ≤ 6` and use the radius-10 normals of `FrameP` in a local
copy of `frameP_outside` at radius `10`).
Acceptance: no `sorry`.
Depends on: `ball_polygon_c`, `frameP_outside`. Difficulty M. -/
theorem frameP_D (hX : Normal X) {y n : Pt} (hF : FrameP X y n) {z : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 6) :
    depth X y + tgap X - εP * |inner ℝ (z - y) (perp n)| ≤ inner ℝ (z - y) n := by
  sorry

/-- **Lemma DN at scale `Λ`**: the diametral partner `w` of a diametral point `z` within `6`
of `y` is almost straight below: `|X(w − z)| ≤ κD·(−Z(w − z))`, `κD = 2·10⁻⁶`
(paper: `κ_D < 2·10⁻⁶` with `ξ = ζ = 6`).

TODO: prove.
What's missing: copy `frame_dn` (`E132Main43Frame`): the far points `g± ∈ K` (abscissa
`±(Λ − 1)`, height `≥ h − 1011`) satisfy `|g± − w| ≤ Δ₂ < Δ = |z − w|`, hence
`⟨g± − z, w − z⟩ > 0`; both `g± − z` point below `z` (`Z g ≤ h < Z z`, `frameP_D`) with slope
`≤ (6 + 1011 + 1)/(Λ − 7)`, so `w − z` lies in the downward cone of that slope; `≤ κD`.
Acceptance: no `sorry`.
Depends on: `FrameP.far`, `FrameP.top`, `frameP_D`, `D_inner`. Difficulty M (copy). -/
theorem frameP_dn (hX : Normal X) {y n : Pt} (hF : FrameP X y n) {z w : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 6) (hw : w ∈ X) (hzw : dist z w = diam X) :
    inner ℝ (w - z) n < 0 ∧ |inner ℝ (w - z) (perp n)| ≤ κD * -inner ℝ (w - z) n := by
  sorry

/-! ## The flat model (lem:flatmodel) -/

/-- **lem:flatmodel(a), K-row**: a point of `S ∖ D` within `6` of `y` has level in
`[−δ₀/5, 0]` (`6εP = 1.2·10⁻⁵ ≤ 2·10⁻⁵`).

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits `frameP_outside`).
Depends on: `frameP_outside`, `FrameP.top`, `Sset_not_interior`, `ball_polygon_a`. -/
theorem flat_K (hX : Normal X) {y n : Pt} (hF : FrameP X y n) {q : Pt} (hq : q ∈ Sset X)
    (hqD : q ∉ Dset X) (hqy : dist q y ≤ 6) :
    depth X y - δ₀P / 5 ≤ inner ℝ (q - y) n ∧ inner ℝ (q - y) n ≤ depth X y := by
  have hqX : q ∈ X := (mem_filter.1 hq).1
  refine ⟨?_, hF.top (ball_polygon_a hqX hqD)⟩
  have h := frameP_outside hX hF hqy (Sset_not_interior hX hq)
  have hab : |inner ℝ (q - y) (perp n)| ≤ 6 := by
    have := abs_real_inner_le_norm (q - y) (perp n)
    rw [norm_perp, hF.unit, mul_one, ← dist_eq_norm] at this
    linarith
  have : εP * |inner ℝ (q - y) (perp n)| ≤ δ₀P / 5 := by
    unfold εP δ₀P
    nlinarith [abs_nonneg (inner ℝ (q - y) (perp n))]
  linarith

/-- **lem:flatmodel(a), interior points**: an interior point of `K` has level `< 0`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `FrameP.top`. Difficulty S. -/
theorem flat_int {y n : Pt} (hF : FrameP X y n) {q : Pt} (hq : q ∈ interior (KBall X)) :
    inner ℝ (q - y) n < depth X y := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hq)
  have hmem : q + (ε / 2) • n ∈ KBall X := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.unit, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  have h := hF.top hmem
  rw [show q + (ε / 2) • n - y = (q - y) + (ε / 2) • n by abel, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hF.unit] at h
  linarith

/-- **lem:flatmodel(b)**: there is `H ≥ t − δ₀/2` such that every point of `D` within `6` of
`y` has level in `[H, H + δ₀/2]`.

TODO: prove.
What's missing: let `H` be the smallest level of the (finitely many) points of `D ∩ B̄(y, 6)`
(`H := t` if there is none).  `H ≥ t − 6εP ≥ t − δ₀/2` by `frameP_D`.  Two points `z₁, z₂` of
`D ∩ B̄(y, 6)` have `|Z z₁ − Z z₂| ≤ κD |X z₁ − X z₂| ≤ 12κD < δ₀/2`: copy `dd_heights`
(`E132Main43Frame`) with `frameP_dn` (each `zᵢ` sees `z₁`/`z₂`'s partner nearly below:
`D_inner` for the pair `zᵢ`, `w_{zⱼ}`).
Acceptance: no `sorry`.
Depends on: `frameP_D`, `frameP_dn`, `D_inner`, `Finset.exists_min_image`. Difficulty M. -/
theorem flat_D (hX : Normal X) {y n : Pt} (hF : FrameP X y n) :
    ∃ H : ℝ, tgap X - δ₀P / 2 ≤ H ∧ ∀ z ∈ Dset X, dist z y ≤ 6 →
      depth X y + H ≤ inner ℝ (z - y) n ∧ inner ℝ (z - y) n ≤ depth X y + H + δ₀P / 2 := by
  sorry

/-- **lem:flatmodel(c), pinning**: for a K-row point `k` and a diametral point `z` within `6` of
`y`, the level difference is `t` up to `δ₀/5`.

TODO: prove.
What's missing: paper proof of lem:flatmodel(c).  Put `Δc := Z z − Z k ≥ t − 6εP`
(`frameP_D`, `FrameP.top`).  Take a `Δ₂`-partner `w` of `k` and `u = (w − k)/Δ₂`; `−u` is a unit
outer normal at `k` (`neg_mem_normalCone`), so `‖−u − n‖ ≤ ε₀` (`FrameP.normals`, `k` within
`6`) and `|⟨z − k, u⟩ + Δc| ≤ 12ε₀`.  If `z` is normal for `k` then `⟨z − k, u⟩ ≥ 0`, so
`Δc ≤ 12ε₀` and `|Δc − t| ≤ 12ε₀`.  Otherwise `z` is an exception (`exact_identity_b` with the
partner `w`): `⟨z − k, u⟩ = −t + (d² − t²)/(2Δ₂)` (`d = |zk| ≤ 12`, `t ≤ 6`), so
`|Δc − t| ≤ 12ε₀ + 72/Δ₂ ≤ 1.3·10⁻⁵ ≤ δ₀/5`.
Acceptance: no `sorry`.
Depends on: `frameP_D`, `FrameP.top`, `FrameP.normals`, `neg_mem_normalCone`,
`exact_identity_b` (or its proof), `ball_polygon_b`. Difficulty M. -/
theorem flat_pin (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    {k z : Pt} (hk : k ∈ Sset X) (hkD : k ∉ Dset X) (hky : dist k y ≤ 6) (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 6) :
    |(inner ℝ (z - y) n - inner ℝ (k - y) n) - tgap X| ≤ δ₀P / 5 := by
  sorry

/-- **lem:flatmodel(d)**: two good′ points at distance `≤ 3` have frames with normals within
`ε₀`, and the levels of a common nearby point in the two frames differ by `≤ δ₀/5`.

TODO: prove.
What's missing: `p₀′ = y′ + h′n′` is a boundary point within `4` of `y`, so `‖n′ − n‖ ≤ ε₀`
(`FrameP.normals`, as `frame_normal_close`).  Levels: `Z q − h = ⟨q − p₀, n⟩`, and
`⟨q − p₀, n⟩ − ⟨q − p₀′, n′⟩ = ⟨q − p₀, n − n′⟩ + ⟨p₀′ − p₀, n′⟩`; the first term is
`≤ 7ε₀`; the second is `≥ 0` (`n′` normal at `p₀′`) and `≤ ⟨p₀′ − p₀, n′ − n⟩ ≤ 5ε₀`
(`n` normal at `p₀`).  Total `≤ 12ε₀ ≤ δ₀/5`.
Acceptance: no `sorry`.
Depends on: `FrameP.normals`, `FrameP.foot_normal`, `KBall_isClosed`. Difficulty M. -/
theorem frameP_close {y y' n n' : Pt} (hF : FrameP X y n) (hF' : FrameP X y' n')
    (hd : dist y y' ≤ 3) :
    ‖n' - n‖ ≤ ε₀P ∧ ∀ q : Pt, dist q y ≤ 6 →
      |(inner ℝ (q - y) n - depth X y) - (inner ℝ (q - y') n' - depth X y')| ≤ δ₀P / 5 := by
  sorry

/-! ## Neighbours of a good′ point -/

/-- Every `δ`-neighbour of `y` is a K-row point (`S ∖ D`), a diametral point, or an interior
point of `K` in `R ∖ D` (paper: "every neighbour of `y` is a K-neighbour, a D-neighbour or an
interior neighbour").

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `Rset_interior`, `mem_nbδ`. Difficulty S. -/
theorem nb_kind (hX : Normal X) {y q : Pt} (hq : q ∈ nbδ X y) :
    (q ∈ Sset X ∧ q ∉ Dset X) ∨ q ∈ Dset X ∨
      (q ∈ Rset X ∧ q ∉ Dset X ∧ q ∈ interior (KBall X)) := by
  by_cases hD : q ∈ Dset X
  · exact Or.inr (Or.inl hD)
  by_cases hS : q ∈ Sset X
  · exact Or.inl ⟨hS, hD⟩
  have hR : q ∈ Rset X := mem_sdiff.2 ⟨(mem_nbδ.1 hq).1, hS⟩
  exact Or.inr (Or.inr ⟨hR, hD, Rset_interior hX hR hD⟩)

/-- A neighbour of `y` above level `0` is diametral (paper: "a neighbour with `c > h` is a
D-neighbour").

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits `flat_K`).
Depends on: `nb_kind`, `flat_K`, `flat_int`, `dist_of_mem_nbδ`. -/
theorem nb_above_D (hX : Normal X) {y n : Pt} (hF : FrameP X y n) {q : Pt}
    (hq : q ∈ nbδ X y) (habove : depth X y < inner ℝ (q - y) n) : q ∈ Dset X := by
  rcases nb_kind hX hq with ⟨hS, hD⟩ | hD | ⟨-, -, hint⟩
  · have := (flat_K hX hF hS hD (by rw [dist_of_mem_nbδ hX hq]; norm_num)).2
    linarith
  · exact hD
  · have := flat_int hF hint
    linarith

/-- **Mirror pairs, K-row**: two distinct K-row neighbours of `y` have opposite abscissae up
to `10⁻⁴` (paper: `|ψ₁ + ψ₂| < 0.012°`).  In particular there are at most two of them.

TODO: prove.
What's missing: both are unit vectors from `y` with heights in `[h − δ₀/5, h]` (`flat_K`);
write `Xᵢ² = 1 − Zᵢ²`.  If `X₁, X₂` had the same sign, `|X₁ − X₂| ≤ √(|Z₁² − Z₂²|) ≤ 0.01`
and `|q₁ − q₂| < 1`, contradicting `one_le_dist`.  So they have opposite signs and
`|X₁ + X₂| = ||X₁| − |X₂|| = |Z₂² − Z₁²|/(|X₁| + |X₂|) ≤ 4·10⁻⁵/0.99`.
Acceptance: no `sorry`.
Depends on: `flat_K`, `n1_norm_sq_frame`, `one_le_dist`, `dist_of_mem_nbδ`. Difficulty M. -/
theorem pair_K2116 (hX : Normal X) {y n : Pt} (hF : FrameP X y n) {q₁ q₂ : Pt}
    (h₁ : q₁ ∈ nbδ X y) (h₂ : q₂ ∈ nbδ X y) (hS₁ : q₁ ∈ Sset X) (hS₂ : q₂ ∈ Sset X)
    (hD₁ : q₁ ∉ Dset X) (hD₂ : q₂ ∉ Dset X) (hne : q₁ ≠ q₂) :
    |inner ℝ (q₁ - y) (perp n) + inner ℝ (q₂ - y) (perp n)| ≤ 1 / 10 ^ 4 := by
  sorry

/-- **Mirror pairs, D**: two distinct diametral neighbours of `y` have opposite abscissae up
to `2·10⁻⁴`.

TODO: prove.
What's missing: as `pair_K2116`, with heights in `[h + H, h + H + δ₀/2]` (`flat_D`):
`|Z₂² − Z₁²| ≤ 10⁻⁴`.
Acceptance: no `sorry`.
Depends on: `flat_D`, `n1_norm_sq_frame`, `one_le_dist`, `dist_of_mem_nbδ`. Difficulty M. -/
theorem pair_D2116 (hX : Normal X) {y n : Pt} (hF : FrameP X y n) {q₁ q₂ : Pt}
    (h₁ : q₁ ∈ nbδ X y) (h₂ : q₂ ∈ nbδ X y) (hD₁ : q₁ ∈ Dset X) (hD₂ : q₂ ∈ Dset X)
    (hne : q₁ ≠ q₂) :
    |inner ℝ (q₁ - y) (perp n) + inner ℝ (q₂ - y) (perp n)| ≤ 2 / 10 ^ 4 := by
  sorry

/-- **Hexagon**: six `δ`-neighbours (pairwise `≥ 1` apart, at distance `1`) form an exact
regular hexagon, in any unit frame `n`.

TODO: prove.
What's missing: write the neighbours as `y + dirF n ψᵢ` (angles mod `2π`, `exists_angle`);
pairwise distance `≥ 1` ⇔ angular gaps `≥ π/3`; six gaps `≥ π/3` summing to `2π` are all
`= π/3`.  (`hexagon_exact` of `E132Main43Classify` proves closure under `rot (π/3)`; either
reuse it or redo the angle count as in `degδ_le_three_of_D`.)
Acceptance: no `sorry`.
Depends on: `exists_angle`, `dist_of_mem_nbδ`, `one_le_dist`, `sqd_lt_of_arg`.
Difficulty M. -/
theorem hex_of_deg6 (hX : Normal X) {y n : Pt} (hn : ‖n‖ = 1) (hdeg : degδ X y = 6) :
    ∃ θ₀ : ℝ, IsHexNb X y n θ₀ 1 := by
  sorry

end

end Erdos132Main

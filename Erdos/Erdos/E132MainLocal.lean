import Erdos.E132MainDefs
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Erdős Problem 132, `54/37` theorem — local geometry (§3) and bad edges (§5)

Lemmas 3.1–3.4, the rung identity, the T-edge/rung dichotomy, (T1), (T2), arc spacing,
turning along an arc; the lens lemma 5.1, lens-corner arc length 5.2, and the bad-edge counts
KK, DD, (c1), (c2).  See `E132MainDefs.lean` for the conventions.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Helpers: distances of `X`, the direction field, planar coordinates -/

theorem mem_distSetS {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    dist x y ∈ distSetS X := by
  simp only [distSetS, pairsS, mem_image, mem_filter]
  exact ⟨s(x, y), ⟨Finset.mk_mem_sym2_iff.2 ⟨hx, hy⟩, by simpa using hxy⟩, rfl⟩

theorem nonneg_of_mem_distSetS {d : ℝ} (hd : d ∈ distSetS X) : 0 ≤ d := by
  simp only [distSetS, mem_image] at hd
  obtain ⟨z, -, rfl⟩ := hd
  induction z using Sym2.ind with
  | _ a b => exact (dist_nonneg : 0 ≤ dist a b)

theorem diam_nonneg (X : Finset Pt) : 0 ≤ diam X := by
  unfold diam; split_ifs with h
  · exact nonneg_of_mem_distSetS (max'_mem _ h)
  · exact le_rfl

theorem dist2_nonneg (X : Finset Pt) : 0 ≤ dist2 X := by
  unfold dist2; split_ifs with h
  · exact nonneg_of_mem_distSetS (mem_of_mem_erase (max'_mem _ h))
  · exact le_rfl

theorem le_diam_of_mem {d : ℝ} (hd : d ∈ distSetS X) : d ≤ diam X := by
  unfold diam; rw [dif_pos ⟨_, hd⟩]; exact le_max' _ _ hd

theorem dist2_le_diam (X : Finset Pt) : dist2 X ≤ diam X := by
  unfold dist2; split_ifs with h
  · exact le_diam_of_mem (mem_of_mem_erase (max'_mem _ h))
  · exact diam_nonneg X

theorem dist_le_diam {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) : dist x y ≤ diam X := by
  by_cases hxy : x = y
  · subst hxy; rw [dist_self]; exact diam_nonneg X
  · exact le_diam_of_mem (mem_distSetS hx hy hxy)

theorem dist_le_dist2 {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hne : dist x y ≠ diam X) :
    dist x y ≤ dist2 X := by
  by_cases hxy : x = y
  · subst hxy; rw [dist_self]; exact dist2_nonneg X
  · have hm : dist x y ∈ (distSetS X).erase (diam X) := mem_erase.2 ⟨hne, mem_distSetS hx hy hxy⟩
    unfold dist2; rw [dif_pos ⟨_, hm⟩]; exact le_max' _ _ hm

theorem minDist_le_dist {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    minDist X ≤ dist x y := by
  have hm := mem_distSetS hx hy hxy
  unfold minDist; rw [dif_pos ⟨_, hm⟩]; exact min'_le _ _ hm

theorem mem_partners {d : ℝ} {p q : Pt} :
    q ∈ partners X d p ↔ q ∈ X ∧ q ≠ p ∧ dist p q = d := by
  simp [partners]

theorem mem_of_mem_Sset {p : Pt} (hp : p ∈ Sset X) : p ∈ X := (mem_filter.1 hp).1

theorem dist2_pos_of_mem_Sset {p : Pt} (hp : p ∈ Sset X) : 0 < dist2 X := by
  obtain ⟨q, hq⟩ := (mem_filter.1 hp).2
  obtain ⟨-, hqp, h⟩ := mem_partners.1 hq
  rw [← h]; exact dist_pos.2 (Ne.symm hqp)

theorem diam_pos_of_mem_Sset {p : Pt} (hp : p ∈ Sset X) : 0 < diam X :=
  (dist2_pos_of_mem_Sset hp).trans_le (dist2_le_diam X)

theorem mem_Dset_of {y q : Pt} (hy : y ∈ X) (hq : q ∈ X) (h : dist y q = diam X)
    (hpos : 0 < diam X) : y ∈ Dset X := by
  refine mem_filter.2 ⟨hy, q, mem_partners.2 ⟨hq, ?_, h⟩⟩
  rintro rfl; rw [dist_self] at h; linarith

theorem dist_ne_diam_of_not_mem_Dset {y q : Pt} (hy : y ∈ X) (hyD : y ∉ Dset X) (hq : q ∈ X)
    (hqy : q ≠ y) : dist y q ≠ diam X := by
  intro h
  exact hyD (mem_filter.2 ⟨hy, q, mem_partners.2 ⟨hq, hqy, h⟩⟩)

/-- The partner distance `|p x_p|` (`Δ₂` or `Δ`). -/
theorem DirField.dist_partner (F : DirField X) {p : Pt} (hp : p ∈ Sset X) :
    dist p (F.partner p) = if p ∈ Dset X then diam X else dist2 X := by
  split_ifs with h
  · exact F.partner_D p hp h
  · exact F.partner_K p hp h

theorem DirField.dist_partner_pos (F : DirField X) {p : Pt} (hp : p ∈ Sset X) :
    0 < dist p (F.partner p) := by
  rw [F.dist_partner hp]; split_ifs
  · exact diam_pos_of_mem_Sset hp
  · exact dist2_pos_of_mem_Sset hp

/-- `u_p` is a unit vector for `p ∈ S` (local copy of `DirField.norm_u`, proved here so that
this file does not depend on the `sorry` in `E132MainDefs`). -/
theorem DirField.norm_u' (F : DirField X) {p : Pt} (hp : p ∈ Sset X) : ‖F.u p‖ = 1 := by
  have h := F.dist_partner_pos hp
  rw [DirField.u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h, ← dist_eq_norm,
    dist_comm (F.partner p) p, inv_mul_cancel₀ h.ne']

theorem DirField.inner_u (F : DirField X) (p y : Pt) :
    inner ℝ y (F.u p) = (dist p (F.partner p))⁻¹ * inner ℝ y (F.partner p - p) := by
  rw [DirField.u, real_inner_smul_right]

/-- Law of cosines in inner-product form. -/
theorem two_inner_sub (y p w : Pt) :
    2 * inner ℝ (y - p) (w - p) = dist y p ^ 2 + dist w p ^ 2 - dist y w ^ 2 := by
  have h := norm_sub_sq_real (y - p) (w - p)
  rw [show y - p - (w - p) = y - w by abel] at h
  rw [dist_eq_norm y p, dist_eq_norm w p, dist_eq_norm y w]
  linarith

/-- Chord `≤` arc: `‖a − b‖ ≤ ∠(a, b)` for unit vectors. -/
theorem norm_sub_le_ang {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a - b‖ ≤ ang a b := by
  have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm a b
  rw [ha, hb, mul_one, mul_one] at hc
  have h1 := Real.one_sub_sq_div_two_le_cos (x := ang a b)
  have h0 : 0 ≤ ang a b := InnerProductGeometry.angle_nonneg a b
  have hsq : ‖a - b‖ ^ 2 ≤ ang a b ^ 2 := by
    rw [norm_sub_sq_real, ha, hb, ← hc]; unfold ang at h1 h0 ⊢; nlinarith
  nlinarith [norm_nonneg (a - b)] 

theorem inner_coord (x y : Pt) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem norm_sq_coord (x : Pt) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord]; ring

theorem det2_eq_inner_perp (u e : Pt) : det2 u e = inner ℝ e (perp u) := by
  simp [det2, perp, inner_coord]; ring

theorem lagrange (e u : Pt) : inner ℝ e u ^ 2 + det2 u e ^ 2 = ‖e‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_sq_coord, norm_sq_coord, inner_coord, det2]; ring

theorem decomp {u : Pt} (hu : ‖u‖ = 1) (e : Pt) :
    e = inner ℝ e u • u + det2 u e • perp u := by
  have h := norm_sq_coord u
  rw [hu] at h
  ext i; fin_cases i <;> simp [inner_coord, det2, perp]
  · linear_combination (e 0) * h
  · linear_combination (e 1) * h


/-! ## §3 Ball polygon and exact identities -/

/-- **Lemma 3.1(a)** `X ∖ D ⊆ K`.

TODO: prove.
What's missing: a non-diametral point has all its distances `≤ Δ₂` (no distance of `X` lies in
`(Δ₂, Δ)`, by definition of `dist2` as a max of `distSet ∖ {Δ}`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S–M. -/
theorem ball_polygon_a {y : Pt} (hy : y ∈ X) (hyD : y ∉ Dset X) : y ∈ KBall X := by
  simp only [KBall, Set.mem_iInter, Metric.mem_closedBall]
  intro w hw
  rw [Finset.mem_coe] at hw
  by_cases hwy : w = y
  · subst hwy; rw [dist_self]; exact dist2_nonneg X
  · exact dist_le_dist2 hy hw (dist_ne_diam_of_not_mem_Dset hy hyD hw hwy)

/-- **Lemma 3.1(b)** `S ∖ D ⊆ ∂K`.

TODO: prove.
What's missing: `v ∈ K ∩ C(w, Δ₂)` with `K ⊆ D(w, Δ₂)` is not interior.
Acceptance: no `sorry`.
Depends on: `ball_polygon_a`. Difficulty S–M. -/
theorem ball_polygon_b {v : Pt} (hv : v ∈ Sset X) (hvD : v ∉ Dset X) : v ∈ frontier (KBall X) := by
  have hK := ball_polygon_a (mem_of_mem_Sset hv) hvD
  obtain ⟨w, hw⟩ := (mem_filter.1 hv).2
  obtain ⟨hwX, -, hd⟩ := mem_partners.1 hw
  have hpos := dist2_pos_of_mem_Sset hv
  refine ⟨subset_closure hK, fun hint => ?_⟩
  have hsub : KBall X ⊆ Metric.closedBall w (dist2 X) :=
    Set.biInter_subset_of_mem (by simpa using hwX)
  have := interior_mono hsub hint
  rw [interior_closedBall w hpos.ne', Metric.mem_ball] at this
  linarith

/-- **Lemma 3.1(c)** `dist(z, K) ≥ t` for `z ∈ D`.

TODO: prove.
What's missing: `K ⊆ D(x, Δ₂)` for the diametral partner `x` of `z`; triangle inequality.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem ball_polygon_c {z y : Pt} (hz : z ∈ Dset X) (hy : y ∈ KBall X) : tgap X ≤ dist z y := by
  obtain ⟨x, hx⟩ := (mem_filter.1 hz).2
  obtain ⟨hxX, -, hd⟩ := mem_partners.1 hx
  have hy' : dist y x ≤ dist2 X := by
    have := Set.mem_iInter₂.1 hy x (by simpa using hxX); simpa using this
  have := dist_triangle z y x
  unfold tgap; linarith

/-- The direction field exists.

TODO: prove (choose partners; `p ∈ S ∖ D` → a `Δ₂`-partner, `p ∈ S ∩ D` → a diametral one).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem dirField_nonempty (X : Finset Pt) : Nonempty (DirField X) := by
  refine ⟨⟨(fun p => if h : (partners X (diam X) p).Nonempty then h.choose
      else if h' : (partners X (dist2 X) p).Nonempty then h'.choose else p), ?_, ?_, ?_⟩⟩
  · intro p hp
    split_ifs with h h'
    · exact (mem_partners.1 h.choose_spec).1
    · exact (mem_partners.1 h'.choose_spec).1
    · exact absurd (mem_filter.1 hp).2 h'
  · intro p hp hpD
    have h : ¬ (partners X (diam X) p).Nonempty := fun h =>
      hpD (mem_filter.2 ⟨mem_of_mem_Sset hp, h⟩)
    have h' := (mem_filter.1 hp).2
    simp only [dif_neg h, dif_pos h']
    exact (mem_partners.1 h'.choose_spec).2.2
  · intro p _ hpD
    have h := (mem_filter.1 hpD).2
    simp only [dif_pos h]
    exact (mem_partners.1 h.choose_spec).2.2

/-- `u_p` is a unit vector for `p ∈ S`.

TODO: prove (`partner p ≠ p` since its distance is `Δ₂ > 0` or `Δ > 0`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem DirField.norm_u (F : DirField X) {p : Pt} (hp : p ∈ Sset X) : ‖F.u p‖ = 1 := by
  exact F.norm_u' hp

/-- **Lemma 3.2(a)** For `p ∈ S ∩ D`: `(y − p)·u_p ≥ |y − p|²/(2Δ)`.

TODO: prove (law of cosines, `|y − x_p| ≤ Δ`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S–M. -/
theorem exact_identity_a (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∈ Dset X)
    (hy : y ∈ X) : dist y p ^ 2 / (2 * diam X) ≤ inner ℝ (y - p) (F.u p) := by
  have hΔ := F.partner_D p hp hpD
  have hpos := diam_pos_of_mem_Sset hp
  have hle := dist_le_diam hy (F.partner_mem p hp)
  have key := two_inner_sub y p (F.partner p)
  rw [dist_comm (F.partner p) p, hΔ] at key
  have h2 : dist y (F.partner p) ^ 2 ≤ diam X ^ 2 := pow_le_pow_left₀ dist_nonneg hle 2
  rw [F.inner_u, hΔ, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hpos]
  nlinarith

/-- **Lemma 3.2(b)** For `p ∈ S ∖ D`: normal (`(y − p)·u_p ≥ |y − p|²/(2Δ₂)`) or exception
(`|y w_p| = Δ`).

TODO: prove (law of cosines; `|y w_p| ∈ [0, Δ₂] ∪ {Δ}`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S–M. -/
theorem exact_identity_b (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X)
    (hy : y ∈ X) :
    dist y p ^ 2 / (2 * dist2 X) ≤ inner ℝ (y - p) (F.u p) ∨ dist y (F.partner p) = diam X := by
  by_cases hexc : dist y (F.partner p) = diam X
  · exact Or.inr hexc
  left
  have hΔ := F.partner_K p hp hpD
  have hpos := dist2_pos_of_mem_Sset hp
  have hle := dist_le_dist2 hy (F.partner_mem p hp) hexc
  have key := two_inner_sub y p (F.partner p)
  rw [dist_comm (F.partner p) p, hΔ] at key
  have h2 : dist y (F.partner p) ^ 2 ≤ dist2 X ^ 2 := pow_le_pow_left₀ dist_nonneg hle 2
  rw [F.inner_u, hΔ, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hpos]
  nlinarith

/-- **Rung identity, algebra** [C2]: `(1 + Δ₂² − Δ²)/(2Δ₂) = −τ` with `t = Δ − Δ₂`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem rung_identity_alg (Δ Δ₂ : ℝ) (h : Δ₂ ≠ 0) :
    (1 + Δ₂ ^ 2 - Δ ^ 2) / (2 * Δ₂) =
      -((Δ - Δ₂) - (1 - (Δ - Δ₂) ^ 2) / (2 * Δ₂)) := by
  field_simp
  ring

/-- [C2] `τ − t = (t² − 1)/(2Δ₂)`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem tau_sub_tgap (X : Finset Pt) : tau X - tgap X = (tgap X ^ 2 - 1) / (2 * dist2 X) := by
  rw [tau]; ring

/-- [C2] `τ > 1 ⟺ t > 1` (for `t ≥ 0`, `Δ₂ > 0`).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem one_lt_tau_iff_alg {t Δ₂ : ℝ} (ht : 0 ≤ t) (hΔ : 0 < Δ₂) :
    1 < t - (1 - t ^ 2) / (2 * Δ₂) ↔ 1 < t := by
  have e : t - (1 - t ^ 2) / (2 * Δ₂) - 1 = (t - 1) * (1 + (t + 1) / (2 * Δ₂)) := by
    field_simp; ring
  have hf : 0 < 1 + (t + 1) / (2 * Δ₂) := by positivity
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : (t - 1) * (1 + (t + 1) / (2 * Δ₂)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hf.le
    linarith
  · intro h
    have : 0 < (t - 1) * (1 + (t + 1) / (2 * Δ₂)) := mul_pos (by linarith) hf
    linarith

/-- **Lemma 3.2(c)** Exception at distance 1: `(y − p)·u_p = −τ` **exactly**.

TODO: prove.
What's missing: law of cosines in `y p w_p` plus `rung_identity_alg`.
Acceptance: no `sorry`.
Depends on: `rung_identity_alg`, `DirField.norm_u`. Difficulty M. -/
theorem exact_identity_c (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X)
    (hexc : dist y (F.partner p) = diam X) (h1 : dist y p = 1) :
    inner ℝ (y - p) (F.u p) = - tau X := by
  have hΔ := F.partner_K p hp hpD
  have hpos := dist2_pos_of_mem_Sset hp
  have key := two_inner_sub y p (F.partner p)
  rw [dist_comm (F.partner p) p, hΔ, hexc, h1] at key
  have hr := rung_identity_alg (diam X) (dist2 X) hpos.ne'
  rw [F.inner_u, hΔ, tau, tgap, ← hr, inv_mul_eq_div,
    div_eq_div_iff hpos.ne' (by positivity)]
  linear_combination (dist2 X) * key

/-- Exceptions at distance 1 exist only when `τ ≤ 1` (Cauchy–Schwarz on 3.2(c)).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `DirField.norm_u`. Difficulty S. -/
theorem tau_le_one_of_exception (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X)
    (hexc : dist y (F.partner p) = diam X) (h1 : dist y p = 1) : tau X ≤ 1 := by
  have h := exact_identity_c F hp hpD hexc h1
  have hcs := abs_real_inner_le_norm (y - p) (F.u p)
  rw [F.norm_u' hp, ← dist_eq_norm, h1, h, abs_neg, one_mul] at hcs
  exact (le_abs_self _).trans hcs

/-- **Rung offsets**: a rung `(v, z)` has `z − v = −τ u_v + σ s u_v^⊥` with `σ = ±1`,
`s = √(1 − τ²)`.

TODO: prove.
What's missing: decompose the unit vector `z − v` in the orthonormal basis `(u_v, u_v^⊥)`.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `DirField.norm_u`. Difficulty M. -/
theorem rung_offset (F : DirField X) {v z : Pt} (h : IsRung F v z) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ z - v = (-tau X) • F.u v + (σ * sOff X) • perp (F.u v) := by
  obtain ⟨hv, hvD, -, -, h1, hexc⟩ := h
  have hu := F.norm_u' hv
  have ha := exact_identity_c F hv hvD hexc (by rw [dist_comm]; exact h1)
  have hdec := decomp hu (z - v)
  have hlag := lagrange (z - v) (F.u v)
  rw [hu, ← dist_eq_norm, dist_comm, h1, ha] at hlag
  rw [ha] at hdec
  have hs : sOff X = |det2 (F.u v) (z - v)| := by
    rw [sOff, ← Real.sqrt_sq_eq_abs]; congr 1; linarith
  rcases abs_choice (det2 (F.u v) (z - v)) with hb | hb
  · refine ⟨1, Or.inl rfl, ?_⟩; rw [hs, hb, one_mul]; exact hdec
  · refine ⟨-1, Or.inr rfl, ?_⟩; rw [hs, hb, neg_one_mul, neg_neg]; exact hdec

theorem abs_det2_le (w e : Pt) : |det2 w e| ≤ ‖e‖ * ‖w‖ := by
  have h := lagrange e w
  have h2 : det2 w e ^ 2 ≤ (‖e‖ * ‖w‖) ^ 2 := by nlinarith [sq_nonneg (inner ℝ e w)]
  have := sq_le_sq.1 h2
  rwa [abs_of_nonneg (by positivity : 0 ≤ ‖e‖ * ‖w‖)] at this

theorem det2_sub_right (u x y : Pt) : det2 u (x - y) = det2 u x - det2 u y := by
  simp only [det2, PiLp.sub_apply]; ring

theorem det2_sub_left (u v e : Pt) : det2 (u - v) e = det2 u e - det2 v e := by
  simp only [det2, PiLp.sub_apply]; ring

theorem inner_sub_swap (p q w : Pt) : inner ℝ (p - q) w = - inner ℝ (q - p) w := by
  rw [← neg_sub q p, inner_neg_left]

/-- A point `y ≠ p` of `X` is seen from `p ∈ S` either strictly on the inner side
(`(y − p)·u_p > 0`) or as an exception (then `p ∉ D` and `y ∈ D`). -/
theorem inner_pos_or_exc (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hy : y ∈ X)
    (hyp : y ≠ p) :
    0 < inner ℝ (y - p) (F.u p) ∨
      (p ∉ Dset X ∧ dist y (F.partner p) = diam X ∧ y ∈ Dset X) := by
  have hd : 0 < dist y p := dist_pos.2 hyp
  by_cases hpD : p ∈ Dset X
  · left
    have hpos := diam_pos_of_mem_Sset hp
    exact lt_of_lt_of_le (by positivity) (exact_identity_a F hp hpD hy)
  · rcases exact_identity_b F hp hpD hy with h | h
    · left
      have hpos := dist2_pos_of_mem_Sset hp
      exact lt_of_lt_of_le (by positivity) h
    · exact Or.inr ⟨hpD, h, mem_Dset_of hy (F.partner_mem p hp) h (diam_pos_of_mem_Sset hp)⟩

/-- `|(q − p)·u_p + (p − q)·u_q| ≤ |pq| ∠(u_p, u_q)`. -/
theorem abs_inner_add_le (F : DirField X) {p q : Pt} (hp : p ∈ Sset X) (hq : q ∈ Sset X) :
    |inner ℝ (q - p) (F.u p) + inner ℝ (p - q) (F.u q)| ≤ dist p q * ang (F.u p) (F.u q) := by
  rw [inner_sub_swap p q, ← sub_eq_add_neg, ← inner_sub_right]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [← dist_eq_norm, dist_comm]
  exact mul_le_mul_of_nonneg_left (norm_sub_le_ang (F.norm_u' hp) (F.norm_u' hq)) dist_nonneg

theorem IsTEdge.symm {F : DirField X} {p q : Pt} (h : IsTEdge F p q) : IsTEdge F q p :=
  ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩

/-- **Lemma 3.3 (no common normal)**: distinct `p, q ∈ S ∖ D` have `u_p ≠ u_q`.

TODO: prove ((q − p)·u_p > 0 and (p − q)·u_q > 0 by 3.2(b), normal case).
Acceptance: no `sorry`.
Depends on: `exact_identity_b`. Difficulty S–M. -/
theorem u_ne (F : DirField X) {p q : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X) (hq : q ∈ Sset X)
    (hqD : q ∉ Dset X) (hpq : p ≠ q) : F.u p ≠ F.u q := by
  intro heq
  have h1 := inner_pos_or_exc F hp (mem_of_mem_Sset hq) (Ne.symm hpq)
  have h2 := inner_pos_or_exc F hq (mem_of_mem_Sset hp) hpq
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · rw [heq] at h1; rw [inner_sub_swap] at h2; linarith
    · exact hpD h2.2.2
  · exact hqD h1.2.2

/-- **T-edge / rung dichotomy** (§3): if `τ > 2β` every good edge is a T-edge or a rung.

TODO: prove.
What's missing: case analysis on 3.2(a)/(b); `|a + b| ≤ |u_p − u_q| ≤ ∠ ≤ β`; an exception
target is in `D`, which sees everything as normal; an exception with the other end in `(0, β)`
gives `|a + b| ≥ τ − β > β`.
Acceptance: no `sorry`.
Depends on: `exact_identity_a`, `exact_identity_b`, `exact_identity_c`. Difficulty M. -/
theorem good_dichotomy (hX : Normal X) (F : DirField X) (hτ : 2 * beta < tau X) {p q : Pt}
    (hp : p ∈ Sset X) (hq : q ∈ Sset X) (hpq : dist p q = 1)
    (hg : ang (F.u p) (F.u q) ≤ beta) :
    IsTEdge F p q ∨ IsRung F p q ∨ IsRung F q p := by
  have hpq' : p ≠ q := by rintro rfl; simp at hpq
  rcases inner_pos_or_exc F hp (mem_of_mem_Sset hq) hpq'.symm with ha | ⟨hpD, hexc, hqD⟩
  · rcases inner_pos_or_exc F hq (mem_of_mem_Sset hp) hpq' with hb | ⟨hqD, hexc, hpD⟩
    · left
      have hsum := abs_inner_add_le F hp hq
      rw [hpq, one_mul] at hsum
      have := abs_le.1 (hsum.trans hg)
      exact ⟨ha, by linarith, hb, by linarith⟩
    · exact Or.inr (Or.inr ⟨hq, hqD, hp, hpD, by rw [dist_comm]; exact hpq, hexc⟩)
  · exact Or.inr (Or.inl ⟨hp, hpD, hq, hqD, hpq, hexc⟩)

/-- The far end of a good rung: `(v − z)·u_z ∈ [τ − β, τ + β]`.

TODO: prove (`|a + b| ≤ β` with `a = −τ`).
Acceptance: no `sorry`.
Depends on: `exact_identity_c`. Difficulty S. -/
theorem rung_far_end (F : DirField X) {v z : Pt} (h : IsRung F v z)
    (hg : ang (F.u v) (F.u z) ≤ beta) :
    tau X - beta ≤ inner ℝ (v - z) (F.u z) ∧ inner ℝ (v - z) (F.u z) ≤ tau X + beta := by
  obtain ⟨hv, hvD, hz, -, h1, hexc⟩ := h
  have ha := exact_identity_c F hv hvD hexc (by rw [dist_comm]; exact h1)
  have ha' : inner ℝ (v - z) (F.u v) = tau X := by rw [inner_sub_swap, ha, neg_neg]
  have hd := abs_inner_add_le F hv hz
  rw [h1, one_mul, inner_sub_swap z v, ha'] at hd
  have := abs_le.1 (hd.trans hg)
  constructor <;> linarith

/-- **(T1)** each `p` has at most one T-neighbour on each side of `ℝu_p`.

TODO: prove.
What's missing: two T-directions on one side have elevation in `(0, arcsin β)`, so are `< 60°`
apart, but two points at distance 1 from `p` and `≥ 1` from each other are `≥ 60°` apart.
Acceptance: no `sorry`.
Depends on: `DirField.norm_u`. Difficulty M. -/
theorem T1 (hX : Normal X) (F : DirField X) {σ : ℝ} {p q₁ q₂ : Pt} (hσ : σ = 1 ∨ σ = -1)
    (h₁ : IsSideT F σ p q₁) (h₂ : IsSideT F σ p q₂) : q₁ = q₂ := by
  by_contra hne
  obtain ⟨hp, hq₁, hd₁, -, ⟨ha₁, ha₁', -⟩, hs₁⟩ := h₁
  obtain ⟨-, hq₂, hd₂, -, ⟨ha₂, ha₂', -⟩, hs₂⟩ := h₂
  have hmin := minDist_le_dist (mem_of_mem_Sset hq₁) (mem_of_mem_Sset hq₂) hne
  rw [hX.minDist_eq] at hmin
  have hu := F.norm_u' hp
  have l₁ := lagrange (q₁ - p) (F.u p)
  have l₂ := lagrange (q₂ - p) (F.u p)
  have l₃ := lagrange (q₁ - q₂) (F.u p)
  rw [hu, ← dist_eq_norm, dist_comm q₁ p, hd₁] at l₁
  rw [hu, ← dist_eq_norm, dist_comm q₂ p, hd₂] at l₂
  rw [hu, ← dist_eq_norm, show q₁ - q₂ = (q₁ - p) - (q₂ - p) by abel, inner_sub_left,
    det2_sub_right] at l₃
  set a₁ := inner ℝ (q₁ - p) (F.u p)
  set a₂ := inner ℝ (q₂ - p) (F.u p)
  set b₁ := det2 (F.u p) (q₁ - p)
  set b₂ := det2 (F.u p) (q₂ - p)
  have hβ : beta = 1 / 100 := rfl
  rw [hβ] at ha₁' ha₂'
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hbb : 0 < b₁ * b₂ := by
    have := mul_pos hs₁ hs₂
    calc 0 < σ * b₁ * (σ * b₂) := this
      _ = (σ * σ) * (b₁ * b₂) := by ring
      _ = b₁ * b₂ := by rw [hσ2, one_mul]
  have e1 : 1 - (1 / 100 : ℝ) ^ 2 ≤ b₁ ^ 2 := by nlinarith
  have e2 : 1 - (1 / 100 : ℝ) ^ 2 ≤ b₂ ^ 2 := by nlinarith
  have hsq : (1 - (1 / 100 : ℝ) ^ 2) ^ 2 ≤ (b₁ * b₂) ^ 2 := by
    rw [mul_pow]; nlinarith
  have hb : 1 - (1 / 100 : ℝ) ^ 2 ≤ b₁ * b₂ := by nlinarith
  have hd : 1 ≤ dist q₁ q₂ ^ 2 := by nlinarith
  nlinarith

/-- **(T2)** if `q` is the right T-neighbour of `p`, then `p` is the left T-neighbour of `q`.

TODO: prove (`∠(u_p, u_q) ≤ β` and `q − p` nearly perpendicular to both).
Acceptance: no `sorry`.
Depends on: `DirField.norm_u`. Difficulty M. -/
theorem T2 (hX : Normal X) (F : DirField X) {p q : Pt} (h : IsSideT F (-1) p q) :
    IsSideT F 1 q p := by
  obtain ⟨hp, hq, hd, hg, hT, hs⟩ := h
  refine ⟨hq, hp, by rw [dist_comm]; exact hd,
    by rw [ang, InnerProductGeometry.angle_comm]; exact hg, hT.symm, ?_⟩
  have hl := lagrange (q - p) (F.u p)
  rw [F.norm_u' hp, ← dist_eq_norm, dist_comm q p, hd] at hl
  have hβ : beta = 1 / 100 := rfl
  obtain ⟨ha, ha', -⟩ := hT
  rw [hβ] at ha' hg
  have hb : det2 (F.u p) (q - p) ≤ -(1 - (1 / 100) ^ 2) := by nlinarith
  have hdiff := abs_det2_le (F.u q - F.u p) (q - p)
  rw [det2_sub_left, ← dist_eq_norm, dist_comm q p, hd, one_mul] at hdiff
  have hn : ‖F.u q - F.u p‖ ≤ 1 / 100 := by
    refine (norm_sub_le_ang (F.norm_u' hq) (F.norm_u' hp)).trans ?_
    rw [ang, InnerProductGeometry.angle_comm]; exact hg
  have := abs_le.1 (hdiff.trans hn)
  have hneg : det2 (F.u q) (p - q) = - det2 (F.u q) (q - p) := by
    rw [show p - q = -(q - p) by abel]; simp only [det2, PiLp.neg_apply]; ring
  rw [hneg]; nlinarith

/-- T-edges number at most `|S|` (each vertex has `≤ 2` T-edges by (T1)).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `T1`, `two_mul_card_le_of_deg_le`. Difficulty M. -/
theorem card_tEdges_le (hX : Normal X) (F : DirField X) : (tEdges X F).card ≤ (Sset X).card := by
  have h := two_mul_card_le_of_deg_le (V := Sset X) (E := tEdges X F) (k := 2) ?_ ?_
  · omega
  · intro z hz
    have hz' : z ∈ edges X := (mem_filter.1 (mem_filter.1 hz).1).1
    simp only [edges, pairsS, mem_filter] at hz'
    obtain ⟨⟨hs, hnd⟩, -⟩ := hz'
    exact ⟨hnd, fun p hp => Finset.mem_sym2_iff.1 hs p hp⟩
  · intro p _
    have hsub : (tEdges X F).filter (fun z => p ∈ z) ⊆
        ((Sset X).filter (IsSideT F 1 p) ∪ (Sset X).filter (IsSideT F (-1) p)).image
          (fun q => s(p, q)) := by
      intro z hz
      obtain ⟨hzT, hpz⟩ := mem_filter.1 hz
      obtain ⟨q, rfl⟩ := Sym2.mem_iff_exists.1 hpz
      obtain ⟨hzg, hT⟩ := mem_filter.1 hzT
      obtain ⟨hze, hg⟩ := mem_filter.1 hzg
      obtain ⟨hzP, hzd⟩ := mem_filter.1 hze
      simp only [pairsS, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at hzP
      obtain ⟨⟨hp, hq⟩, -⟩ := hzP
      have hd : dist p q = 1 := by rw [← hX.minDist_eq]; exact hzd
      have hT' := hT p q rfl
      have hg' := hg p q rfl
      rw [mem_image]
      refine ⟨q, ?_, rfl⟩
      have hl := lagrange (q - p) (F.u p)
      rw [F.norm_u' hp, ← dist_eq_norm, dist_comm q p, hd] at hl
      have hβ : beta = 1 / 100 := rfl
      have ha := hT'.2.1
      have ha0 := hT'.1
      rw [hβ] at ha
      rcases lt_or_gt_of_ne (show det2 (F.u p) (q - p) ≠ 0 by
        intro h0; rw [h0] at hl; nlinarith) with hb | hb
      · exact mem_union_right _ (mem_filter.2 ⟨hq, hp, hq, hd, hg', hT', by linarith⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hq, hp, hq, hd, hg', hT', by linarith⟩)
    have c1 : ((Sset X).filter (IsSideT F 1 p)).card ≤ 1 :=
      card_le_one.2 fun a ha b hb =>
        T1 hX F (Or.inl rfl) (mem_filter.1 ha).2 (mem_filter.1 hb).2
    have c2 : ((Sset X).filter (IsSideT F (-1) p)).card ≤ 1 :=
      card_le_one.2 fun a ha b hb =>
        T1 hX F (Or.inr rfl) (mem_filter.1 ha).2 (mem_filter.1 hb).2
    exact (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans (by omega)))

/-- `edges = good ⊔ bad`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_good_add_bad (F : DirField X) : (good X F).card + (bad X F).card = eS X := by
  rw [good, bad, card_filter_add_card_filter_not]; rfl

/-- For `τ > 2β`: `good ⊆ tEdges ∪ rungs`.

TODO: prove from the dichotomy.
Acceptance: no `sorry`.
Depends on: `good_dichotomy`. Difficulty S–M. -/
theorem good_subset_T_union_rungs (hX : Normal X) (F : DirField X) (hτ : 2 * beta < tau X) :
    good X F ⊆ tEdges X F ∪ rungs X F := by
  intro z hz
  obtain ⟨hze, hg⟩ := mem_filter.1 hz
  obtain ⟨hzP, hzd⟩ := mem_filter.1 hze
  induction z using Sym2.ind with
  | _ p q =>
  simp only [pairsS, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at hzP
  obtain ⟨⟨hp, hq⟩, -⟩ := hzP
  have hd : dist p q = 1 := by rw [← hX.minDist_eq]; exact hzd
  rcases good_dichotomy hX F hτ hp hq hd (hg p q rfl) with h | h | h
  · refine mem_union_left _ (mem_filter.2 ⟨hz, fun a b hab => ?_⟩)
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  · exact mem_union_right _ (mem_filter.2 ⟨hz, p, q, rfl, h⟩)
  · exact mem_union_right _ (mem_filter.2 ⟨hz, q, p, Sym2.eq_swap, h⟩)

/-! ## Turning measure -/

/-! ### Support-point uniqueness for all but countably many directions -/

theorem norm_dirVec (θ : ℝ) : ‖dirVec θ‖ = 1 := by
  have h := norm_sq_coord (dirVec θ)
  have h2 : (dirVec θ) 0 ^ 2 + (dirVec θ) 1 ^ 2 = 1 := by simp [dirVec]
  rw [h2] at h
  nlinarith [norm_nonneg (dirVec θ)]

theorem dirVec_injOn : Set.InjOn dirVec (Set.Ico 0 (2 * π)) := by
  intro θ hθ θ' hθ' h
  have hc : Real.cos θ = Real.cos θ' := by
    have := congrArg (fun v : Pt => v 0) h; simpa [dirVec] using this
  have hs : Real.sin θ = Real.sin θ' := by
    have := congrArg (fun v : Pt => v 1) h; simpa [dirVec] using this
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  obtain ⟨h3, h4⟩ := hθ'
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < k := by nlinarith
  have hk0 : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0] at hk; simp at hk; linarith

/-- Directions `θ ∈ [0, 2π)` whose support set in `K` has at least two points. -/
def exceptDirs (K : Set Pt) : Set ℝ :=
  {θ | θ ∈ Set.Ico 0 (2 * π) ∧ ∃ x ∈ K, ∃ y ∈ K, x ≠ y ∧ dirVec θ ∈ normalCone K x ∧
    dirVec θ ∈ normalCone K y}

/-- A direction with a non-trivial support face owns an open set of points `z` whose
nearest-point direction is `θ`; distinct directions own disjoint sets, hence countability. -/
theorem exceptDirs_countable {K : Set Pt} (hK : Convex ℝ K) : (exceptDirs K).Countable := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Pt
  have key : ∀ θ ∈ exceptDirs K, ∃ z ∈ D, ∃ q ∈ K, ∃ s : ℝ, 0 < s ∧ z - q = s • dirVec θ ∧
      dirVec θ ∈ normalCone K q := by
    rintro θ ⟨-, x, hx, y, hy, hxy, hnx, hny⟩
    have hd : ‖dirVec θ‖ = 1 := norm_dirVec θ
    have h0 : inner ℝ (y - x) (dirVec θ) = 0 := by
      have a := hnx y hy; have b := hny x hx; rw [inner_sub_swap] at b; linarith
    have hdec := decomp hd (y - x)
    rw [h0, zero_smul, zero_add, det2_eq_inner_perp] at hdec
    set d := dirVec θ
    set e := perp d
    set b := inner ℝ (y - x) e
    have hc : b ≠ 0 := by
      intro hc; apply hxy
      rw [hc, zero_smul] at hdec; exact (sub_eq_zero.1 hdec).symm
    have hde : inner ℝ d e = 0 := by rw [← det2_eq_inner_perp]; simp [det2]; ring
    have hdd : inner ℝ d d = 1 := by rw [real_inner_self_eq_norm_sq, hd]; norm_num
    let U : Set Pt := {z | 0 < inner ℝ (z - x) d ∧ 0 < inner ℝ (z - x) e / b ∧
      inner ℝ (z - x) e / b < 1}
    have hUo : IsOpen U := by
      have c1 : Continuous fun z : Pt => inner ℝ (z - x) d := by fun_prop
      have c2 : Continuous fun z : Pt => inner ℝ (z - x) e / b := by fun_prop
      exact (isOpen_lt continuous_const c1).inter
        ((isOpen_lt continuous_const c2).inter (isOpen_lt c2 continuous_const))
    have hUn : U.Nonempty := by
      refine ⟨x + (1 / 2 : ℝ) • (y - x) + d, ?_, ?_, ?_⟩ <;>
      · rw [show x + (1 / 2 : ℝ) • (y - x) + d - x = (1 / 2 : ℝ) • (y - x) + d by abel,
          inner_add_left, real_inner_smul_left]
        try rw [h0, hdd]
        try rw [hde, add_zero, mul_div_assoc, div_self hc]
        norm_num
    obtain ⟨z, hzD, hzU⟩ := hDd.exists_mem_open hUo hUn
    obtain ⟨ha, hl0, hl1⟩ := hzU
    set a := inner ℝ (z - x) d
    set c := inner ℝ (z - x) e
    have hz := decomp hd (z - x)
    rw [det2_eq_inner_perp] at hz
    refine ⟨z, hzD, x + (c / b) • (y - x), hK.add_smul_sub_mem hx hy ⟨hl0.le, hl1.le⟩, a, ha,
      ?_, ?_⟩
    · have : (c / b) • (y - x) = c • e := by
        rw [hdec, smul_smul, div_mul_cancel₀ c hc]
      rw [show z - (x + (c / b) • (y - x)) = (z - x) - (c / b) • (y - x) by abel, this, hz]
      abel
    · intro k hk
      rw [show k - (x + (c / b) • (y - x)) = (k - x) - (c / b) • (y - x) by abel,
        inner_sub_left, real_inner_smul_left, h0, mul_zero, sub_zero]
      exact hnx k hk
  choose! f hfD q hqK s hs hzs hqN using key
  refine Set.MapsTo.countable_of_injOn (f := f) (fun θ hθ => hfD θ hθ) ?_ hDc
  intro θ hθ θ' hθ' hff
  have e1 := hzs θ hθ
  have e2 := hzs θ' hθ'
  rw [hff] at e1
  have n1 := hqN θ hθ (q θ') (hqK θ' hθ')
  have n2 := hqN θ' hθ' (q θ) (hqK θ hθ)
  have hs1 := hs θ hθ
  have hs2 := hs θ' hθ'
  have A : inner ℝ (q θ' - q θ) (f θ' - q θ) ≤ 0 := by
    rw [e1, real_inner_smul_right]; nlinarith
  have B : inner ℝ (q θ - q θ') (f θ' - q θ') ≤ 0 := by
    rw [e2, real_inner_smul_right]; nlinarith
  have C : inner ℝ (q θ' - q θ) (f θ' - q θ) + inner ℝ (q θ - q θ') (f θ' - q θ') =
      ‖q θ' - q θ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, show q θ - q θ' = -(q θ' - q θ) by abel, inner_neg_left,
      ← sub_eq_add_neg, ← inner_sub_right]
    congr 1; abel
  have hqq : q θ' = q θ := by
    have : ‖q θ' - q θ‖ ^ 2 ≤ 0 := by linarith
    have : ‖q θ' - q θ‖ = 0 := by nlinarith [norm_nonneg (q θ' - q θ)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  rw [hqq] at e2
  have hsd : s θ • dirVec θ = s θ' • dirVec θ' := by rw [← e1, ← e2]
  have hss : s θ = s θ' := by
    have := congrArg norm hsd
    rwa [norm_smul, norm_smul, norm_dirVec, norm_dirVec, Real.norm_of_nonneg hs1.le,
      Real.norm_of_nonneg hs2.le, mul_one, mul_one] at this
  rw [hss] at hsd
  exact dirVec_injOn hθ.1 hθ'.1 (smul_right_injective Pt hs2.ne' hsd)

/-- The set of directions normal to a compact set of points is closed. -/
theorem isClosed_normalDirs {K γ : Set Pt} (hγ : IsCompact γ) :
    IsClosed {θ : ℝ | ∃ x ∈ γ, dirVec θ ∈ normalCone K x} := by
  have : CompactSpace γ := isCompact_iff_compactSpace.1 hγ
  have hS : IsClosed {p : ℝ × γ | dirVec p.1 ∈ normalCone K p.2} := by
    have : {p : ℝ × γ | dirVec p.1 ∈ normalCone K p.2} =
        ⋂ y ∈ K, {p : ℝ × γ | (y 0 - (p.2 : Pt) 0) * Real.cos p.1 +
          (y 1 - (p.2 : Pt) 1) * Real.sin p.1 ≤ 0} := by
      ext p; simp [normalCone, inner_coord, dirVec]
    rw [this]
    refine isClosed_biInter fun y _ => isClosed_le ?_ continuous_const
    fun_prop
  have := isClosedMap_fst_of_compactSpace _ hS
  convert this using 1
  ext θ; simp

/-- **Lemma 3.4 (multiplicity)**: if every boundary point lies in at most `M` of the *closed*
sets `γ_i ⊆ ∂K`, then `Σ turning(γ_i) ≤ 2πM`.

STATEMENT CHANGE (2026-09-23): added `hγc : ∀ i ∈ A, IsClosed (γ i)`.  Without it the lemma
is false: `turning` is an outer measure, and for `K` the unit disc and a Bernstein set
`B ⊆ [0, 2π)`, `γ₁ = dirVec '' B`, `γ₂ = dirVec '' Bᶜ` give `M = 1` but turnings `2π + 2π`.
The paper only uses closed arcs, and every downstream arc is `γ '' Icc a b` (compact).

Proved: off the countable set `exceptDirs K` (directions with a non-singleton support face,
`exceptDirs_countable`) the support point is unique; integrate the indicator sum. -/
theorem turning_sum_le {K : Set Pt} (hK : Convex ℝ K) (hKc : IsCompact K) {ι : Type*}
    (A : Finset ι) (γ : ι → Set Pt) (hγ : ∀ i ∈ A, γ i ⊆ frontier K)
    (hγc : ∀ i ∈ A, IsClosed (γ i)) (M : ℕ)
    (hM : ∀ x, (A.filter (fun i => x ∈ γ i)).card ≤ M) :
    ∑ i ∈ A, turning K (γ i) ≤ 2 * π * M := by
  classical
  set I : Set ℝ := Set.Ico 0 (2 * π)
  let C : ι → Set ℝ := fun i => {θ | θ ∈ I ∧ ∃ x ∈ γ i, dirVec θ ∈ normalCone K x}
  have hKcl : IsClosed K := hKc.isClosed
  have hγK : ∀ i ∈ A, γ i ⊆ K := fun i hi => (hγ i hi).trans hKcl.frontier_subset
  have hCm : ∀ i ∈ A, MeasurableSet (C i) := fun i hi =>
    measurableSet_Ico.inter
      (isClosed_normalDirs (hKc.of_isClosed_subset (hγc i hi) (hγK i hi))).measurableSet
  have hE : MeasureTheory.volume (exceptDirs K) = 0 :=
    (exceptDirs_countable hK).measure_zero _
  -- pointwise bound off the exceptional directions
  have hpt : ∀ᵐ θ ∂MeasureTheory.volume,
      ∑ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ ≤
        I.indicator (fun _ => (M : ENNReal)) θ := by
    refine MeasureTheory.measure_mono_null (fun θ hθ => ?_) hE
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hθ
    by_contra hθE
    by_cases hI : θ ∈ I
    · rw [Set.indicator_of_mem hI] at hθ
      simp only [Set.indicator_apply] at hθ
      rw [Finset.sum_boole] at hθ
      have hne : (A.filter (fun i => θ ∈ C i)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h0; rw [h0] at hθ; simp at hθ
      obtain ⟨i₀, hi₀⟩ := hne
      obtain ⟨hi₀A, -, x₀, hx₀, hn₀⟩ := Finset.mem_filter.1 hi₀
      have hsub : A.filter (fun i => θ ∈ C i) ⊆ A.filter (fun i => x₀ ∈ γ i) := by
        intro i hi
        obtain ⟨hiA, -, x, hx, hn⟩ := Finset.mem_filter.1 hi
        refine Finset.mem_filter.2 ⟨hiA, ?_⟩
        by_contra hx0
        have hne : x₀ ≠ x := fun h => hx0 (h ▸ hx)
        exact hθE ⟨hI, x₀, hγK i₀ hi₀A hx₀, x, hγK i hiA hx, hne, hn₀, hn⟩
      have := (Finset.card_le_card hsub).trans (hM x₀)
      have : ((A.filter (fun i => θ ∈ C i)).card : ENNReal) ≤ M := by exact_mod_cast this
      exact absurd hθ (not_lt.2 this)
    · rw [Set.indicator_of_notMem hI] at hθ
      have : ∀ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ = 0 := fun i _ =>
        Set.indicator_of_notMem (fun h => hI h.1) _
      rw [Finset.sum_eq_zero this] at hθ
      exact lt_irrefl _ hθ
  have hsum : ∑ i ∈ A, MeasureTheory.volume (C i) ≤ M * ENNReal.ofReal (2 * π) := by
    calc ∑ i ∈ A, MeasureTheory.volume (C i)
        = ∑ i ∈ A, ∫⁻ θ, (C i).indicator (fun _ => (1 : ENNReal)) θ := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [MeasureTheory.lintegral_indicator_const (hCm i hi), one_mul]
      _ = ∫⁻ θ, ∑ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ := by
          rw [MeasureTheory.lintegral_finsetSum]
          exact fun i hi => measurable_const.indicator (hCm i hi)
      _ ≤ ∫⁻ θ, I.indicator (fun _ => (M : ENNReal)) θ := MeasureTheory.lintegral_mono_ae hpt
      _ = M * ENNReal.ofReal (2 * π) := by
          rw [MeasureTheory.lintegral_indicator_const measurableSet_Ico, Real.volume_Ico,
            sub_zero]
  have hfin : ∀ i ∈ A, MeasureTheory.volume (C i) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono (fun θ h => h.1))
  have h1 : ∑ i ∈ A, turning K (γ i) = (∑ i ∈ A, MeasureTheory.volume (C i)).toReal := by
    rw [ENNReal.toReal_sum hfin]; rfl
  rw [h1]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
    ENNReal.ofReal_ne_top) hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at h2
  linarith

/-! ### Turning at a single point -/

theorem exists_dirVec {n : Pt} (hn : ‖n‖ = 1) : ∃ θ : ℝ, dirVec θ = n := by
  set z : ℂ := ⟨n 0, n 1⟩
  have hsq := norm_sq_coord n
  rw [hn] at hsq
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [z]
    rw [show n 0 * n 0 + n 1 * n 1 = 1 by nlinarith, Real.sqrt_one]
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  refine ⟨Complex.arg z, ?_⟩
  ext i; fin_cases i
  · simp [dirVec, Complex.cos_arg hz0, hz, z]
  · simp [dirVec, Complex.sin_arg, hz, z]

theorem dirVec_add (θ φ : ℝ) :
    dirVec (θ + φ) = Real.cos φ • dirVec θ + Real.sin φ • perp (dirVec θ) := by
  ext i; fin_cases i <;> simp [dirVec, perp, Real.cos_add, Real.sin_add] <;> ring

theorem dirVec_add_int_mul (θ : ℝ) (k : ℤ) : dirVec (θ + k * (2 * π)) = dirVec θ := by
  simp [dirVec, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem normalCone_add_smul {K : Set Pt} {x n₁ n₂ : Pt} (h₁ : n₁ ∈ normalCone K x)
    (h₂ : n₂ ∈ normalCone K x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • n₁ + b • n₂ ∈ normalCone K x := by
  intro y hy
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  nlinarith [h₁ y hy, h₂ y hy]

/-- If the directions `[c, c + α]` (`α ≤ 2π`) are all normal at a point of `γ`, the turning of
`γ` is at least `α`. -/
theorem le_turning_of_Icc {K γ : Set Pt} {x : Pt} (hx : x ∈ γ) {c α : ℝ} (hα : 0 ≤ α)
    (hα' : α ≤ 2 * π) (h : ∀ θ ∈ Set.Icc c (c + α), dirVec θ ∈ normalCone K x) :
    α ≤ turning K γ := by
  have hpi := Real.pi_pos
  set k : ℤ := ⌊c / (2 * π)⌋
  set c' := c - k * (2 * π)
  have hk1 : (k : ℝ) ≤ c / (2 * π) := Int.floor_le _
  have hk2 : c / (2 * π) < k + 1 := Int.lt_floor_add_one _
  have hc0 : 0 ≤ c' := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 hk1; simp only [c']; linarith
  have hc1 : c' < 2 * π := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 hk2; simp only [c']; linarith
  have h' : ∀ θ ∈ Set.Icc c' (c' + α), dirVec θ ∈ normalCone K x := by
    intro θ hθ
    rw [← dirVec_add_int_mul θ k]
    exact h _ ⟨by simp only [c'] at hθ; linarith [hθ.1], by simp only [c'] at hθ; linarith [hθ.2]⟩
  set T : Set ℝ := {θ | θ ∈ Set.Ico 0 (2 * π) ∧ ∃ x ∈ γ, dirVec θ ∈ normalCone K x}
  have hT1 : Set.Ico c' (min (c' + α) (2 * π)) ⊆ T := fun θ hθ =>
    ⟨⟨by linarith [hθ.1], lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩, x, hx,
      h' θ ⟨hθ.1, (lt_of_lt_of_le hθ.2 (min_le_left _ _)).le⟩⟩
  have hT2 : Set.Ico 0 (c' + α - 2 * π) ⊆ T := fun θ hθ => by
    refine ⟨⟨hθ.1, by linarith [hθ.2]⟩, x, hx, ?_⟩
    rw [← dirVec_add_int_mul θ 1]
    exact h' _ ⟨by push_cast; linarith [hθ.1], by push_cast; linarith [hθ.2]⟩
  have hdisj : Disjoint (Set.Ico c' (min (c' + α) (2 * π))) (Set.Ico 0 (c' + α - 2 * π)) := by
    rw [Set.disjoint_left]; intro θ h1 h2; linarith [h1.1, h2.2]
  have hvol : MeasureTheory.volume (Set.Ico c' (min (c' + α) (2 * π)) ∪
      Set.Ico 0 (c' + α - 2 * π)) = ENNReal.ofReal α := by
    rw [MeasureTheory.measure_union hdisj measurableSet_Ico, Real.volume_Ico, Real.volume_Ico]
    rcases le_or_gt (c' + α) (2 * π) with hle | hlt
    · rw [min_eq_left hle, sub_zero,
        ENNReal.ofReal_of_nonpos (show c' + α - 2 * π ≤ 0 by linarith), add_zero,
        add_sub_cancel_left]
    · rw [min_eq_right hlt.le, sub_zero, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
  have hTfin : MeasureTheory.volume T ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono (fun θ h => h.1))
  have hle := MeasureTheory.measure_mono (μ := MeasureTheory.volume) (Set.union_subset hT1 hT2)
  rw [hvol] at hle
  have := ENNReal.toReal_mono hTfin hle
  rwa [ENNReal.toReal_ofReal hα] at this

/-- Two unit normals at one point of `γ`, at angle `< π`: the turning of `γ` is at least
their angle. -/
theorem ang_le_turning_of_normals {K γ : Set Pt} {x n₁ n₂ : Pt} (hx : x ∈ γ)
    (h₁ : n₁ ∈ normalCone K x) (h₂ : n₂ ∈ normalCone K x) (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hlt : ang n₁ n₂ < π) : ang n₁ n₂ ≤ turning K γ := by
  set α := ang n₁ n₂
  have hα0 : 0 ≤ α := InnerProductGeometry.angle_nonneg _ _
  rcases hα0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact ENNReal.toReal_nonneg
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hcos : Real.cos α = inner ℝ n₁ n₂ := by
    have := InnerProductGeometry.cos_angle_mul_norm_mul_norm n₁ n₂
    rwa [hn₁, hn₂, mul_one, mul_one] at this
  obtain ⟨θ₁, hθ₁⟩ := exists_dirVec hn₁
  have hlag := lagrange n₂ n₁
  rw [hn₁, hn₂, real_inner_comm, ← hcos] at hlag
  have hdet2 : det2 n₁ n₂ ^ 2 = Real.sin α ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq α]
  have hdec := decomp hn₁ n₂
  rw [real_inner_comm, ← hcos] at hdec
  -- `det2 n₁ n₂ = σ sin α`
  obtain ⟨σ, hσ, hdσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ det2 n₁ n₂ = σ * Real.sin α := by
    rcases mul_self_eq_mul_self_iff.1 (show det2 n₁ n₂ * det2 n₁ n₂ = Real.sin α * Real.sin α by
      nlinarith) with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  have key : ∀ t ∈ Set.Icc 0 α, dirVec (θ₁ + σ * t) ∈ normalCone K x := by
    intro t ht
    have hdir : dirVec (θ₁ + σ * t) =
        (Real.sin α)⁻¹ • (Real.sin (α - t) • n₁ + Real.sin t • n₂) := by
      rw [dirVec_add, hθ₁, hdec, hdσ]
      have hc : Real.cos (σ * t) = Real.cos t := by
        rcases hσ with rfl | rfl <;> simp
      have hs : Real.sin (σ * t) = σ * Real.sin t := by
        rcases hσ with rfl | rfl <;> simp
      rw [hc, hs, Real.sin_sub, eq_inv_smul_iff₀ hsin.ne']
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hdir]
    obtain ⟨ht0, ht1⟩ := ht
    have s1 : 0 ≤ Real.sin (α - t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have s2 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
    have hn := normalCone_add_smul h₁ h₂ s1 s2
    intro y hy
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hsin.le) (hn y hy)
  rcases hσ with rfl | rfl
  · refine le_turning_of_Icc hx hα0 (by linarith [Real.pi_pos]) (c := θ₁) fun θ hθ => ?_
    have := key (θ - θ₁) ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    rwa [one_mul, add_sub_cancel] at this
  · refine le_turning_of_Icc hx hα0 (by linarith [Real.pi_pos]) (c := θ₁ - α) fun θ hθ => ?_
    have := key (θ₁ - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    rwa [neg_one_mul, neg_sub, add_sub_cancel] at this

/-- The turning of a connected boundary arc is at least the angle between (outward) normals at
its ends.

TODO: prove.
What's missing: normal-cone map is upper semicontinuous with arc values (nonempty interior),
so the union over a connected arc is a connected subset of `S¹` containing both normals.
Acceptance: no `sorry`.
Depends on: normal-cone topology. Difficulty L. -/
theorem turning_ge_angle {K : Set Pt} (hK : Convex ℝ K) (hKc : IsCompact K)
    (hint : (interior K).Nonempty) {γ : ℝ → Pt} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hsub : γ '' Set.Icc a b ⊆ frontier K) {ν₁ ν₂ : Pt}
    (h₁ : ν₁ ∈ normalCone K (γ a)) (h₂ : ν₂ ∈ normalCone K (γ b)) (hn₁ : ν₁ ≠ 0)
    (hn₂ : ν₂ ≠ 0) : ang ν₁ ν₂ ≤ turning K (γ '' Set.Icc a b) := by
  sorry

/-- `1`-separated reals in `[a, b]` number at most `b − a + 1`. -/
theorem card_le_of_sep_real {a : ℝ} (T : Finset ℝ) : ∀ b : ℝ, a ≤ b + 1 →
    (∀ x ∈ T, a ≤ x ∧ x ≤ b) → (∀ x ∈ T, ∀ y ∈ T, x ≠ y → 1 ≤ |x - y|) →
    (T.card : ℝ) ≤ b - a + 1 := by
  induction T using Finset.induction_on_max with
  | empty => intro b hb _ _; simp; linarith
  | insert m T hlt ih =>
    intro b hb hmem hsep
    have hmT : m ∉ T := fun h => lt_irrefl _ (hlt m h)
    have hm := hmem m (mem_insert_self _ _)
    have hT : ∀ x ∈ T, a ≤ x ∧ x ≤ m - 1 := by
      intro x hx
      refine ⟨(hmem x (mem_insert_of_mem hx)).1, ?_⟩
      have := hsep x (mem_insert_of_mem hx) m (mem_insert_self _ _) (hlt x hx).ne
      rw [abs_of_neg (by linarith [hlt x hx])] at this; linarith
    have h1 := ih (m - 1) (by linarith [hm.1]) hT
      (fun x hx y hy hxy => hsep x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy)
    rw [card_insert_of_notMem hmT]; push_cast; linarith [hm.2]

/-- **Arc spacing**: `1`-separated points on a `1`-Lipschitz arc of length `ℓ` number `≤ ℓ + 1`.

TODO: prove (pull back to parameters, which are pairwise `≥ 1` apart in `[a, b]`).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty M. -/
theorem card_le_arcLength {P : Finset Pt} (hP : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ dist x y)
    {γ : ℝ → Pt} (hγ : LipschitzWith 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hsub : ∀ x ∈ P, x ∈ γ '' Set.Icc a b) : (P.card : ℝ) ≤ b - a + 1 := by
  have hch : ∀ x ∈ P, ∃ s ∈ Set.Icc a b, γ s = x := fun x hx => hsub x hx
  choose! t ht htγ using hch
  have hinj : Set.InjOn t P := fun x hx y hy h => by rw [← htγ x hx, ← htγ y hy, h]
  rw [← card_image_of_injOn hinj]
  refine card_le_of_sep_real _ b (by linarith) ?_ ?_
  · intro s hs; obtain ⟨x, hx, rfl⟩ := mem_image.1 hs; exact ht x hx
  · intro s hs s' hs' hne
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hs
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hs'
    have hxy : x ≠ y := fun h => hne (h ▸ rfl)
    have h1 := hP x hx y hy hxy
    have hl := hγ.dist_le_mul (t x) (t y)
    rw [htγ x hx, htγ y hy] at hl
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hl
    linarith

/-! ## §5.1 Lens lemma -/

/-- Half-angle of a lens: `cos φ₀ = d/(2R)`. -/
def phi0 (d R : ℝ) : ℝ := Real.arccos (d / (2 * R))

/-- Corner radius `ρ₀ = 1/sin(φ₀/2)`. -/
def rho0 (d R : ℝ) : ℝ := 1 / Real.sin (phi0 d R / 2)

/-- Real-variable core of Lemma 5.1 (steps 1–2). -/
theorem lens_real {φ₀ a R : ℝ} (hφ : 0 < φ₀) (hφ' : φ₀ < π / 2) (ha : 0 ≤ a) (ha' : a ≤ φ₀)
    (hR : 0 < R) (h1 : R * (Real.cos a - Real.cos φ₀) ≤ 1)
    (h2 : 2 ≤ R * (Real.cos (φ₀ / 2) - Real.cos φ₀)) :
    φ₀ / 2 < a ∧ R * (φ₀ - a) ≤ 1 / Real.sin (φ₀ / 2) := by
  have hpi := Real.pi_pos
  have hlt : φ₀ / 2 < a := by
    by_contra h
    push Not at h
    have := Real.cos_le_cos_of_nonneg_of_le_pi ha (by linarith) h
    nlinarith
  refine ⟨hlt, ?_⟩
  have hs2 : 0 < Real.sin (φ₀ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set y := (φ₀ - a) / 2 with hy
  set x := (a + φ₀) / 2 with hx
  have hy0 : 0 ≤ y := by linarith
  have hyπ : y < π / 2 := by linarith
  have hcosy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith, hyπ⟩
  have htan := Real.le_tan hy0 hyπ
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcosy] at htan
  have hsx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hdiff : Real.cos a - Real.cos φ₀ = 2 * Real.sin x * Real.sin y := by
    rw [Real.cos_sub_cos, show (a - φ₀) / 2 = -y by rw [hy]; ring, Real.sin_neg]; ring
  have hprod : 2 * Real.sin x * Real.cos y = Real.sin a + Real.sin φ₀ := by
    rw [Real.two_mul_sin_mul_cos, show x - y = a by rw [hx, hy]; ring,
      show x + y = φ₀ by rw [hx, hy]; ring]
  have hsa : Real.sin (φ₀ / 2) ≤ Real.sin a :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hlt.le
  have hsφ : Real.sin (φ₀ / 2) ≤ Real.sin φ₀ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have key : Real.sin (φ₀ / 2) * (φ₀ - a) ≤ Real.cos a - Real.cos φ₀ := by
    rw [hdiff]
    have h3 : 2 * Real.sin x * (y * Real.cos y) ≤ 2 * Real.sin x * Real.sin y :=
      mul_le_mul_of_nonneg_left htan (by positivity)
    have e : 2 * Real.sin x * (y * Real.cos y) = y * (Real.sin a + Real.sin φ₀) := by
      rw [← hprod]; ring
    have e2 : φ₀ - a = 2 * y := by rw [hy]; ring
    rw [e2]
    nlinarith
  rw [le_div_iff₀ hs2]
  nlinarith

/-- Inner product in an orthonormal frame `(e, e^⊥)`. -/
theorem inner_frame {e : Pt} (he : ‖e‖ = 1) (w₁ w₂ : Pt) :
    inner ℝ w₁ w₂ = inner ℝ w₁ e * inner ℝ w₂ e + det2 e w₁ * det2 e w₂ := by
  have h := norm_sq_coord e
  rw [he] at h
  rw [inner_coord, inner_coord, inner_coord]
  simp only [det2]
  linear_combination (w₁ 0 * w₂ 0 + w₁ 1 * w₂ 1) * h

theorem norm_sq_frame {e : Pt} (he : ‖e‖ = 1) (w : Pt) :
    ‖w‖ ^ 2 = inner ℝ w e ^ 2 + det2 e w ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_frame he]; ring

/-- Angle from the cosine in a frame. -/
theorem ang_eq_of_inner {w₁ w₂ : Pt} {R θ : ℝ} (hR : 0 < R) (h₁ : ‖w₁‖ = R) (h₂ : ‖w₂‖ = R)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ π) (h : inner ℝ w₁ w₂ = R ^ 2 * Real.cos θ) : ang w₁ w₂ = θ := by
  rw [ang, InnerProductGeometry.angle, h₁, h₂, h, show R ^ 2 * Real.cos θ / (R * R) = Real.cos θ by
    field_simp, Real.arccos_cos hθ hθ']

/-- Lemma 5.1 in the coordinates of the frame `(e, e^⊥)`, `e = (c₂ − c₁)/d`:
`p − c₁ = (xp, yp)`, `q − c₂ = (xq, yq)`. -/
theorem lens_coord {R d xp yp xq yq : ℝ} (hd0 : 0 < d) (hd : d < 2 * R)
    (hR : 2 / (Real.cos (phi0 d R / 2) - Real.cos (phi0 d R)) ≤ R)
    (Ep : xp ^ 2 + yp ^ 2 = R ^ 2) (Eq : xq ^ 2 + yq ^ 2 = R ^ 2)
    (Ep₂ : (xp - d) ^ 2 + yp ^ 2 ≤ R ^ 2) (Eq₁ : (xq + d) ^ 2 + yq ^ 2 ≤ R ^ 2)
    (Epq : (xp - xq - d) ^ 2 + (yp - yq) ^ 2 ≤ 1) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      R * Real.arccos ((xp * (d / 2) + yp * (σ * R * Real.sin (phi0 d R))) / (R * R)) ≤
        rho0 d R ∧
      R * Real.arccos ((xq * (-(d / 2)) + yq * (σ * R * Real.sin (phi0 d R))) / (R * R)) ≤
        rho0 d R := by
  have hpi := Real.pi_pos
  have hR0 : 0 < R := by linarith
  set C := d / (2 * R) with hC_def
  have hC0 : 0 < C := by positivity
  have hC1 : C < 1 := by rw [div_lt_one (by positivity)]; exact hd
  have hdC : d = 2 * R * C := by rw [hC_def]; field_simp
  set φ₀ := phi0 d R with hφ_def
  have hφC : Real.cos φ₀ = C := Real.cos_arccos (by linarith) hC1.le
  have hφ0 : 0 < φ₀ := Real.arccos_pos.2 hC1
  have hφ1 : φ₀ < π / 2 := Real.arccos_lt_pi_div_two.2 hC0
  set S := Real.sin φ₀ with hS_def
  have hgpos : 0 < Real.cos (φ₀ / 2) - Real.cos φ₀ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith)
      (by linarith : φ₀ / 2 < φ₀)
    linarith
  have hg : 2 ≤ R * (Real.cos (φ₀ / 2) - Real.cos φ₀) := by
    rw [div_le_iff₀ hgpos] at hR; linarith
  have hs2 : 0 < Real.sin (φ₀ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hhalf : 1 - Real.cos φ₀ = 2 * Real.sin (φ₀ / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (φ₀ / 2)
    rw [show 2 * (φ₀ / 2) = φ₀ by ring] at h1
    have h2 := Real.sin_sq_add_cos_sq (φ₀ / 2)
    linarith
  have hc2 : Real.cos (φ₀ / 2) ≤ 1 := Real.cos_le_one _
  have hRs : 1 ≤ R * Real.sin (φ₀ / 2) ^ 2 := by
    have : R * (Real.cos (φ₀ / 2) - Real.cos φ₀) ≤ R * (1 - Real.cos φ₀) :=
      mul_le_mul_of_nonneg_left (by linarith) hR0.le
    rw [hhalf] at this; linarith
  have hs21 : Real.sin (φ₀ / 2) ^ 2 ≤ 1 := by
    have := Real.sin_sq_add_cos_sq (φ₀ / 2); nlinarith [sq_nonneg (Real.cos (φ₀ / 2))]
  have hR1 : 1 ≤ R := by
    have := mul_le_mul_of_nonneg_left hs21 hR0.le; linarith
  -- abscissae
  have hxp : d / 2 ≤ xp := by
    have h : d * d ≤ d * (2 * xp) := by nlinarith
    have := le_of_mul_le_mul_left h hd0; linarith
  have hxq : d / 2 ≤ -xq := by
    have h : d * d ≤ d * (-2 * xq) := by nlinarith
    have := le_of_mul_le_mul_left h hd0; linarith
  have hxp1 : xp ≤ R := by
    have : xp ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg yp]
    exact abs_le_of_sq_le_sq' this hR0.le |>.2
  have hxq1 : -xq ≤ R := by
    have : (-xq) ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg yq]
    exact abs_le_of_sq_le_sq' this hR0.le |>.2
  have hsum : xp - xq - d ≤ 1 := by
    have : (xp - xq - d) ^ 2 ≤ 1 := by linarith [sq_nonneg (yp - yq)]
    have := abs_le_of_sq_le_sq' (show (xp - xq - d) ^ 2 ≤ 1 ^ 2 by rw [one_pow]; exact this)
      zero_le_one
    linarith [this.2]
  set a := Real.arccos (xp / R) with ha_def
  set b := Real.arccos (-xq / R) with hb_def
  have hxpR : C ≤ xp / R := by rw [le_div_iff₀ hR0]; rw [hdC] at hxp; linarith
  have hxqR : C ≤ -xq / R := by rw [le_div_iff₀ hR0]; rw [hdC] at hxq; linarith
  have hxpR1 : xp / R ≤ 1 := by rw [div_le_one hR0]; exact hxp1
  have hxqR1 : -xq / R ≤ 1 := by rw [div_le_one hR0]; exact hxq1
  have hca : Real.cos a = xp / R := Real.cos_arccos (by linarith) hxpR1
  have hcb : Real.cos b = -xq / R := Real.cos_arccos (by linarith) hxqR1
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hb0 : 0 ≤ b := Real.arccos_nonneg _
  have haφ : a ≤ φ₀ := Real.arccos_le_arccos hxpR
  have hbφ : b ≤ φ₀ := Real.arccos_le_arccos hxqR
  have h1a : R * (Real.cos a - Real.cos φ₀) ≤ 1 := by
    have e1 : R * (xp / R - C) = xp - R * C := by field_simp
    rw [hca, hφC, e1]; rw [hdC] at hsum hxq; linarith
  have h1b : R * (Real.cos b - Real.cos φ₀) ≤ 1 := by
    have e1 : R * (-xq / R - C) = -xq - R * C := by field_simp
    rw [hcb, hφC, e1]; rw [hdC] at hsum hxp; linarith
  obtain ⟨hla, hRa⟩ := lens_real hφ0 hφ1 ha0 haφ hR0 h1a hg
  obtain ⟨hlb, hRb⟩ := lens_real hφ0 hφ1 hb0 hbφ hR0 h1b hg
  have hsa : Real.sin (φ₀ / 2) ≤ Real.sin a :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hla.le
  have hsb : Real.sin (φ₀ / 2) ≤ Real.sin b :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hlb.le
  have hsa0 : 0 ≤ Real.sin a := by linarith
  have hsb0 : 0 ≤ Real.sin b := by linarith
  have hyp2 : yp ^ 2 = (R * Real.sin a) ^ 2 := by
    rw [mul_pow, Real.sin_sq, hca]; field_simp; linarith
  have hyq2 : yq ^ 2 = (R * Real.sin b) ^ 2 := by
    rw [mul_pow, Real.sin_sq, hcb]; field_simp; linarith
  have habs_p : |yp| = R * Real.sin a := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ R * Real.sin a)]
    exact (sq_eq_sq_iff_abs_eq_abs _ _).1 hyp2
  have habs_q : |yq| = R * Real.sin b := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ R * Real.sin b)]
    exact (sq_eq_sq_iff_abs_eq_abs _ _).1 hyq2
  have e3 : 1 ≤ (R * Real.sin (φ₀ / 2)) ^ 2 := by
    rw [mul_pow, sq R, mul_assoc]; exact one_le_mul_of_one_le_of_one_le hR1 hRs
  have e1 : (R * Real.sin (φ₀ / 2)) ^ 2 ≤ yp ^ 2 := by
    rw [hyp2]; exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsa hR0.le) 2
  have e2 : (R * Real.sin (φ₀ / 2)) ^ 2 ≤ yq ^ 2 := by
    rw [hyq2]; exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsb hR0.le) 2
  have hsame : 0 < yp * yq := by
    by_contra hneg
    push Not at hneg
    have ex : (yp - yq) ^ 2 = yp ^ 2 + yq ^ 2 - 2 * (yp * yq) := by ring
    have : (yp - yq) ^ 2 ≤ 1 := by linarith [sq_nonneg (xp - xq - d)]
    linarith
  obtain ⟨σ, hσ, hσp, hσq⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * yp = |yp| ∧ σ * yq = |yq| := by
    have hyp0 : yp ≠ 0 := by rintro h; rw [h, zero_mul] at hsame; exact lt_irrefl _ hsame
    rcases lt_or_gt_of_ne hyp0 with h | h
    · have h' : yq < 0 := by
        by_contra h''; push Not at h''
        exact absurd hsame (not_lt.2 (mul_nonpos_iff.2 (Or.inr ⟨h.le, h''⟩)))
      exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring, by rw [abs_of_neg h']; ring⟩
    · have h' : 0 < yq := by
        by_contra h''; push Not at h''
        exact absurd hsame (not_lt.2 (mul_nonpos_iff.2 (Or.inl ⟨h.le, h''⟩)))
      exact ⟨1, Or.inl rfl, by rw [abs_of_pos h]; ring, by rw [abs_of_pos h']; ring⟩
  refine ⟨σ, hσ, ?_, ?_⟩
  · have hcos : (xp * (d / 2) + yp * (σ * R * S)) / (R * R) = Real.cos (φ₀ - a) := by
      rw [Real.cos_sub, hφC, hca, ← hS_def,
        show yp * (σ * R * S) = R * S * (σ * yp) by ring, hσp, habs_p, hdC]
      field_simp
    rw [hcos, Real.arccos_cos (by linarith) (by linarith)]; exact hRa
  · have hcos : (xq * (-(d / 2)) + yq * (σ * R * S)) / (R * R) = Real.cos (φ₀ - b) := by
      rw [Real.cos_sub, hφC, hcb, ← hS_def,
        show yq * (σ * R * S) = R * S * (σ * yq) by ring, hσq, habs_q, hdC]
      field_simp
    rw [hcos, Real.arccos_cos (by linarith) (by linarith)]; exact hRb

/-- **Lemma 5.1 (lens lemma)**: `p` on the `C(c₁, R)`-arc, `q` on the `C(c₂, R)`-arc of the lens
`D(c₁,R) ∩ D(c₂,R)`, `|pq| ≤ 1`, and `R ≥ 2/(cos(φ₀/2) − cos φ₀)` ⇒ a common corner `c` within
circular arc length `ρ₀` of both.

TODO: prove.
What's missing: coordinates `c₁,₂ = (∓d/2, 0)`; (1) `|φ|, |ψ| > φ₀/2`; (2) MVT for `cos`,
`R(φ₀ − |φ|) ≤ ρ₀`; (3) same-sign argument using `R ≥ 1/sin²(φ₀/2)`.
Acceptance: no `sorry`.
Depends on: real trig. Difficulty L. -/
theorem lens_corner {c₁ c₂ p q : Pt} {R : ℝ} (hd0 : 0 < dist c₁ c₂) (hd : dist c₁ c₂ < 2 * R)
    (hR : 2 / (Real.cos (phi0 (dist c₁ c₂) R / 2) - Real.cos (phi0 (dist c₁ c₂) R)) ≤ R)
    (hp : dist p c₁ = R) (hp₂ : dist p c₂ ≤ R) (hq : dist q c₂ = R) (hq₁ : dist q c₁ ≤ R)
    (hpq : dist p q ≤ 1) :
    ∃ c : Pt, dist c c₁ = R ∧ dist c c₂ = R ∧
      R * ang (p - c₁) (c - c₁) ≤ rho0 (dist c₁ c₂) R ∧
      R * ang (q - c₂) (c - c₂) ≤ rho0 (dist c₁ c₂) R := by
  set d := dist c₁ c₂ with hd_def
  have hR0 : 0 < R := by linarith
  have hd0' : d ≠ 0 := hd0.ne'
  set e : Pt := d⁻¹ • (c₂ - c₁) with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd0, ← dist_eq_norm,
      dist_comm, inv_mul_cancel₀ hd0']
  have hce : c₂ - c₁ = d • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hd0', one_smul]
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hpe : inner ℝ (perp e) e = 0 := by rw [inner_coord]; simp [perp]; ring
  have hdet_ee : det2 e e = 0 := by simp only [det2]; ring
  have hdet_pe : det2 e (perp e) = 1 := by
    have h := norm_sq_coord e; rw [he] at h; simp only [det2, perp]; simp; linarith
  have lin_i : ∀ (w : Pt) (t : ℝ), inner ℝ (w + t • e) e = inner ℝ w e + t := by
    intro w t; rw [inner_add_left, real_inner_smul_left, hee, mul_one]
  have lin_d : ∀ (w : Pt) (t : ℝ), det2 e (w + t • e) = det2 e w := by
    intro w t; simp only [det2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have det_lin : ∀ (a b : ℝ), det2 e (a • e + b • perp e) = b := by
    intro a b
    have : det2 e (a • e + b • perp e) = a * det2 e e + b * det2 e (perp e) := by
      simp only [det2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this, hdet_ee, hdet_pe]; ring
  set xp := inner ℝ (p - c₁) e
  set yp := det2 e (p - c₁)
  set xq := inner ℝ (q - c₂) e
  set yq := det2 e (q - c₂)
  have Ep : xp ^ 2 + yp ^ 2 = R ^ 2 := by rw [← norm_sq_frame he, ← dist_eq_norm, hp]
  have Eq : xq ^ 2 + yq ^ 2 = R ^ 2 := by rw [← norm_sq_frame he, ← dist_eq_norm, hq]
  have Ep₂ : (xp - d) ^ 2 + yp ^ 2 ≤ R ^ 2 := by
    have h := norm_sq_frame he (p - c₂)
    have e' : p - c₂ = (p - c₁) + (-d) • e := by rw [neg_smul, ← hce]; abel
    have hi : inner ℝ (p - c₂) e = xp - d := by rw [e', lin_i]; ring
    have ht : det2 e (p - c₂) = yp := by rw [e', lin_d]
    rw [hi, ht] at h
    rw [← h, ← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hp₂ 2
  have Eq₁ : (xq + d) ^ 2 + yq ^ 2 ≤ R ^ 2 := by
    have h := norm_sq_frame he (q - c₁)
    have e' : q - c₁ = (q - c₂) + d • e := by rw [← hce]; abel
    have hi : inner ℝ (q - c₁) e = xq + d := by rw [e', lin_i]
    have ht : det2 e (q - c₁) = yq := by rw [e', lin_d]
    rw [hi, ht] at h
    rw [← h, ← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hq₁ 2
  have Epq : (xp - xq - d) ^ 2 + (yp - yq) ^ 2 ≤ 1 := by
    have h := norm_sq_frame he (p - q)
    have e' : p - q = ((p - c₁) - (q - c₂)) + (-d) • e := by rw [neg_smul, ← hce]; abel
    have hi : inner ℝ (p - q) e = xp - xq - d := by rw [e', lin_i, inner_sub_left]; ring
    have ht : det2 e (p - q) = yp - yq := by rw [e', lin_d, det2_sub_right]
    rw [hi, ht] at h
    rw [← h, ← dist_eq_norm]; exact pow_le_one₀ dist_nonneg hpq
  obtain ⟨σ, hσ, h1, h2⟩ := lens_coord hd0 hd hR Ep Eq Ep₂ Eq₁ Epq
  set S := Real.sin (phi0 d R) with hS_def
  have hC1 : d / (2 * R) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hS : S ^ 2 = 1 - (d / (2 * R)) ^ 2 := by
    rw [hS_def, Real.sin_sq, phi0, Real.cos_arccos (by
      have : 0 ≤ d / (2 * R) := by positivity
      linarith) hC1]
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set c := c₁ + (d / 2) • e + (σ * R * S) • perp e with hc_def
  have hcc₁ : c - c₁ = (d / 2) • e + (σ * R * S) • perp e := by rw [hc_def]; abel
  have hcc₂ : c - c₂ = ((d / 2) • e + (σ * R * S) • perp e) + (-d) • e := by
    rw [neg_smul, ← hce, hc_def]; abel
  have ic₁ : inner ℝ (c - c₁) e = d / 2 := by
    rw [hcc₁, inner_add_left, real_inner_smul_left e e (d / 2),
      real_inner_smul_left (perp e) e (σ * R * S), hee, hpe]; ring
  have dc₁ : det2 e (c - c₁) = σ * R * S := by rw [hcc₁, det_lin]
  have ic₂ : inner ℝ (c - c₂) e = -(d / 2) := by rw [hcc₂, lin_i, ← hcc₁, ic₁]; ring
  have dc₂ : det2 e (c - c₂) = σ * R * S := by rw [hcc₂, lin_d, ← hcc₁, dc₁]
  have hsq : (d / 2) ^ 2 + (σ * R * S) ^ 2 = R ^ 2 := by
    rw [mul_pow, mul_pow, hσ2, hS]; field_simp; ring
  have hnc₁ : ‖c - c₁‖ = R := by
    have h := norm_sq_frame he (c - c₁)
    rw [ic₁, dc₁, hsq] at h
    exact (pow_left_inj₀ (norm_nonneg _) hR0.le two_ne_zero).1 h
  have hnc₂ : ‖c - c₂‖ = R := by
    have h := norm_sq_frame he (c - c₂)
    rw [ic₂, dc₂, neg_sq, hsq] at h
    exact (pow_left_inj₀ (norm_nonneg _) hR0.le two_ne_zero).1 h
  refine ⟨c, by rw [dist_eq_norm]; exact hnc₁, by rw [dist_eq_norm]; exact hnc₂, ?_, ?_⟩
  · have : ang (p - c₁) (c - c₁) =
        Real.arccos ((xp * (d / 2) + yp * (σ * R * S)) / (R * R)) := by
      rw [ang, InnerProductGeometry.angle, hnc₁, ← dist_eq_norm, hp, inner_frame he, ic₁, dc₁]
    rw [this]; exact h1
  · have : ang (q - c₂) (c - c₂) =
        Real.arccos ((xq * (-(d / 2)) + yq * (σ * R * S)) / (R * R)) := by
      rw [ang, InnerProductGeometry.angle, hnc₂, ← dist_eq_norm, hq, inner_frame he, ic₂, dc₂]
    rw [this]; exact h2

/-- **Lemma 5.2 (lens-corner arc length)**: for compact convex `K' ⊆` lens, `p, q ∈ ∂K'` as in
5.1 with `|pq| = 1`, the boundary arc of `K'` from `p` to `q` on the corner's side has length
`≤ 2ρ₀`.

TODO: prove.
What's missing: perimeter monotonicity for nested convex sets (not in Mathlib), applied to
`K' ∩ H ⊆ Λ ∩ H`; parametrisation of `∂K'` by arc length.
Acceptance: no `sorry`.
Depends on: `lens_corner`; convex perimeter monotonicity. Difficulty XL. -/
theorem lens_arc_length {c₁ c₂ p q : Pt} {R : ℝ} {K' : Set Pt} (hK' : Convex ℝ K')
    (hKc : IsCompact K') (hsub : K' ⊆ Metric.closedBall c₁ R ∩ Metric.closedBall c₂ R)
    (hd0 : 0 < dist c₁ c₂) (hd : dist c₁ c₂ < 2 * R)
    (hR : 2 / (Real.cos (phi0 (dist c₁ c₂) R / 2) - Real.cos (phi0 (dist c₁ c₂) R)) ≤ R)
    (hp : dist p c₁ = R) (hq : dist q c₂ = R) (hpK : p ∈ frontier K') (hqK : q ∈ frontier K')
    (hpq : dist p q = 1) :
    ∃ γ : ℝ → Pt, ∃ ℓ : ℝ, 0 ≤ ℓ ∧ ℓ ≤ 2 * rho0 (dist c₁ c₂) R ∧ LipschitzWith 1 γ ∧
      γ 0 = p ∧ γ ℓ = q ∧ γ '' Set.Icc 0 ℓ ⊆ frontier K' := by
  sorry

/-- **[C7]** KK lens constants: `2/(1 − 0.97) < 8.2²`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c7_kk : (2 : ℝ) / (1 - 0.97) < 8.2 ^ 2 := by
  norm_num

/-- **[C3]** `2/Δ₂ ≤ β/2` for `Δ₂ ≥ 10⁴`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c3 {Δ₂ : ℝ} (h : 10 ^ 4 ≤ Δ₂) : 2 / Δ₂ ≤ beta / 2 := by
  have hpos : (0 : ℝ) < Δ₂ := by linarith
  rw [div_le_iff₀ hpos, beta]; linarith

/-! ## §5.2 Bad-edge counts -/

/-- Bad edges with both ends in `S ∖ D`. -/
def badKK (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun z => ∀ p ∈ z, p ∉ Dset X)

/-- Bad edges with both ends in `S ∩ D`. -/
def badDD (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun z => ∀ p ∈ z, p ∈ Dset X)

/-- Bad cross edges `zv` (`z ∈ D`, `v ∉ D`) with `|z w_v| = Δ` — case (c1). -/
def badC1 (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun e => ∃ v z, e = s(v, z) ∧ v ∉ Dset X ∧ z ∈ Dset X ∧
    dist z (F.partner v) = diam X)

/-- Bad cross edges with `|z w_v| ≠ Δ` (hence `≤ Δ₂`) — case (c2). -/
def badC2 (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun e => ∃ v z, e = s(v, z) ∧ v ∉ Dset X ∧ z ∈ Dset X ∧
    dist z (F.partner v) ≠ diam X)

/-- Every bad edge is KK, DD, (c1) or (c2).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem bad_subset (F : DirField X) :
    bad X F ⊆ badKK X F ∪ badDD X F ∪ badC1 X F ∪ badC2 X F := by
  intro e he
  simp only [mem_union, badKK, badDD, badC1, badC2, mem_filter]
  induction e using Sym2.ind with
  | _ a b =>
  by_cases ha : a ∈ Dset X <;> by_cases hb : b ∈ Dset X
  · exact Or.inl (Or.inl (Or.inr ⟨he, by simp [ha, hb]⟩))
  · by_cases hc : dist a (F.partner b) = diam X
    · exact Or.inl (Or.inr ⟨he, b, a, Sym2.eq_swap, hb, ha, hc⟩)
    · exact Or.inr ⟨he, b, a, Sym2.eq_swap, hb, ha, hc⟩
  · by_cases hc : dist b (F.partner a) = diam X
    · exact Or.inl (Or.inr ⟨he, a, b, rfl, ha, hb, hc⟩)
    · exact Or.inr ⟨he, a, b, rfl, ha, hb, hc⟩
  · exact Or.inl (Or.inl (Or.inl ⟨he, by simp [ha, hb]⟩))

/-- **[C9]** numeric constants of §5: KK `12π(4·8.2+1)/β < 1.28·10⁵`, DD `12π·9/β < 3.4·10⁴`,
(c1) `24π/β < 7600`, (c2) `48π(2·600+1)/β < 1.82·10⁷`, and the total `< cBad`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c9 :
    12 * π * (4 * 8.2 + 1) / beta < 128000 ∧ 12 * π * 9 / beta < 34000 ∧
      24 * π / beta < 7600 ∧ 48 * π * (2 * 600 + 1) / beta < 18200000 ∧
      (128000 + 34000 + 7600 + 18200000 : ℝ) ≤ cBad := by
  have hp := Real.pi_lt_d4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [beta, cBad] <;> linarith

/-- **KK bound** `#KK-bad < 1.28·10⁵`.

TODO: prove.
What's missing: `w_p = w_q` ⇒ good ([C3]); else lens `Λ(w_p, w_q) ⊇ K`, Lemmas 5.1/5.2 give an
arc `γ_pq ⊆ ∂K` of length `≤ 2ρ₀` with turning `> β` (`turning_ge_angle`); multiplicity
`M ≤ 6(4ρ₀ + 1)` (`card_le_arcLength`, kissing); Lemma 3.4.  Small-perimeter case separately.
Acceptance: no `sorry`.
Depends on: `lens_corner`, `lens_arc_length`, `turning_ge_angle`, `turning_sum_le`,
`card_le_arcLength`, `card_partners_minDist_le`, `c3`, `c7_kk`, `c9`. Difficulty XL. -/
theorem card_badKK_le (hX : Normal X) (F : DirField X) : ((badKK X F).card : ℝ) ≤ 128000 := by
  sorry

/-- **DD bound** `#DD-bad < 3.4·10⁴` (same argument on `∂P₁`, lens radius `Δ`, `ρ₀ ≤ 2`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: as `card_badKK_le`, with `convexHull ℝ X` in place of `K`. Difficulty XL
(shares the machinery with KK: L once KK is done). -/
theorem card_badDD_le (hX : Normal X) (F : DirField X) : ((badDD X F).card : ℝ) ≤ 34000 := by
  sorry

/-! ### Helpers for (c1) -/

/-- A direction that is outward-normal at `z` for every point of `S` is normal to `conv S`. -/
theorem mem_normalCone_convexHull {S : Set Pt} {z n : Pt}
    (h : ∀ y ∈ S, inner ℝ (y - z) n ≤ 0) : n ∈ normalCone (convexHull ℝ S) z := by
  have hH : Convex ℝ {y : Pt | inner ℝ (y - z) n ≤ 0} := by
    intro a ha b hb s t hs ht hst
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    obtain rfl : t = 1 - s := by linarith
    have e : s • a + (1 - s) • b - z = s • (a - z) + (1 - s) • (b - z) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    nlinarith
  intro y hy
  exact convexHull_min (fun y hy => h y hy) hH hy

/-- A point of `K` with a non-zero outward normal is a boundary point. -/
theorem mem_frontier_of_normal {K : Set Pt} {z n : Pt} (hz : z ∈ K) (hn : n ≠ 0)
    (h : n ∈ normalCone K z) : z ∈ frontier K := by
  refine ⟨subset_closure hz, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn
  have hyz : (z + (ε / 2 / ‖n‖) • n) - z = (ε / 2 / ‖n‖) • n := by abel
  have hy : z + (ε / 2 / ‖n‖) • n ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hyz, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ hnpos.ne']
    linarith
  have := h _ hy
  rw [hyz, real_inner_smul_left, real_inner_self_eq_norm_sq] at this
  have : 0 < ε / 2 / ‖n‖ * ‖n‖ ^ 2 := by positivity
  linarith

/-- In a triangle `v z w` with `|vw| = a ≥ 10⁴`, `|zw| = b ≥ a`, `|vz| = 1`, the angle at `w`
is at most `1/200`. -/
theorem ang_small {v z w : Pt} {a b : ℝ} (ha : 10 ^ 4 ≤ a) (hb : a ≤ b) (hv : dist v w = a)
    (hz : dist z w = b) (h1 : dist v z = 1) : ang (v - w) (z - w) ≤ 1 / 200 := by
  set θ := ang (v - w) (z - w)
  have hθ0 : 0 ≤ θ := InnerProductGeometry.angle_nonneg _ _
  have hθπ : θ ≤ π := InnerProductGeometry.angle_le_pi _ _
  have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm (v - w) (z - w)
  rw [← dist_eq_norm, ← dist_eq_norm, hv, hz] at hc
  have key := two_inner_sub v w z
  rw [hv, hz, h1] at key
  have h1c : a * b * (1 - Real.cos θ) ≤ 1 / 2 := by
    change Real.cos θ * (a * b) = _ at hc
    nlinarith [sq_nonneg (b - a)]
  have hcos2 := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hcos2
  have hsc := Real.sin_sq_add_cos_sq (θ / 2)
  have hjordan := Real.mul_le_sin (x := θ / 2) (by positivity) (by linarith)
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d4
  set q := 2 / π * (θ / 2)
  have hq0 : 0 ≤ q := by positivity
  have h2 : 2 * q ^ 2 ≤ 1 - Real.cos θ := by nlinarith
  have hab : (10 : ℝ) ^ 8 ≤ a * b := by nlinarith
  have h3 : a * b * (2 * q ^ 2) ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1c
  have hq : q ≤ 1 / 10 ^ 4 := by nlinarith
  have hθq : θ = π * q := by simp only [q]; field_simp
  rw [hθq]
  nlinarith

/-- **(c1) bound** `< 24π/β < 7600`: the normal cone of `P₁` at `z` has angle `> β/2`; normal
cones are interior-disjoint.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `turning_sum_le` (or a direct disjoint-cones count), `exact_identity_a`, `c3`, `c9`,
kissing. Difficulty L. -/
theorem card_badC1_le (hX : Normal X) (F : DirField X) : ((badC1 X F).card : ℝ) ≤ 7600 := by
  have hPc : IsCompact (convexHull ℝ (X : Set Pt)) := X.finite_toSet.isCompact_convexHull ℝ
  set P := convexHull ℝ (X : Set Pt)
  have hPconv : Convex ℝ P := convex_convexHull ℝ _
  set Z := (Sset X).filter (fun z => z ∈ Dset X ∧ ∃ v ∈ Sset X, v ∉ Dset X ∧ dist v z = 1 ∧
      dist z (F.partner v) = diam X ∧ beta < ang (F.u v) (F.u z))
  -- step 1: every (c1) edge is a `δ`-edge at a point of `Z`
  have hsub : badC1 X F ⊆
      Z.biUnion (fun z => (partners X (minDist X) z).image (fun v => s(v, z))) := by
    intro e he
    obtain ⟨hbad, v, z, rfl, hvD, hzD, hexc⟩ := mem_filter.1 he
    obtain ⟨hedge, hng⟩ := mem_filter.1 hbad
    obtain ⟨hP, hd⟩ := mem_filter.1 hedge
    simp only [pairsS, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at hP
    obtain ⟨⟨hv, hz⟩, hvz⟩ := hP
    have hd1 : dist v z = 1 := by rw [← hX.minDist_eq]; exact hd
    have hang : beta < ang (F.u v) (F.u z) := by
      simp only [IsGood, not_forall, not_le] at hng
      obtain ⟨p, q, hpq, hlt⟩ := hng
      rcases Sym2.eq_iff.1 hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hlt
      · rwa [ang, InnerProductGeometry.angle_comm]
    rw [mem_biUnion]
    refine ⟨z, mem_filter.2 ⟨hz, hzD, v, hv, hvD, hd1, hexc, hang⟩,
      mem_image.2 ⟨v, mem_partners.2 ⟨mem_of_mem_Sset hv, hvz, ?_⟩, rfl⟩⟩
    rw [dist_comm, hd1, hX.minDist_eq]
  have hcount : ((badC1 X F).card : ℝ) ≤ 6 * Z.card := by
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∑ z ∈ Z, ((partners X (minDist X) z).image (fun v => s(v, z))).card ≤
        ∑ _z ∈ Z, 6 :=
      sum_le_sum fun z _ => card_image_le.trans (card_partners_minDist_le X z)
    rw [sum_const, smul_eq_mul] at h2
    have := h1.trans h2
    have : (badC1 X F).card ≤ 6 * Z.card := by linarith
    exact_mod_cast this
  -- the outward normal `−u_z` of `P₁` at `z ∈ S ∩ D`
  have hN : ∀ z ∈ Sset X, z ∈ Dset X → -F.u z ∈ normalCone P z := by
    intro z hzS hzD
    apply mem_normalCone_convexHull
    intro y hy
    rw [inner_neg_right, neg_nonpos]
    have := exact_identity_a F hzS hzD hy
    have hΔ := diam_pos_of_mem_Sset hzS
    have hp : 0 ≤ dist y z ^ 2 / (2 * diam X) := by positivity
    linarith
  -- step 2: each `z ∈ Z` has turning `> 1/200` in `P₁`
  have hturn : ∀ z ∈ Z, 1 / 200 < turning P {z} := by
    intro z hz
    obtain ⟨hzS, hzD, v, hv, hvD, hd1, hexc, hang⟩ := mem_filter.1 hz
    have hΔ : 0 < diam X := diam_pos_of_mem_Sset hzS
    have hwX : F.partner v ∈ X := F.partner_mem v hv
    have hxX := F.partner_mem z hzS
    have hzx : dist z (F.partner z) = diam X := F.partner_D z hzS hzD
    set m := (diam X)⁻¹ • (F.partner v - z)
    have hn2 : -m ∈ normalCone P z := by
      apply mem_normalCone_convexHull
      intro y hy
      rw [inner_neg_right, neg_nonpos, real_inner_smul_right]
      apply mul_nonneg (inv_nonneg.2 hΔ.le)
      have key := two_inner_sub y z (F.partner v)
      have hle := dist_le_diam hy hwX
      rw [dist_comm (F.partner v) z, hexc] at key
      have : dist y (F.partner v) ^ 2 ≤ diam X ^ 2 := pow_le_pow_left₀ dist_nonneg hle 2
      nlinarith [sq_nonneg (dist y z)]
    have hu1 : ‖-F.u z‖ = 1 := by rw [norm_neg]; exact F.norm_u' hzS
    have hm1 : ‖m‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hΔ, ← dist_eq_norm, dist_comm, hexc,
        inv_mul_cancel₀ hΔ.ne']
    have hu2 : ‖-m‖ = 1 := by rw [norm_neg]; exact hm1
    have hsmall : ang (F.u v) m ≤ 1 / 200 := by
      have hdv : dist v (F.partner v) = dist2 X := F.partner_K v hv hvD
      have hpos2 := dist2_pos_of_mem_Sset hv
      rw [ang, DirField.u, InnerProductGeometry.angle_smul_left_of_pos _ _
        (by rw [hdv]; exact inv_pos.2 hpos2),
        InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.2 hΔ),
        ← InnerProductGeometry.angle_neg_neg, neg_sub, neg_sub]
      exact ang_small hX.large (dist2_le_diam X) hdv hexc hd1
    have htri := InnerProductGeometry.angle_le_angle_add_angle (F.u v) m (F.u z)
    have hang2 : 1 / 200 < ang (-F.u z) (-m) := by
      rw [ang, InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_comm]
      unfold ang at hsmall hang
      have hβ : beta = 1 / 100 := rfl
      rw [hβ] at hang
      linarith
    have hltpi : ang (-F.u z) (-m) < π := by
      rw [ang, InnerProductGeometry.angle_neg_neg]
      refine lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _) fun hpi => ?_
      obtain ⟨-, r, hr, hrm⟩ := InnerProductGeometry.angle_eq_pi_iff.1 hpi
      have habs : |r| = 1 := by
        have := congrArg norm hrm
        rwa [hm1, norm_smul, F.norm_u' hzS, mul_one, Real.norm_eq_abs, eq_comm] at this
      have hr1 : r = -1 := by rw [abs_of_neg hr] at habs; linarith
      rw [hr1, neg_one_smul, DirField.u, hzx] at hrm
      have hwz : F.partner v - z = z - F.partner z := by
        have := congrArg (fun y => diam X • y) hrm
        simp only [m, smul_neg, smul_smul, mul_inv_cancel₀ hΔ.ne', one_smul] at this
        rw [this]; abel
      have hdw : dist (F.partner v) (F.partner z) = 2 * diam X := by
        rw [dist_eq_norm, show F.partner v - F.partner z =
          (F.partner v - z) + (z - F.partner z) by abel, hwz, ← two_smul ℝ, norm_smul,
          ← dist_eq_norm, hzx]
        norm_num
      have := dist_le_diam hwX hxX
      linarith
    have := ang_le_turning_of_normals (Set.mem_singleton z) (hN z hzS hzD) hn2 hu1 hu2 hltpi
    linarith
  -- step 3: Lemma 3.4 with multiplicity 1
  have hfront : ∀ z ∈ Z, ({z} : Set Pt) ⊆ frontier P := by
    intro z hz y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    obtain ⟨hzS, hzD, -⟩ := mem_filter.1 hz
    refine mem_frontier_of_normal (subset_convexHull ℝ _ (mem_coe.2 (mem_of_mem_Sset hzS)))
      ?_ (hN y hzS hzD)
    intro h0
    have := F.norm_u' hzS
    rw [← norm_neg, h0, norm_zero] at this
    norm_num at this
  have hsum := turning_sum_le hPconv hPc Z (fun z => ({z} : Set Pt)) hfront
    (fun _ _ => isClosed_singleton) 1 (fun x => card_le_one.2 fun a ha b hb => by
      simp only [Finset.mem_filter, Set.mem_singleton_iff] at ha hb
      rw [← ha.2, ← hb.2])
  have hZ : (Z.card : ℝ) * (1 / 200) ≤ 2 * π * 1 := by
    have : ∑ _z ∈ Z, (1 / 200 : ℝ) ≤ ∑ z ∈ Z, turning P {z} :=
      sum_le_sum fun z hz => (hturn z hz).le
    rw [sum_const, nsmul_eq_mul] at this
    push_cast at hsum
    linarith
  have hpi := Real.pi_lt_d4
  linarith

/-- **[C8]** `cos α ≥ −0.8821` on `ρ ∈ [1 − 10⁻⁴, 1]` (step 3 of (c2)).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c8_cos {ρ : ℝ} (h0 : 1 - 1 / 10 ^ 4 ≤ ρ) (h1 : ρ ≤ 1) :
    -0.8821 ≤ (1 + ρ ^ 2 - 1.94 ^ 2) / (2 * ρ) := by
  have hpos : 0 < 2 * ρ := by norm_num at h0; linarith
  rw [le_div_iff₀ hpos]
  norm_num at h0 ⊢
  nlinarith

/-- **[C8]** the walk leaves the disc: `(Δ₂ − d₀)² + (2/5)(Δ₂ − d₀)·L·β > Δ₂²` at `L = 6/β`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c8_walk {Δ₂ d₀ : ℝ} (h : 10 ^ 4 ≤ Δ₂) (h0 : 0 ≤ d₀) (h1 : d₀ ≤ 1) :
    Δ₂ ^ 2 < (Δ₂ - d₀) ^ 2 + 2 / 5 * (Δ₂ - d₀) * (6 / beta) * beta := by
  norm_num [beta]
  nlinarith

/-- **(c2) bound** `< 48π(2L + 1)/β < 1.82·10⁷` (`L = 600`).

TODO: prove.
What's missing: depth `d₀ ∈ [0, 1 − t]`; `α ∈ (β/2, 151.9°]` ([C8] `c8_cos`); walk along `∂K`
with forward tangents within `β/4` of `e₀` leaves `D(x_z, Δ₂)` by `σ = L` (`c8_walk`), so
`J_v` has turning `> β/4`; Lemma 3.4 with multiplicity `2L + 1`.
Acceptance: no `sorry`.
Depends on: `turning_sum_le`, `card_le_arcLength`, `c8_cos`, `c8_walk`, `c9`, kissing;
one-sided tangents of convex curves. Difficulty XL. -/
theorem card_badC2_le (hX : Normal X) (F : DirField X) : ((badC2 X F).card : ℝ) ≤ 18200000 := by
  sorry

/-- **Total bad edges** `≤ cBad`.

TODO: none (proved from the four counts).
Acceptance: no `sorry` (inherits).
Depends on: `bad_subset`, `card_badKK_le`, `card_badDD_le`, `card_badC1_le`, `card_badC2_le`,
`c9`. -/
theorem card_bad_le (hX : Normal X) (F : DirField X) : ((bad X F).card : ℝ) ≤ cBad := by
  have h := card_le_card (bad_subset F)
  have h1 := card_union_le (badKK X F ∪ badDD X F ∪ badC1 X F) (badC2 X F)
  have h2 := card_union_le (badKK X F ∪ badDD X F) (badC1 X F)
  have h3 := card_union_le (badKK X F) (badDD X F)
  have e1 := card_badKK_le hX F
  have e2 := card_badDD_le hX F
  have e3 := card_badC1_le hX F
  have e4 := card_badC2_le hX F
  have hc := c9.2.2.2.2
  have : ((bad X F).card : ℝ) ≤ (badKK X F).card + (badDD X F).card + (badC1 X F).card +
      (badC2 X F).card := by
    exact_mod_cast h.trans (h1.trans (by omega))
  linarith

end

end Erdos132Main

import Erdos.E132MainDefs

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

/-- **Lemma 3.4 (multiplicity)**: if every boundary point lies in at most `M` of the sets
`γ_i ⊆ ∂K`, then `Σ turning(γ_i) ≤ 2πM`.

TODO: prove.
What's missing: for all but countably many directions `ν` the support point `y_ν` is unique;
`ν ∈ N(γ_i) ⟺ y_ν ∈ γ_i`; integrate the indicator sum over `ν ∈ [0, 2π)`.
Acceptance: no `sorry`.
Depends on: measure theory on `ℝ`, support functions of convex bodies. Difficulty L. -/
theorem turning_sum_le {K : Set Pt} (hK : Convex ℝ K) (hKc : IsCompact K) {ι : Type*}
    (A : Finset ι) (γ : ι → Set Pt) (hγ : ∀ i ∈ A, γ i ⊆ frontier K) (M : ℕ)
    (hM : ∀ x, (A.filter (fun i => x ∈ γ i)).card ≤ M) :
    ∑ i ∈ A, turning K (γ i) ≤ 2 * π * M := by
  sorry

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
  sorry

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

/-- **(c1) bound** `< 24π/β < 7600`: the normal cone of `P₁` at `z` has angle `> β/2`; normal
cones are interior-disjoint.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `turning_sum_le` (or a direct disjoint-cones count), `exact_identity_a`, `c3`, `c9`,
kissing. Difficulty L. -/
theorem card_badC1_le (hX : Normal X) (F : DirField X) : ((badC1 X F).card : ℝ) ≤ 7600 := by
  sorry

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

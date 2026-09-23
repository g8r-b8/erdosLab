import Erdos.E132MainLocal

/-!
# Erdős Problem 132, `54/37` theorem — Regions I, II, III (§§6–7)

Every region lemma bounds `e(S)`; the top-level region statements (`regionI`, `regionII_high`,
`regionII_rest`, `regionII_res`, `regionIII`) are **proved** here from the finer lemmas, so the
statements are checked to fit together.  Region split on `τ` (with `β = 1/100`):

| region | `τ` range | `e(S) ≤` |
|---|---|---|
| I | `τ ≤ √3/2 − 2β` | `|S| + C` |
| III | `√3/2 − 2β < τ < √3/2 + 3β` | `|S| + 2|P₁| + C` |
| II-rest | `√3/2 + 3β ≤ τ < cos(β/2)` | `(5/4)|S| + C` |
| II-res | `cos(β/2) ≤ τ ≤ 1` | `(4/3)|S| + C` |
| II-high | `τ > 1` | `|S| + C` |
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Helpers (coordinates, separation, unit vectors, offsets, T-steps) -/

theorem inner_pt (x y : Pt) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]; ring

theorem norm_sq_pt (x : Pt) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_pt]; ring

theorem dist_sq_pt (x y : Pt) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq_pt]; simp

@[simp] theorem perp_apply0 (a : Pt) : perp a 0 = - a 1 := by simp [perp]
@[simp] theorem perp_apply1 (a : Pt) : perp a 1 = a 0 := by simp [perp]

theorem pt_ext_iff {a b : Pt} : a = b ↔ a 0 = b 0 ∧ a 1 = b 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    ext i; fin_cases i <;> simp [h0, h1]

theorem det2_pt (a b : Pt) : det2 a b = a 0 * b 1 - a 1 * b 0 := rfl

theorem norm_perp (a : Pt) : ‖perp a‖ = ‖a‖ := by
  have h : ‖perp a‖ ^ 2 = ‖a‖ ^ 2 := by rw [norm_sq_pt, norm_sq_pt]; simp; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem perp_sub (a b : Pt) : perp (a - b) = perp a - perp b := by
  rw [pt_ext_iff]; simp; ring

theorem unit_sq {a : Pt} (h : ‖a‖ = 1) : a 0 ^ 2 + a 1 ^ 2 = 1 := by
  rw [← norm_sq_pt, h, one_pow]

theorem inner_unit_le {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : |inner ℝ a b| ≤ 1 := by
  have := abs_real_inner_le_norm a b; rw [ha, hb] at this; simpa using this

theorem ang_unit {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ang a b = Real.arccos (inner ℝ a b) := by
  unfold ang InnerProductGeometry.angle; rw [ha, hb]; simp

theorem cos_ang_unit {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    Real.cos (ang a b) = inner ℝ a b := by
  unfold ang; rw [InnerProductGeometry.cos_angle, ha, hb]; simp

theorem ang_comm (a b : Pt) : ang a b = ang b a := InnerProductGeometry.angle_comm a b

/-- Chord `≤` arc for unit vectors. -/
theorem norm_sub_le_ang {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a - b‖ ≤ ang a b := by
  have h0 : 0 ≤ ang a b := InnerProductGeometry.angle_nonneg a b
  have hc := Real.one_sub_sq_div_two_le_cos (x := ang a b)
  rw [cos_ang_unit ha hb] at hc
  have hn : ‖a - b‖ ^ 2 = 2 - 2 * inner ℝ a b := by
    rw [@norm_sub_sq_real, ha, hb]; ring
  have : ‖a - b‖ ^ 2 ≤ ang a b ^ 2 := by rw [hn]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) h0).1 this

/-- A lower bound on an angle from an upper bound on the inner product. -/
theorem lt_ang_of_inner_lt {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {θ : ℝ} (h0 : 0 ≤ θ)
    (hπ : θ ≤ π) (h : inner ℝ a b < Real.cos θ) : θ < ang a b := by
  rw [ang_unit ha hb]
  have h1 := inner_unit_le ha hb
  rw [abs_le] at h1
  calc θ = Real.arccos (Real.cos θ) := (Real.arccos_cos h0 hπ).symm
    _ < Real.arccos (inner ℝ a b) :=
        Real.arccos_lt_arccos h1.1 h (Real.cos_le_one θ)

theorem cos_le_inner_of_ang_le {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {θ : ℝ}
    (hπ : θ ≤ π) (h : ang a b ≤ θ) : Real.cos θ ≤ inner ℝ a b := by
  rw [← cos_ang_unit ha hb]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg a b) hπ h

/-- Decomposition in the frame `(u, u^⊥)` of a unit `u`. -/
theorem decomp {u : Pt} (hu : ‖u‖ = 1) (e : Pt) :
    e = inner ℝ e u • u + det2 u e • perp u := by
  have h := unit_sq hu
  rw [pt_ext_iff, inner_pt, det2_pt]; simp
  constructor
  · linear_combination (-e 0) * h
  · linear_combination (-e 1) * h

theorem inner_sq_add_det_sq {u e : Pt} (hu : ‖u‖ = 1) :
    inner ℝ e u ^ 2 + det2 u e ^ 2 = ‖e‖ ^ 2 := by
  have h := unit_sq hu
  rw [inner_pt, det2_pt, norm_sq_pt]; linear_combination (e 0 ^ 2 + e 1 ^ 2) * h

/-- Lagrange-type identity: `(c·a)(c·b) + det(c,a) det(c,b) = |c|² (a·b)`. -/
theorem inner_mul_add_det_mul (c a b : Pt) :
    inner ℝ c a * inner ℝ c b + det2 c a * det2 c b = ‖c‖ ^ 2 * inner ℝ a b := by
  rw [inner_pt, inner_pt, inner_pt, det2_pt, det2_pt, norm_sq_pt]; ring

theorem norm_frame {a c : ℝ} (h : a ^ 2 + c ^ 2 = 1) (w : Pt) : ‖a • w + c • perp w‖ = ‖w‖ := by
  have : ‖a • w + c • perp w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [norm_sq_pt, norm_sq_pt]; simp; linear_combination (w 0 ^ 2 + w 1 ^ 2) * h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem norm_frame_le (a c : ℝ) {u : Pt} (hu : ‖u‖ = 1) : ‖a • u + c • perp u‖ ≤ |a| + |c| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_perp, hu, Real.norm_eq_abs, Real.norm_eq_abs]; simp

/-- Offsets `o_σ(u) = −τu + σ s u^⊥`: `|o_σ(u) − o_σ'(u')| ≤ |τ||u − u'| + 2s`. -/
theorem norm_offset_sub {u u' : Pt} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) {τ s σ σ' : ℝ}
    (hs : 0 ≤ s) (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1) :
    ‖((-τ) • u + (σ * s) • perp u) - ((-τ) • u' + (σ' * s) • perp u')‖ ≤
      |τ| * ‖u - u'‖ + 2 * s := by
  have e : ((-τ) • u + (σ * s) • perp u) - ((-τ) • u' + (σ' * s) • perp u') =
      (-τ) • (u - u') + ((σ * s) • perp u - (σ' * s) • perp u') := by
    rw [smul_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_neg]
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_perp, norm_perp, hu, hu', Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul]
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;>
      simp [abs_of_nonneg hs] <;> linarith

/-- Two right T-steps from nearly parallel normals are close. -/
theorem norm_tstep_sub {u₁ u₂ e₁ e₂ : Pt} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (he₁ : ‖e₁‖ = 1)
    (he₂ : ‖e₂‖ = 1) (ha₁ : 0 < inner ℝ e₁ u₁) (ha₁' : inner ℝ e₁ u₁ < beta)
    (ha₂ : 0 < inner ℝ e₂ u₂) (ha₂' : inner ℝ e₂ u₂ < beta) (hc₁ : det2 u₁ e₁ < 0)
    (hc₂ : det2 u₂ e₂ < 0) : ‖e₁ - e₂‖ ≤ ‖u₁ - u₂‖ + 2 * beta := by
  set a₁ := inner ℝ e₁ u₁
  set a₂ := inner ℝ e₂ u₂
  set c₁ := det2 u₁ e₁
  set c₂ := det2 u₂ e₂
  have n₁ := inner_sq_add_det_sq (e := e₁) hu₁
  have n₂ := inner_sq_add_det_sq (e := e₂) hu₂
  rw [he₁] at n₁; rw [he₂] at n₂
  have E : e₁ - e₂ = (a₁ • (u₁ - u₂) + c₁ • perp (u₁ - u₂)) +
      ((a₁ - a₂) • u₂ + (c₁ - c₂) • perp u₂) := by
    conv_lhs => rw [decomp hu₁ e₁, decomp hu₂ e₂]
    rw [perp_sub, smul_sub, smul_sub, sub_smul, sub_smul]; abel
  rw [E]
  refine (norm_add_le _ _).trans ?_
  rw [norm_frame (by linarith) (u₁ - u₂)]
  have h2 := norm_frame_le (a₁ - a₂) (c₁ - c₂) hu₂
  have hb : beta = 1 / 100 := rfl
  have ha : |a₁ - a₂| ≤ beta := by rw [abs_le]; constructor <;> linarith
  have hc : |c₁ - c₂| ≤ beta := by
    rw [abs_le]
    constructor <;> nlinarith
  linarith

/-- Two unit solutions of `c·u = −τ` that differ have `u₁·u₂ = 2τ² − 1`. -/
theorem inner_two_sol {c u₁ u₂ : Pt} {τ : ℝ} (hc : ‖c‖ = 1) (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1)
    (e₁ : inner ℝ c u₁ = -τ) (e₂ : inner ℝ c u₂ = -τ) (hne : u₁ ≠ u₂) :
    inner ℝ u₁ u₂ = 2 * τ ^ 2 - 1 := by
  have n₁ := inner_sq_add_det_sq (e := u₁) hc
  have n₂ := inner_sq_add_det_sq (e := u₂) hc
  rw [real_inner_comm, e₁, h₁] at n₁
  rw [real_inner_comm, e₂, h₂] at n₂
  have hL := inner_mul_add_det_mul c u₁ u₂
  rw [e₁, e₂, hc] at hL
  have hd : det2 c u₁ ≠ det2 c u₂ := by
    intro hd; apply hne
    rw [decomp hc u₁, decomp hc u₂, real_inner_comm, e₁, real_inner_comm, e₂, hd]
  have hd' : det2 c u₁ = - det2 c u₂ := by
    have : (det2 c u₁ - det2 c u₂) * (det2 c u₁ + det2 c u₂) = 0 := by linear_combination n₁ - n₂
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hd
    · linarith
  rw [hd'] at hL
  linear_combination -hL - n₂

/-! ### The point set -/

theorem dist_mem_distSetS' {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    dist x y ∈ distSetS X := by
  unfold distSetS pairsS
  refine mem_image.2 ⟨s(x, y), mem_filter.2 ⟨mk_mem_sym2_iff.2 ⟨hx, hy⟩, ?_⟩, ?_⟩
  · simpa using hxy
  · simp [pairDist]

theorem pos_of_mem_distSetS' {d : ℝ} (hd : d ∈ distSetS X) : 0 < d := by
  unfold distSetS pairsS at hd
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hd
  induction z using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using (mem_filter.1 hz).2
    simpa [pairDist] using dist_pos.2 hab

theorem minDist_le_dist {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    minDist X ≤ dist x y := by
  have hm := dist_mem_distSetS' hx hy hxy
  unfold minDist
  rw [dif_pos ⟨_, hm⟩]
  exact min'_le _ _ hm

theorem one_le_dist (h1 : minDist X = 1) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    1 ≤ dist x y := h1 ▸ minDist_le_dist hx hy hxy

theorem eq_of_dist_lt_one (h1 : minDist X = 1) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X)
    (h : dist x y < 1) : x = y := by
  by_contra hxy; exact absurd (one_le_dist h1 hx hy hxy) (not_le.2 h)

theorem dist2_nonneg (X : Finset Pt) : 0 ≤ dist2 X := by
  unfold dist2
  split_ifs with h
  · exact (pos_of_mem_distSetS' (mem_of_mem_erase (max'_mem _ h))).le
  · exact le_rfl

/-- The two largest distances, when `Δ₂ > 0`. -/
structure Two (X : Finset Pt) : Prop where
  pos : 0 < dist2 X
  lt : dist2 X < diam X
  le_diam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ diam X
  gap : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ dist2 X ∨ dist x y = diam X

theorem two_of_pos (h : 0 < dist2 X) : Two X := by
  have h' := h
  unfold dist2 at h'
  split_ifs at h' with hne
  · have hne0 : (distSetS X).Nonempty := hne.mono (erase_subset _ _)
    have hd : diam X = (distSetS X).max' hne0 := by unfold diam; rw [dif_pos hne0]
    have hd2 : dist2 X = ((distSetS X).erase (diam X)).max' hne := by
      unfold dist2; rw [dif_pos hne]
    have h2 := max'_mem _ hne
    rw [← hd2] at h2
    have hle : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ diam X := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst hxy; rw [dist_self, hd]; exact (pos_of_mem_distSetS' (max'_mem _ _)).le
      · rw [hd]; exact le_max' _ _ (dist_mem_distSetS' hx hy hxy)
    refine ⟨h, lt_of_le_of_ne (hd ▸ le_max' _ _ (mem_of_mem_erase h2)) (ne_of_mem_erase h2),
      hle, ?_⟩
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy; left; rw [dist_self]; exact h.le
    rcases (hle x hx y hy).lt_or_eq with hl | hl
    · left; rw [hd2]; exact le_max' _ _ (mem_erase.2 ⟨hl.ne, dist_mem_distSetS' hx hy hxy⟩)
    · exact Or.inr hl
  · exact absurd h' (lt_irrefl 0)

theorem mem_Dset_of {p q : Pt} (hp : p ∈ X) (hq : q ∈ X) (hpq : q ≠ p) (h : dist p q = diam X) :
    p ∈ Dset X := by
  unfold Dset partners
  exact mem_filter.2 ⟨hp, q, mem_filter.2 ⟨hq, hpq, h⟩⟩

theorem Normal.dist2_pos (hX : Normal X) : 0 < dist2 X := by
  have := hX.large; linarith

theorem Sset_sub : Sset X ⊆ X := filter_subset _ _

/-- `τ ≥ −1/2` once `Δ₂ ≥ 1`. -/
theorem neg_half_le_tau (hT : Two X) (h1 : 1 ≤ dist2 X) : -(1 / 2) ≤ tau X := by
  have ht : 0 < tgap X := by unfold tgap; linarith [hT.lt]
  have : (1 - tgap X ^ 2) / (2 * dist2 X) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  unfold tau; linarith

theorem abs_tau_le_one (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1) : |tau X| ≤ 1 := by
  have := Real.sqrt_nonneg 3
  rw [abs_le]; unfold beta at hτ₁; constructor <;> linarith

namespace IsRung

variable {F : DirField X} {v z : Pt}

theorem memX (h : IsRung F v z) : v ∈ X ∧ z ∈ X := ⟨Sset_sub h.1, Sset_sub h.2.2.1⟩

theorem ne (h : IsRung F v z) : v ≠ z := by
  intro e; have := h.2.2.2.2.1; rw [e, dist_self] at this; norm_num at this

/-- A rung forces `Δ₂ > 0` (so the two largest distances exist) and `Δ₂ ≥ 1`. -/
theorem two (h : IsRung F v z) : Two X ∧ 1 ≤ dist2 X := by
  obtain ⟨hv, hvD, hz, hzD, h1, hex⟩ := h
  have hvX := Sset_sub hv
  have hzX := Sset_sub hz
  have hvz : z ≠ v := by intro e; rw [e, dist_self] at h1; norm_num at h1
  have hpos : 0 < dist2 X := by
    rcases (dist2_nonneg X).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hp := F.partner_K v hv hvD
      rw [← h', dist_eq_zero] at hp
      rw [← hp] at hex
      rw [dist_comm] at hex
      exact hvD (mem_Dset_of hvX hzX hvz hex)
  have hT := two_of_pos hpos
  refine ⟨hT, ?_⟩
  rcases hT.gap v hvX z hzX with h' | h'
  · linarith
  · exact absurd (mem_Dset_of hvX hzX hvz h') hvD

theorem tau_ge (h : IsRung F v z) : -(1 / 2) ≤ tau X := neg_half_le_tau h.two.1 h.two.2

/-- `c = z − v` is a unit vector with `c·u_v = −τ`. -/
theorem inner_eq (h : IsRung F v z) : inner ℝ (z - v) (F.u v) = - tau X :=
  exact_identity_c F h.1 h.2.1 h.2.2.2.2.2 (by rw [dist_comm]; exact h.2.2.2.2.1)

theorem norm_c (h : IsRung F v z) : ‖z - v‖ = 1 := by
  rw [← dist_eq_norm, dist_comm]; exact h.2.2.2.2.1

end IsRung

/-- `δ`-edges inside `S` are non-degenerate pairs of points of `S`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem mem_edges {z : Sym2 Pt} (hz : z ∈ edges X) : ¬ z.IsDiag ∧ ∀ p ∈ z, p ∈ Sset X := by
  unfold edges pairsS at hz
  simp only [mem_filter, mem_sym2_iff] at hz
  exact ⟨hz.1.2, hz.1.1⟩

/-! ## §6 Region I: `τ ≤ √3/2 − 2β` -/

/-- **[C4]** the elevation window is `< 60°`: `arcsin(√3/2 − 2β) + arcsin β < π/3`.

TODO: prove (via `cos(A + B) > 1/2`).
Acceptance: no `sorry`.
Depends on: `Real.arcsin` bounds. Difficulty M. -/
theorem c4_window : Real.arcsin (√3 / 2 - 2 * beta) + Real.arcsin beta < π / 3 := by
  sorry

/-- **Region I degree bound**: every `p ∈ S` has at most two good `δ`-edges (one per side of
`ℝu_p`; none on the line).

TODO: prove.
What's missing: elevations of good neighbours lie in `[−arcsin τ, arcsin β)` (cases `τ ≥ 0`,
`τ < 0`, `p ∈ D`), a window `< 60°` by [C4]; two unit neighbours are `≥ 60°` apart.
Acceptance: no `sorry`.
Depends on: `exact_identity_a`, `exact_identity_b`, `exact_identity_c`, `c4_window`,
`DirField.norm_u`. Difficulty M–L. -/
theorem regionI_deg_le (hX : Normal X) (F : DirField X) (hτ : tau X ≤ √3 / 2 - 2 * beta)
    {p : Pt} (hp : p ∈ Sset X) : ((good X F).filter (fun z => p ∈ z)).card ≤ 2 := by
  sorry

/-- Region I: `#good ≤ |S|`.

TODO: none (handshake).
Acceptance: no `sorry` (inherits).
Depends on: `regionI_deg_le`, `two_mul_card_le_of_deg_le`, `mem_edges`. -/
theorem regionI_card_good (hX : Normal X) (F : DirField X) (hτ : tau X ≤ √3 / 2 - 2 * beta) :
    (good X F).card ≤ (Sset X).card := by
  have h := two_mul_card_le_of_deg_le (V := Sset X) (E := good X F) (k := 2)
    (fun z hz => mem_edges (mem_filter.1 hz).1) (fun p hp => regionI_deg_le hX F hτ hp)
  omega

/-- **Region I** (§6): `e(S) ≤ |S| + C`.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `card_good_add_bad`, `regionI_card_good`, `card_bad_le`. -/
theorem regionI (hX : Normal X) (F : DirField X) (hτ : tau X ≤ √3 / 2 - 2 * beta) :
    (eS X : ℝ) ≤ (Sset X).card + (cBad + 100) := by
  have h1 := card_good_add_bad F
  have h2 : ((good X F).card : ℝ) ≤ (Sset X).card := by exact_mod_cast regionI_card_good hX F hτ
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by exact_mod_cast h1.symm
  linarith

/-! ## §7 common: `τ > √3/2 − 2β` -/

/-- **[C5, C6]** `τ > √3/2 − 2β ⇒ τ > 2β`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem two_beta_lt_of {τ : ℝ} (h : √3 / 2 - 2 * beta < τ) : 2 * beta < τ := by
  have : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [beta] at *; linarith

/-- `good ≤ goodPure + mixedT`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_good_le_pure_add_mixed (F : DirField X) :
    (good X F).card ≤ (goodPure X F).card + (mixedT X F).card := by
  rw [goodPure]; exact card_le_card_sdiff_add_card

/-! ## §7.1 Mixed T-edges (Region II only) -/

/-- **[C5]** In Region II, `t − arcsin β ≥ 0.886`.

TODO: prove (`t ≥ τ` if `t ≤ 1`, else `t > 1`; `arcsin β ≤ β + β³`).
Acceptance: no `sorry`.
Depends on: `tau_sub_tgap`. Difficulty M. -/
theorem c5_tgap (hX : Normal X) (hτ : √3 / 2 + 3 * beta ≤ tau X) :
    0.886 ≤ tgap X - Real.arcsin beta := by
  sorry

/-- **[C5]** `2π·10/0.886 < 71`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c5_mixed : 2 * π * 10 / 0.886 < 71 := by
  have hp := Real.pi_lt_d4
  rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **Lemma 7.1**: for a T-edge `vz` with `v ∈ S ∖ D`, `z ∈ S ∩ D`, the boundary arc of `K` of
length 2 from `v` on `z`'s side has turning `≥ t − arcsin β`.

TODO: prove.
What's missing: if the turning were `Θ < t − arcsin β`, the arc stays in a `Θ`-cone around the
tangent `e₀`, reaches distance 1 from `v` at some `σ* ≤ 2` at a point within `Θ + arcsin β < t`
of `z`, contradicting `dist(z, K) ≥ t` (Lemma 3.1(c)).
Acceptance: no `sorry`.
Depends on: `ball_polygon_b`, `ball_polygon_c`, `c5_tgap`; tangents of convex curves.
Difficulty L. -/
theorem lemma71 (hX : Normal X) (F : DirField X) (hτ : √3 / 2 + 3 * beta ≤ tau X) {v z : Pt}
    (hv : v ∈ Sset X) (hvD : v ∉ Dset X) (hz : z ∈ Sset X) (hzD : z ∈ Dset X)
    (hvz : dist v z = 1) (hT : IsTEdge F v z) :
    ∃ γ : ℝ → Pt, LipschitzWith 1 γ ∧ γ 0 = v ∧ γ '' Set.Icc 0 2 ⊆ frontier (KBall X) ∧
      tgap X - Real.arcsin beta ≤ turning (KBall X) (γ '' Set.Icc 0 2) := by
  sorry

/-- **Mixed T-edges** `< 71` in Region II (multiplicity `M ≤ 10`, Lemma 3.4).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `lemma71`, `turning_sum_le`, `card_le_arcLength`, `T1`, `c5_tgap`, `c5_mixed`.
Difficulty M (given the lemmas). -/
theorem card_mixedT_le (hX : Normal X) (F : DirField X) (hτ : √3 / 2 + 3 * beta ≤ tau X) :
    ((mixedT X F).card : ℝ) ≤ 71 := by
  sorry

/-! ## §7.2 Region II -/

/-- `τ > 1` ⇒ no rungs (3.2(c)).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `tau_le_one_of_exception`. Difficulty S. -/
theorem rungs_eq_empty (F : DirField X) (hτ : 1 < tau X) : rungs X F = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro e he
  obtain ⟨v, w, -, hr⟩ := (mem_filter.1 he).2
  have := tau_le_one_of_exception F hr.1 hr.2.1 hr.2.2.2.2.2
    (by rw [dist_comm]; exact hr.2.2.2.2.1)
  linarith

/-- **Region II-high** (`τ > 1`): `e(S) ≤ |S| + C`.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `card_good_add_bad`, `good_subset_T_union_rungs`, `rungs_eq_empty`,
`card_tEdges_le`, `card_bad_le`. -/
theorem regionII_high (hX : Normal X) (F : DirField X) (hτ : 1 < tau X) :
    (eS X : ℝ) ≤ (Sset X).card + (cBad + 100) := by
  have hsub := good_subset_T_union_rungs hX F (by unfold beta; linarith)
  rw [rungs_eq_empty F hτ, union_empty] at hsub
  have h2 : ((good X F).card : ℝ) ≤ (Sset X).card :=
    by exact_mod_cast (card_le_card hsub).trans (card_tEdges_le hX F)
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  linarith

/-- **[C5]** `2s + 6β < 1` for `√3/2 + 3β ≤ τ ≤ 1` (covers R1-at-z `2s + 2β`, R2
`2s + 2β + arcsin β`, R2-sym `2s + 4β + arcsin β`).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c5_sOff {τ : ℝ} (h1 : √3 / 2 + 3 * beta ≤ τ) (h2 : τ ≤ 1) :
    2 * √(1 - τ ^ 2) + 6 * beta < 1 := by
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [beta] at *
  have hτ : (0.896 : ℝ) ≤ τ := by linarith
  have hs : √(1 - τ ^ 2) < 0.47 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  linarith

/-- **[C5]** `cos(β/2) > √3/2 + 3β` (rhombi only near resonance).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c5_rhombus : √3 / 2 + 3 * beta < Real.cos (beta / 2) := by
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hc := Real.one_sub_sq_div_two_le_cos (x := beta / 2)
  rw [beta] at *
  norm_num at hc ⊢
  linarith

/-- **(R1) at `v`**: a K-vertex has at most one rung (in Region II).

TODO: prove (the two offsets are `2s < 1` apart; points are `≥ 1` apart).
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`. Difficulty S–M. -/
theorem R1_v (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v z₁ z₂ : Pt} (h₁ : IsRung F v z₁) (h₂ : IsRung F v z₂) : z₁ = z₂ := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F h₁
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F h₂
  have hu := F.norm_u h₁.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  refine eq_of_dist_lt_one hX.minDist_eq h₁.memX.2 h₂.memX.2 ?_
  have e : z₁ - z₂ = (z₁ - v) - (z₂ - v) := by abel
  rw [dist_eq_norm, e, e₁, e₂]
  refine (norm_offset_sub hu hu hs0 hσ₁ hσ₂).trans_lt ?_
  simp only [sub_self, norm_zero, mul_zero, zero_add]
  unfold sOff; unfold beta at hs; linarith

/-- **(R1) at `z`**: a D-vertex has at most one good rung (`|v − v′| ≤ 2s + 2β < 1`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`, rotation bound `|o(u) − o(u′)| ≤ ∠(u, u′)`.
Difficulty M. -/
theorem R1_z (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v₁ v₂ z : Pt} (h₁ : IsRung F v₁ z) (h₂ : IsRung F v₂ z)
    (hg₁ : ang (F.u v₁) (F.u z) ≤ beta) (hg₂ : ang (F.u v₂) (F.u z) ≤ beta) : v₁ = v₂ := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F h₁
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F h₂
  have hu₁ := F.norm_u h₁.1
  have hu₂ := F.norm_u h₂.1
  have huz := F.norm_u h₁.2.2.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hτ0 : |tau X| ≤ 1 := abs_tau_le_one hτ₁ hτ₂
  refine eq_of_dist_lt_one hX.minDist_eq h₁.memX.1 h₂.memX.1 ?_
  have e : v₁ - v₂ = (z - v₂) - (z - v₁) := by abel
  rw [dist_eq_norm, e, e₁, e₂]
  refine (norm_offset_sub hu₂ hu₁ hs0 hσ₂ hσ₁).trans_lt ?_
  have hd : ‖F.u v₂ - F.u v₁‖ ≤ 2 * beta := by
    have := norm_sub_le (F.u v₂ - F.u z) (F.u v₁ - F.u z)
    rw [sub_sub_sub_cancel_right] at this
    have a₁ := norm_sub_le_ang hu₁ huz
    have a₂ := norm_sub_le_ang hu₂ huz
    linarith
  have : |tau X| * ‖F.u v₂ - F.u v₁‖ ≤ 2 * beta :=
    (mul_le_of_le_one_left (norm_nonneg _) hτ0).trans hd
  have hb : (0 : ℝ) < beta := by unfold beta; norm_num
  unfold sOff; linarith


/-- Data of a right T-step `p → q`: unit step, elevation in `(0, β)`, on the right. -/
theorem IsSideT.step {F : DirField X} {p q : Pt} (h : IsSideT F (-1) p q) :
    ‖q - p‖ = 1 ∧ 0 < inner ℝ (q - p) (F.u p) ∧ inner ℝ (q - p) (F.u p) < beta ∧
      det2 (F.u p) (q - p) < 0 := by
  obtain ⟨-, -, h1, -, ⟨a, b, -, -⟩, hs⟩ := h
  refine ⟨by rw [← dist_eq_norm, dist_comm]; exact h1, a, b, by linarith⟩

/-- `|u_a − u_c| ≤ β₁ + β₂` from two angle bounds through `u_b`. -/
theorem norm_u_sub_le {a b c : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖a - c‖ ≤ ang a b + ang b c := by
  have := norm_sub_le (a - b) (c - b)
  rw [sub_sub_sub_cancel_right] at this
  have h1 := norm_sub_le_ang ha hb
  have h2 := norm_sub_le_ang hc hb
  rw [ang_comm c b] at h2
  linarith

/-- **(R2) proximity**: `(v₀, z₀)` a good rung, `v₁`/`z₁` the right pure T-neighbours of
`v₀`/`z₀`; if `v₁` has a good rung `(v₁, z′)` then `z′ = z₁` (`|z′ − z₁| ≤ 2s + 2β + arcsin β`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`, T-step geometry. Difficulty M. -/
theorem R2 (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1)
    {v₀ z₀ v₁ z₁ z' : Pt} (hr₀ : IsRung F v₀ z₀) (hg₀ : ang (F.u v₀) (F.u z₀) ≤ beta)
    (hv : IsSideT F (-1) v₀ v₁) (hv₁ : v₁ ∉ Dset X) (hz : IsSideT F (-1) z₀ z₁)
    (hz₁ : z₁ ∈ Dset X) (hr : IsRung F v₁ z') (hg : ang (F.u v₁) (F.u z') ≤ beta) :
    z' = z₁ := by
  obtain ⟨σ₀, hσ₀, o₀⟩ := rung_offset F hr₀
  obtain ⟨σ₁, hσ₁, o₁⟩ := rung_offset F hr
  obtain ⟨n₁, a₁, a₁', c₁⟩ := hv.step
  obtain ⟨n₂, a₂, a₂', c₂⟩ := hz.step
  have huv₀ := F.norm_u hr₀.1
  have huz₀ := F.norm_u hr₀.2.2.1
  have huv₁ := F.norm_u hr.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hτ0 := abs_tau_le_one hτ₁ hτ₂
  have hb : (0 : ℝ) < beta := by unfold beta; norm_num
  refine eq_of_dist_lt_one hX.minDist_eq hr.memX.2 (Sset_sub hz.2.1) ?_
  have e : z' - z₁ = ((v₁ - v₀) - (z₁ - z₀)) + ((z' - v₁) - (z₀ - v₀)) := by abel
  rw [dist_eq_norm, e, o₀, o₁]
  refine (norm_add_le _ _).trans_lt ?_
  have hE := norm_tstep_sub huv₀ huz₀ n₁ n₂ a₁ a₁' a₂ a₂' c₁ c₂
  have hO := norm_offset_sub huv₁ huv₀ hs0 hσ₁ hσ₀ (τ := tau X)
  have h1 : ‖F.u v₀ - F.u z₀‖ ≤ beta := (norm_sub_le_ang huv₀ huz₀).trans hg₀
  have h2 : ‖F.u v₁ - F.u v₀‖ ≤ beta := by
    rw [norm_sub_rev]; exact (norm_sub_le_ang huv₀ huv₁).trans hv.2.2.2.1
  have h3 : |tau X| * ‖F.u v₁ - F.u v₀‖ ≤ beta :=
    (mul_le_of_le_one_left (norm_nonneg _) hτ0).trans h2
  have hs' : 2 * sOff X + 6 * beta < 1 := hs
  linarith

/-- **(R2-sym) symmetric proximity**: same setting; if `z₁` has a good rung `(v′, z₁)` then
`v′ = v₁` (`|v′ − v₁| ≤ 2s + 4β + arcsin β ≤ 2s + 6β < 1`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`, T-step geometry. Difficulty M. -/
theorem R2_sym (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v₀ z₀ v₁ z₁ v' : Pt} (hr₀ : IsRung F v₀ z₀)
    (hg₀ : ang (F.u v₀) (F.u z₀) ≤ beta) (hv : IsSideT F (-1) v₀ v₁) (hv₁ : v₁ ∉ Dset X)
    (hz : IsSideT F (-1) z₀ z₁) (hz₁ : z₁ ∈ Dset X) (hr : IsRung F v' z₁)
    (hg : ang (F.u v') (F.u z₁) ≤ beta) : v' = v₁ := by
  obtain ⟨σ₀, hσ₀, o₀⟩ := rung_offset F hr₀
  obtain ⟨σ₁, hσ₁, o₁⟩ := rung_offset F hr
  obtain ⟨n₁, a₁, a₁', c₁⟩ := hv.step
  obtain ⟨n₂, a₂, a₂', c₂⟩ := hz.step
  have huv₀ := F.norm_u hr₀.1
  have huz₀ := F.norm_u hr₀.2.2.1
  have huv' := F.norm_u hr.1
  have huz₁ := F.norm_u hr.2.2.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hτ0 := abs_tau_le_one hτ₁ hτ₂
  have hb : (0 : ℝ) < beta := by unfold beta; norm_num
  refine eq_of_dist_lt_one hX.minDist_eq hr.memX.1 (Sset_sub hv.2.1) ?_
  have e : v' - v₁ = ((z₁ - z₀) - (v₁ - v₀)) - ((z₁ - v') - (z₀ - v₀)) := by abel
  rw [dist_eq_norm, e, o₀, o₁]
  refine (norm_sub_le _ _).trans_lt ?_
  have hE := norm_tstep_sub huv₀ huz₀ n₁ n₂ a₁ a₁' a₂ a₂' c₁ c₂
  rw [norm_sub_rev] at hE
  have hO := norm_offset_sub huv' huv₀ hs0 hσ₁ hσ₀ (τ := tau X)
  have h1 : ‖F.u v₀ - F.u z₀‖ ≤ beta := (norm_sub_le_ang huv₀ huz₀).trans hg₀
  have h2 : ‖F.u v' - F.u v₀‖ ≤ 3 * beta := by
    have k1 := norm_u_sub_le huv' huz₁ huz₀
    have k2 := norm_sub_le (F.u v' - F.u z₀) (F.u v₀ - F.u z₀)
    rw [sub_sub_sub_cancel_right] at k2
    have k3 : ang (F.u z₁) (F.u z₀) ≤ beta := by rw [ang_comm]; exact hz.2.2.2.1
    linarith
  have h3 : |tau X| * ‖F.u v' - F.u v₀‖ ≤ 3 * beta :=
    (mul_le_of_le_one_left (norm_nonneg _) hτ0).trans h2
  have hs' : 2 * sOff X + 6 * beta < 1 := hs
  linarith

/-- **(R3a) no three parallel rungs**: `u_v` solves `c·u = −τ`, which has two unit solutions,
and K-ends have distinct normals (Lemma 3.3).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `u_ne`, `DirField.norm_u`. Difficulty M. -/
theorem R3_no_three_parallel (F : DirField X) {v₁ v₂ v₃ z₁ z₂ z₃ : Pt} (h₁ : IsRung F v₁ z₁)
    (h₂ : IsRung F v₂ z₂) (h₃ : IsRung F v₃ z₃) (e₁₂ : z₁ - v₁ = z₂ - v₂)
    (e₁₃ : z₁ - v₁ = z₃ - v₃) : v₁ = v₂ ∨ v₁ = v₃ ∨ v₂ = v₃ := by
  have hc := h₁.norm_c
  have key : ∀ {v z : Pt}, IsRung F v z → z - v = z₁ - v₁ →
      F.u v = (- tau X) • (z₁ - v₁) + det2 (z₁ - v₁) (F.u v) • perp (z₁ - v₁) ∧
      det2 (z₁ - v₁) (F.u v) ^ 2 = 1 - tau X ^ 2 := by
    intro v z h e
    have hi := h.inner_eq
    rw [e] at hi
    have hu := F.norm_u h.1
    have n := inner_sq_add_det_sq (e := F.u v) hc
    rw [real_inner_comm, hi, hu] at n
    refine ⟨?_, by linarith⟩
    conv_lhs => rw [decomp hc (F.u v)]
    rw [real_inner_comm, hi]
  obtain ⟨k₁, d₁⟩ := key h₁ rfl
  obtain ⟨k₂, d₂⟩ := key h₂ e₁₂.symm
  obtain ⟨k₃, d₃⟩ := key h₃ e₁₃.symm
  have ne : ∀ {a b : Pt}, a ∈ Sset X → a ∉ Dset X → b ∈ Sset X → b ∉ Dset X →
      F.u a = F.u b → a = b := by
    intro a b ha haD hb hbD e
    by_contra hab; exact u_ne F ha haD hb hbD hab e
  set c := z₁ - v₁
  have sq : ∀ x y : ℝ, x ^ 2 = y ^ 2 → x = y ∨ x = -y := fun x y h => by
    have : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases sq _ _ (d₁.trans d₂.symm) with e | e
  · left; exact ne h₁.1 h₁.2.1 h₂.1 h₂.2.1 (by rw [k₁, k₂, e])
  rcases sq _ _ (d₁.trans d₃.symm) with e' | e'
  · right; left; exact ne h₁.1 h₁.2.1 h₃.1 h₃.2.1 (by rw [k₁, k₃, e'])
  right; right
  exact ne h₂.1 h₂.2.1 h₃.1 h₃.2.1 (by rw [k₂, k₃]; congr 2; linarith)


/-- Planar core of (R3b): `x, y` two distinct common points of `C(0,1)` and `C(d,1)` ⇒ `x + y = d`. -/
theorem rhombus_real {x0 x1 y0 y1 d0 d1 : ℝ} (hx : x0 ^ 2 + x1 ^ 2 = 1) (hy : y0 ^ 2 + y1 ^ 2 = 1)
    (hxd : (d0 - x0) ^ 2 + (d1 - x1) ^ 2 = 1) (hyd : (d0 - y0) ^ 2 + (d1 - y1) ^ 2 = 1)
    (hxy : ¬ (x0 = y0 ∧ x1 = y1)) (hd : ¬ (d0 = 0 ∧ d1 = 0)) :
    x0 + y0 = d0 ∧ x1 + y1 = d1 := by
  set w0 := x0 - y0
  set w1 := x1 - y1
  set b0 := x0 + y0 - d0
  set b1 := x1 + y1 - d1
  have hwd : w0 * d0 + w1 * d1 = 0 := by simp only [w0, w1]; linear_combination (hyd - hxd - hy + hx) / 2
  have hwb : w0 * b0 + w1 * b1 = 0 := by
    simp only [w0, w1, b0, b1]; linear_combination hx - hy - (hyd - hxd - hy + hx) / 2
  have hbd : b0 * d0 + b1 * d1 = 0 := by
    simp only [b0, b1]; linear_combination (hx - hxd + hy - hyd) / 2
  have hw : 0 < w0 ^ 2 + w1 ^ 2 := by
    by_contra h; push Not at h
    apply hxy; constructor
    · have : w0 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1]
      simp only [w0] at this; linarith
    · have : w1 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1]
      simp only [w1] at this; linarith
  have hd' : 0 < d0 ^ 2 + d1 ^ 2 := by
    by_contra h; push Not at h
    apply hd; constructor <;> nlinarith [sq_nonneg d0, sq_nonneg d1]
  have hdet : (w0 * d1 - w1 * d0) ^ 2 = (w0 ^ 2 + w1 ^ 2) * (d0 ^ 2 + d1 ^ 2) := by
    linear_combination (-(w0 * d0 + w1 * d1)) * hwd
  have hdet0 : w0 * d1 - w1 * d0 ≠ 0 := by
    intro h; rw [h] at hdet; nlinarith [mul_pos hw hd']
  have e0 : (w0 * d1 - w1 * d0) * b0 = 0 := by linear_combination d1 * hwb - w1 * hbd
  have e1 : (w0 * d1 - w1 * d0) * b1 = 0 := by linear_combination w0 * hbd - d0 * hwb
  have := (mul_eq_zero.1 e0).resolve_left hdet0
  have := (mul_eq_zero.1 e1).resolve_left hdet0
  constructor <;> linarith

/-- **(R3b) rhombi force parallel rungs**: a unit rhombus `v₀v₁z₁z₀` has `z₀ − v₀ = z₁ − v₁`
(`v₁, z₀` are the two points of `C(v₀,1) ∩ C(z₁,1)`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: planar circle intersection. Difficulty M. -/
theorem R3_rhombus {v₀ v₁ z₀ z₁ : Pt} (h₀₁ : dist v₀ v₁ = 1) (h₁₁ : dist v₁ z₁ = 1)
    (h₁₀ : dist z₁ z₀ = 1) (h₀₀ : dist z₀ v₀ = 1) (hne : v₁ ≠ z₀) (hne' : v₀ ≠ z₁) :
    z₀ - v₀ = z₁ - v₁ := by
  have dsq : ∀ a b : Pt, dist a b = 1 → (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = 1 := by
    intro a b h; rw [← dist_sq_pt, h, one_pow]
  have k1 := dsq _ _ h₀₁
  have k2 := dsq _ _ h₁₁
  have k3 := dsq _ _ h₁₀
  have k4 := dsq _ _ h₀₀
  have r := rhombus_real (x0 := v₁ 0 - v₀ 0) (x1 := v₁ 1 - v₀ 1) (y0 := z₀ 0 - v₀ 0)
    (y1 := z₀ 1 - v₀ 1) (d0 := z₁ 0 - v₀ 0) (d1 := z₁ 1 - v₀ 1)
    (by linear_combination k1) (by linear_combination k4)
    (by linear_combination k2) (by linear_combination k3)
    (by rintro ⟨a, b⟩; exact hne (pt_ext_iff.2 ⟨by linarith, by linarith⟩))
    (by rintro ⟨a, b⟩; exact hne' (pt_ext_iff.2 ⟨by linarith, by linarith⟩))
  rw [pt_ext_iff]; simp only [PiLp.sub_apply]
  constructor <;> linarith [r.1, r.2]

/-- **(R3c) rhombi only near resonance**: two parallel rungs whose K-ends are joined by a good
edge force `τ ≥ cos(β/2)` (their normals are exactly `2θ₀` apart, `θ₀ = arccos τ`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `u_ne`. Difficulty M. -/
theorem R3_resonance (F : DirField X) {v₀ v₁ z₀ z₁ : Pt} (h₀ : IsRung F v₀ z₀)
    (h₁ : IsRung F v₁ z₁) (hpar : z₀ - v₀ = z₁ - v₁) (hne : v₀ ≠ v₁)
    (hg : ang (F.u v₀) (F.u v₁) ≤ beta) : Real.cos (beta / 2) ≤ tau X := by
  have hc := h₀.norm_c
  have hu₀ := F.norm_u h₀.1
  have hu₁ := F.norm_u h₁.1
  have i₀ := h₀.inner_eq
  have i₁ := h₁.inner_eq
  rw [← hpar] at i₁
  have hne' : F.u v₀ ≠ F.u v₁ := u_ne F h₀.1 h₀.2.1 h₁.1 h₁.2.1 hne
  have hi := inner_two_sol hc hu₀ hu₁ i₀ i₁ hne'
  have hb : beta = 1 / 100 := rfl
  have hπ : beta ≤ π := by rw [hb]; linarith [Real.pi_gt_three]
  have hcos := cos_le_inner_of_ang_le hu₀ hu₁ hπ hg
  rw [hi, show beta = 2 * (beta / 2) by ring, Real.cos_two_mul] at hcos
  have hc2 := c5_rhombus
  have h3 : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hτ := h₀.tau_ge
  by_contra hlt; push Not at hlt
  rw [hb] at hc2 hcos hlt
  nlinarith [mul_pos (sub_pos.2 hlt) (show 0 < Real.cos (1 / 100 / 2) + tau X by linarith)]

/-- **[C5] ownership ratios**: rhombus pairs `(4+m)/(2+m) ≤ 4/3` (`m ≥ 4`),
`(3+m)/(2+m) ≤ 4/3` (`m ≥ 2`); both-reach gaps `(1+k+d)/(k+d) ≤ 5/4` (`k, d ≥ 2`).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem ownership_ratios :
    (∀ m : ℝ, 4 ≤ m → (4 + m) / (2 + m) ≤ 4 / 3) ∧ (∀ m : ℝ, 2 ≤ m → (3 + m) / (2 + m) ≤ 4 / 3) ∧
      (∀ k d : ℝ, 2 ≤ k → 2 ≤ d → (1 + k + d) / (k + d) ≤ 5 / 4) := by
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun k d hk hd => ?_⟩
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith

/-- **Ownership count, no rhombi** (`√3/2 + 3β ≤ τ < cos(β/2)`): pure good edges `≤ (5/4)|S|`.

TODO: prove.
What's missing: formalise walks/ownership/charging: each rung owns `k + d` row vertices and
`≤ 1 + k + d` edges with equality only when both walks reach; both-reach gaps are `(1,1)`
(rhombus — excluded by `R3_resonance`) or `(≥2, ≥2)`; unowned vertices carry `≤ 1` edge.
Acceptance: no `sorry`.
Depends on: `T1`, `T2`, `R1_v`, `R1_z`, `R2`, `R2_sym`, `R3_rhombus`, `R3_resonance`,
`ownership_ratios`, `good_subset_T_union_rungs`. Difficulty XL. -/
theorem ownership_rest (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X < Real.cos (beta / 2)) :
    ((goodPure X F).card : ℝ) ≤ 5 / 4 * (Sset X).card := by
  sorry

/-- **Ownership + pairing** (`cos(β/2) ≤ τ ≤ 1`): pure good edges `≤ (4/3)|S|`.

TODO: prove.
What's missing: as `ownership_rest`, plus pairing each rhombus rung with its (non-rhombus)
successor, injectively (`R3_no_three_parallel`, T-cycles have length `≥ 3`); pair ratio `≤ 4/3`.
Acceptance: no `sorry`.
Depends on: `ownership_rest` machinery, `R3_no_three_parallel`, `ownership_ratios`.
Difficulty XL. -/
theorem ownership_res (hX : Normal X) (F : DirField X) (hτ₁ : Real.cos (beta / 2) ≤ tau X)
    (hτ₂ : tau X ≤ 1) : ((goodPure X F).card : ℝ) ≤ 4 / 3 * (Sset X).card := by
  sorry

/-- Region II wiring: `e(S) ≤ goodPure + 71 + cBad`.

TODO: none.
Acceptance: no `sorry` (inherits).
Depends on: `card_good_add_bad`, `card_good_le_pure_add_mixed`, `card_mixedT_le`,
`card_bad_le`. -/
theorem regionII_eS_le (hX : Normal X) (F : DirField X) (hτ : √3 / 2 + 3 * beta ≤ tau X) :
    (eS X : ℝ) ≤ (goodPure X F).card + (cBad + 100) := by
  have h1 : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  have h2 : ((good X F).card : ℝ) ≤ (goodPure X F).card + (mixedT X F).card := by
    exact_mod_cast card_good_le_pure_add_mixed F
  have h3 := card_mixedT_le hX F hτ
  have h4 := card_bad_le hX F
  linarith

/-- **Region II-rest**: `e(S) ≤ (5/4)|S| + C` (gives `36n/25`). -/
theorem regionII_rest (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X < Real.cos (beta / 2)) :
    (eS X : ℝ) ≤ 5 / 4 * (Sset X).card + (cBad + 100) := by
  have := regionII_eS_le hX F hτ₁
  have := ownership_rest hX F hτ₁ hτ₂
  linarith

/-- **Region II-near-resonant**: `e(S) ≤ (4/3)|S| + C` (gives `54n/37`). -/
theorem regionII_res (hX : Normal X) (F : DirField X) (hτ₁ : Real.cos (beta / 2) ≤ tau X)
    (hτ₂ : tau X ≤ 1) : (eS X : ℝ) ≤ 4 / 3 * (Sset X).card + (cBad + 100) := by
  have := regionII_eS_le hX F (c5_rhombus.le.trans hτ₁)
  have := ownership_res hX F hτ₁ hτ₂
  linarith

/-! ## §7.3 Region III: `√3/2 − 2β < τ < √3/2 + 3β` -/

/-- **[C6]** `√3/2 + 3β < cos(π/7)` and `cos(3π/14) < √3/2 − 2β`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S–M. -/
theorem c6 : √3 / 2 + 3 * beta < Real.cos (π / 7) ∧ Real.cos (3 * π / 14) < √3 / 2 - 2 * beta := by
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3' : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpl := Real.pi_lt_d4
  have hpg := Real.pi_gt_d4
  refine ⟨?_, ?_⟩
  · have hc := Real.one_sub_sq_div_two_le_cos (x := π / 7)
    have : (π / 7) ^ 2 < (3.1416 / 7) ^ 2 := by
      apply pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
    rw [beta]; norm_num at this ⊢; nlinarith
  · have hx : |3 * π / 14| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hb := Real.cos_bound hx
    have hlo : (3 * 3.1415 / 14 : ℝ) ^ 2 < (3 * π / 14) ^ 2 := by
      apply pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    have h4 : |3 * π / 14| ^ 4 ≤ 1 := by
      have := pow_le_one₀ (abs_nonneg _) hx (n := 4); exact this
    rw [abs_le] at hb
    rw [beta]; norm_num at hlo ⊢; nlinarith

/-- K-vertices having a rung. -/
def rungVerts (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (Sset X \ Dset X).filter (fun v => ∃ z, IsRung F v z)

/-- `P₁`: rung K-vertices of `Δ₂`-degree exactly 1. -/
def P1set (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (rungVerts X F).filter (fun v => deg2 X v = 1)

/-- Corner vertices: rung K-vertices with a second `Δ₂`-partner. -/
def cornerVerts (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (rungVerts X F).filter (fun v => ¬ deg2 X v = 1)

/-- **Corner lemma**: `v ∈ S ∖ D` with a rung and a second `Δ₂`-partner `w′`:
`∠(u_v, u′) ≥ min(2θ₀, 90° − θ₀) > 2π/7`.

TODO: prove.
What's missing: case `|zw′| = Δ` (other root of `c·u = −τ`, angle `2θ₀`) / `|zw′| ≤ Δ₂`
(`c·u′ > 0`, angle `≥ 90° − θ₀`); numerics from `c6`.
Acceptance: no `sorry`.
Depends on: `exact_identity_b`, `exact_identity_c`, `c6`. Difficulty M–L. -/
theorem corner_lemma (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) {v z w' : Pt} (hr : IsRung F v z) (hw' : w' ∈ X)
    (hw'v : dist v w' = dist2 X) (hne : w' ≠ F.partner v) :
    2 * π / 7 < ang (F.u v) ((dist2 X)⁻¹ • (w' - v)) := by
  sorry

/-- **At most 6 corner vertices** (their normal cones of `K` are wider than `2π/7` and
interior-disjoint).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `corner_lemma`, `ball_polygon_b`, `turning_sum_le` (or disjoint cones). Difficulty M. -/
theorem card_cornerVerts_le (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) : (cornerVerts X F).card ≤ 6 := by
  sorry

/-- A K-vertex has at most two rungs (the positions `v + o_±`), so `#rungs ≤ 2 #rungVerts`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `rung_offset`. Difficulty M. -/
theorem card_rungs_le (hX : Normal X) (F : DirField X) :
    (rungs X F).card ≤ 2 * (rungVerts X F).card := by
  sorry

/-- `rungVerts = P₁ ⊔ corners`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_rungVerts (F : DirField X) :
    (rungVerts X F).card = (P1set X F).card + (cornerVerts X F).card := by
  rw [P1set, cornerVerts, card_filter_add_card_filter_not]

/-- **Region III** (§7.3): `e(S) ≤ |S| + 2|P₁| + C` with `P₁ ⊆ S` of `Δ₂`-degree 1.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `good_subset_T_union_rungs`, `card_tEdges_le`, `card_rungs_le`, `card_rungVerts`,
`card_cornerVerts_le`, `card_good_add_bad`, `card_bad_le`, `two_beta_lt_of`. -/
theorem regionIII (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) :
    ∃ P₁ ⊆ Sset X, (∀ v ∈ P₁, deg2 X v = 1) ∧
      (eS X : ℝ) ≤ (Sset X).card + 2 * P₁.card + (cBad + 100) := by
  refine ⟨P1set X F, fun v hv => ?_, fun v hv => (mem_filter.1 hv).2, ?_⟩
  · exact (mem_sdiff.1 (mem_filter.1 (mem_filter.1 hv).1).1).1
  have hsub := good_subset_T_union_rungs hX F (two_beta_lt_of hτ₁)
  have hg := (card_le_card hsub).trans (card_union_le _ _)
  have hT := card_tEdges_le hX F
  have hR := card_rungs_le hX F
  have hV := card_rungVerts F
  have hC := card_cornerVerts_le hX F hτ₁ hτ₂
  have hgood : ((good X F).card : ℝ) ≤ (Sset X).card + 2 * (P1set X F).card + 12 := by
    exact_mod_cast (show (good X F).card ≤ (Sset X).card + 2 * (P1set X F).card + 12 by omega)
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  linarith

end

end Erdos132Main

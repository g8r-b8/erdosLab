import Erdos.E132Main15Defs

/-!
# Erdős Problem 132, `15/11` theorem — Region III at the exact value `τ = √3/2`

`angle_R4.md` §3.3.  At `τ = √3/2` (`s = 1/2`, `θ₀ = 30°`) a two-rung vertex `v` with rung ends
`a, b` spans an equilateral **triangle** `v a b` of side 1 whose base `ab` is a D–D `δ`-edge.
Goal: `q₂ ≤ #breaks + cBad` (`exact_breaks`), where a **break** is a point of `S` without a
pure right T-neighbour.  Combined with `#T + #breaks ≤ |S| + #mixed` this gives the slot bound
`#T + q₂ ≤ |S| + C` used in `regionIII_key`.

The rigidity chain:
* **Base determines apex** (`base_apex_unique`); bad bases are `≤ cBad` (`card_badBase_le`).
* **(R)** rows are cyclic orders (`rowR_cap_K`) — the cap cut off by a pure K–K T-edge contains no
  other row point.  *Not on the critical path* of the slot formulation (kept for fidelity).
* **(B′)** the pure right/left D-walks from a good base stay on `C(w_v, Δ)`, stepping by the
  rotation `rot α₁` (`Bprime_walk_right`, `Bprime_walk_left`, `Bprime_rot`, `Bprime_span`).
* **(W)** one centre per D-walk (`W_center`); the apex position (`apex_eq`).
* **(Arc)** the short arc of `C(w, Δ₂)` between consecutive apexes lies in `K`, hence in `∂K`
  (`arc_sub_K`), and has single-ray normal cones in its relative interior (`normal_fact`).
* **(Rigid)** the pure right K-walk from an apex moves along that arc in steps of `α₂`
  (`rigid_step`).
* **(Arith)** `jα₂ ≠ kα₁` whenever `kα₁ < π/3` (`arith_no_land`, with `tgap_bounds_exact`), so
  the K-walk breaks strictly before the next apex.
* **(Count)** arcs of different triangles are disjoint (`arc_centre_unique` for different
  centres), giving an injection `triangles → breaks` (`exact_breaks`).

Orientation convention: with inward normal `u ≈ −(p − w)/|p − w|`, "right" (`σ = −1`,
`det2 u (q − p) < 0`) is the **counterclockwise** sense about `w` in both rows.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- A **triangle** at `τ = √3/2`: `v` has good rungs to `a` and `b`, and the base `ab` is a good
pure D-row T-edge with `b` the right neighbour of `a`. -/
def IsTri (F : DirField X) (v a b : Pt) : Prop :=
  IsRung F v a ∧ IsRung F v b ∧ s(v, a) ∈ rungs X F ∧ s(v, b) ∈ rungs X F ∧ RowR F a b ∧
    s(a, b) ∈ good X F

/-! ## Constants at `τ = √3/2` -/

/-- At `τ = √3/2`: `√3/2 < t < √3/2 + 1/(2Δ₂)` (`t < 1`, since `t ≥ 1` forces `τ ≥ t ≥ 1`).

TODO: none — proved.
What's missing: (was) `tau_sub_tgap` (`τ − t = (t² − 1)/(2Δ₂)`); if `t ≥ 1` then `τ ≥ 1`; so
`t < 1` and `0 < (1 − t²)/(2Δ₂) < 1/(2Δ₂)`.
Acceptance: no `sorry`.
Depends on: `tau_sub_tgap`, `Normal.dist2_pos`, `tgap > 0`. Difficulty S. -/
theorem tgap_bounds_exact (hX : Normal X) (hτ : tau X = √3 / 2) :
    √3 / 2 < tgap X ∧ tgap X < √3 / 2 + 1 / (2 * dist2 X) := by
  have hpos := hX.dist2_pos
  have ht0 : 0 < tgap X := by have := (two_of_pos hpos).lt; unfold tgap; linarith
  have e := tau_sub_tgap X
  rw [hτ] at e
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have ht1 : tgap X < 1 := by
    by_contra h; push Not at h
    have : 0 ≤ (tgap X ^ 2 - 1) / (2 * dist2 X) := div_nonneg (by nlinarith) (by positivity)
    linarith
  have hd : 0 < 2 * dist2 X := by positivity
  have e' : tgap X - √3 / 2 = (1 - tgap X ^ 2) / (2 * dist2 X) := by
    have : (tgap X ^ 2 - 1) / (2 * dist2 X) = -((1 - tgap X ^ 2) / (2 * dist2 X)) := by
      rw [← neg_div, neg_sub]
    linarith
  constructor
  · have : 0 < (1 - tgap X ^ 2) / (2 * dist2 X) := div_pos (by nlinarith) hd
    linarith
  · have : (1 - tgap X ^ 2) / (2 * dist2 X) < 1 / (2 * dist2 X) :=
      div_lt_div_of_pos_right (by nlinarith) hd
    linarith

/-- `x ≤ arcsin x ≤ x + x³` for `0 < x ≤ 1/2`. -/
private theorem arcsin_bounds {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 2) :
    x ≤ Real.arcsin x ∧ Real.arcsin x ≤ x + x ^ 3 := by
  have hπ := Real.pi_gt_three
  constructor
  · have hs := Real.sin_arcsin (x := x) (by linarith) (by linarith)
    have := Real.sin_le (Real.arcsin_nonneg.2 h0.le)
    linarith
  · have hx3 : x ^ 3 ≤ 1 / 8 := by
      calc x ^ 3 ≤ (1 / 2) ^ 3 := by gcongr
        _ = 1 / 8 := by norm_num
    rw [Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
      ⟨by nlinarith [pow_pos h0 3], by linarith⟩]
    have := Real.sin_gt_sub_cube (x := x + x ^ 3) (by positivity)
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have : (x + x ^ 3) ^ 3 ≤ 6 * x ^ 3 := by
      have e : (x + x ^ 3) ^ 3 = x ^ 3 * (1 + x ^ 2) ^ 3 := by ring
      rw [e]
      have : (1 + x ^ 2) ^ 3 ≤ 6 := by
        have : 1 + x ^ 2 ≤ 5 / 4 := by linarith
        calc (1 + x ^ 2) ^ 3 ≤ (5 / 4) ^ 3 := by gcongr
          _ ≤ 6 := by norm_num
      have : 0 < x ^ 3 := by positivity
      nlinarith
    linarith

/-- **(Arith)** For `R ≥ 10⁴`, `Δ = R + t` with `√3/2 < t < √3/2 + 1/(2R)`, `α₁ = 2 arcsin(1/(2Δ))`,
`α₂ = 2 arcsin(1/(2R))`: no `j ≥ 1`, `k` with `kα₁ < π/3` have `jα₂ = kα₁`.
(`jα₂ = kα₁ ⇒ k > j ⇒ kα₁ ≥ α₁α₂/(α₂ − α₁) ≥ 1/(t + 1/(23R)) > 1/0.8662 > π/3`.)

TODO: none — proved (with `x ≤ arcsin x ≤ x + x³`: `1/α₁ ≤ R + t`, `1/α₂ ≥ R − 1/(4R)`).
What's missing: (was) bounds on `f(ρ) = 1/α_ρ`: from `sin(α/2) = 1/(2ρ)` and
`x − x³/6 ≤ sin x ≤ x`: `ρ − 1/(23ρ) ≤ f(ρ) ≤ ρ`; then `1/α₁ − 1/α₂ ≤ t + 1/(23R)`,
`t + 1/(23R) < 0.8662 < 3/π` (`Real.pi_lt_d2`).
Acceptance: no `sorry`.
Depends on: `Real.sin_arcsin`, `Real.sin_le`, `Real.sin_gt_sub_cube`-type bounds. Difficulty M. -/
theorem arith_no_land {R t : ℝ} (hR : 10 ^ 4 ≤ R) (ht₁ : √3 / 2 < t) (ht₂ : t < √3 / 2 + 1 / (2 * R))
    {j k : ℕ} (hj : 1 ≤ j) (hk : (k : ℝ) * (2 * Real.arcsin (1 / (2 * (R + t)))) < π / 3) :
    (j : ℝ) * (2 * Real.arcsin (1 / (2 * R))) ≠ k * (2 * Real.arcsin (1 / (2 * (R + t)))) := by
  intro hjk
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by linarith
  set x₁ := 1 / (2 * (R + t)) with hx₁
  set x₂ := 1 / (2 * R) with hx₂
  set A := 2 * Real.arcsin x₁
  set B := 2 * Real.arcsin x₂
  have hx₁0 : 0 < x₁ := by positivity
  have hx₂0 : 0 < x₂ := by positivity
  have hx₂s : x₂ ≤ 1 / 20000 := by
    rw [hx₂, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hx₁s : x₁ ≤ 1 / 2 := by
    rw [hx₁, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨a1, -⟩ := arcsin_bounds hx₁0 hx₁s
  obtain ⟨-, b2⟩ := arcsin_bounds hx₂0 (by linarith)
  have hA0 : 0 < A := by simp only [A]; linarith
  -- `1/A ≤ R + t`
  have hA : 1 / A ≤ R + t := by
    rw [div_le_iff₀ hA0]
    have : (R + t) * (2 * x₁) = 1 := by rw [hx₁]; field_simp
    simp only [A]; nlinarith
  -- `R − 1/(4R) ≤ 1/B`
  have hB0 : 0 < B := by
    have := arcsin_bounds hx₂0 (by linarith); simp only [B]; linarith [this.1]
  have hR' : 0 < R - 1 / (4 * R) := by
    have : 1 / (4 * R) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hB : R - 1 / (4 * R) ≤ 1 / B := by
    rw [le_div_iff₀ hB0]
    have e : 2 * (x₂ + x₂ ^ 3) * (R - 1 / (4 * R)) = 1 - x₂ ^ 4 := by
      rw [hx₂]; field_simp; ring
    have : B ≤ 2 * (x₂ + x₂ ^ 3) := by simp only [B]; linarith
    have := mul_le_mul_of_nonneg_right this hR'.le
    nlinarith [pow_pos hx₂0 4]
  -- `1/A − 1/B ≤ c := t + 1/(4R) < 0.8662`
  set c := t + 1 / (4 * R)
  have hc : c < 0.8662 := by
    have h1 : 1 / (2 * R) ≤ 1 / 20000 := hx₂s
    have h2 : 1 / (4 * R) ≤ 1 / 40000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    simp only [c]; linarith
  have hkey : B - A ≤ c * (A * B) := by
    have h : 1 / A - 1 / B ≤ c := by simp only [c]; linarith
    have : B - A = (1 / A - 1 / B) * (A * B) := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_right h (by positivity)
  -- integrality: `j (B − A) ≥ A`
  have hAB : A < B := by
    have : x₁ < x₂ := by
      rw [hx₁, hx₂]; exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have := Real.arcsin_lt_arcsin (by linarith) this (by linarith)
    simp only [A, B]; linarith
  have hkj : (j : ℝ) + 1 ≤ k := by
    have : j < k := by
      by_contra hle; push Not at hle
      have h1 : (k : ℝ) ≤ j := by exact_mod_cast hle
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
      have : (k : ℝ) * A < j * B := by nlinarith
      linarith
    exact_mod_cast this
  have hjBA : A ≤ j * (B - A) := by
    have : 0 ≤ ((k : ℝ) - j - 1) * A := mul_nonneg (by linarith) hA0.le
    nlinarith
  -- `j B c ≥ 1`, but `j B = k A < π/3` and `c < 3/π`
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have h1 : 1 ≤ j * B * c := by
    have h2 := mul_le_mul_of_nonneg_left hkey hj0
    have : A * 1 ≤ A * (j * B * c) := by
      have : (j : ℝ) * (c * (A * B)) = A * (j * B * c) := by ring
      linarith
    exact le_of_mul_le_mul_left this hA0
  have hπ := Real.pi_lt_d2
  have hkA : (k : ℝ) * A < π / 3 := hk
  have hjB : (j : ℝ) * B < π / 3 := by linarith
  have hjB0 : 0 ≤ (j : ℝ) * B := by positivity
  have e1 : (j : ℝ) * B * c ≤ (j * B) * 0.8662 := mul_le_mul_of_nonneg_left hc.le hjB0
  have e2 : (j : ℝ) * B * 0.8662 ≤ π / 3 * 0.8662 := by linarith
  linarith

/-! ## Private helpers (rung pairs) -/

/-- `det(a, c b) = c det(a, b)`. -/
private theorem det2_smul_right' (a b : Pt) (c : ℝ) : det2 a (c • b) = c * det2 a b := by
  simp only [det2_pt, PiLp.smul_apply, smul_eq_mul]; ring

/-- `det(a, b^⊥) = a·b`. -/
private theorem det2_perp_right' (a b : Pt) : det2 a (perp b) = inner ℝ a b := by
  rw [det2_pt, inner_pt]; simp

/-- Two rungs `z ≠ z′` of `v`: `z − z′ = 2sκ u_v^⊥` and `z′ − v = −τu_v − κs u_v^⊥`, `κ = ±1`. -/
private theorem rung_pair_kappa (F : DirField X) {v z z' : Pt} (hr : IsRung F v z)
    (hr' : IsRung F v z') (hne : z ≠ z') :
    ∃ κ : ℝ, (κ = 1 ∨ κ = -1) ∧ z - z' = (2 * sOff X * κ) • perp (F.u v) ∧
      z' - v = (-tau X) • F.u v + (-κ * sOff X) • perp (F.u v) := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F hr
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F hr'
  have hne12 : σ₁ ≠ σ₂ := by
    rintro rfl; apply hne
    have : z - v = z' - v := by rw [e₁, e₂]
    exact sub_left_injective this
  have hz : z - z' = (z - v) - (z' - v) := by abel
  rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl
  · exact absurd rfl hne12
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rw [hz, e₁, e₂, show 2 * sOff X * 1 = 1 * sOff X - (-1) * sOff X by ring, sub_smul]; abel
    · rw [e₂]; try ring_nf
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · rw [hz, e₁, e₂, show 2 * sOff X * (-1) = (-1) * sOff X - 1 * sOff X by ring, sub_smul]; abel
    · rw [e₂]; try ring_nf
  · exact absurd rfl hne12

/-- The side of `2sκ u^⊥` seen from `u′ ≈ u` has the sign of `κ`. -/
private theorem side_sign {u u' : Pt} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (huu : ‖u - u'‖ ≤ 1 / 100)
    {s κ σ : ℝ} (hs : 0 < s) (h : 0 < σ * det2 u' ((2 * s * κ) • perp u)) : 0 < σ * κ := by
  have huu' : 0 < inner ℝ u' u := by
    have e := @norm_sub_sq_real _ _ _ u u'
    rw [hu, hu', real_inner_comm] at e
    nlinarith [norm_nonneg (u - u')]
  rw [det2_smul_right', det2_perp_right'] at h
  by_contra h'; push Not at h'
  have : σ * (2 * s * κ * inner ℝ u' u) = (σ * κ) * (2 * s * inner ℝ u' u) := by ring
  have h2 : 0 ≤ 2 * s * inner ℝ u' u := by positivity
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h' h2]

/-- `u·u' > 0` for unit vectors with `|u − u'| ≤ 1/100`. -/
private theorem inner_pos_of_close {u u' : Pt} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (huu : ‖u - u'‖ ≤ 1 / 100) : 0 < inner ℝ u' u := by
  have e := @norm_sub_sq_real _ _ _ u u'
  rw [hu, hu', real_inner_comm] at e
  nlinarith [norm_nonneg (u - u')]

/-- Two K-vertices whose rungs to a common end `b` have the same offset coefficient (in their own
frames) and nearly equal normals coincide. -/
private theorem eq_of_same_offset (hX : Normal X) (F : DirField X) {v v' b : Pt}
    (hv : IsRung F v b) (hv' : IsRung F v' b) (huu : ‖F.u v' - F.u v‖ ≤ 2 / 100) {c : ℝ}
    (hc : |c| ≤ 1) (hτ : |tau X| ≤ 1)
    (h : b - v = (-tau X) • F.u v + c • perp (F.u v))
    (h' : b - v' = (-tau X) • F.u v' + c • perp (F.u v')) : v = v' := by
  refine eq_of_dist_lt_one hX.minDist_eq hv.memX.1 hv'.memX.1 ?_
  have e : v - v' = (b - v') - (b - v) := by abel
  rw [dist_eq_norm, e, h, h']
  have : ((-tau X) • F.u v' + c • perp (F.u v')) - ((-tau X) • F.u v + c • perp (F.u v)) =
      (-tau X) • (F.u v' - F.u v) + c • perp (F.u v' - F.u v) := by
    rw [perp_sub, smul_sub, smul_sub]; abel
  rw [this]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_smul, norm_smul, norm_perp, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  nlinarith [norm_nonneg (F.u v' - F.u v), abs_nonneg c, abs_nonneg (tau X)]

/-- At `τ = √3/2`, `s = 1/2`. -/
private theorem sOff_exact (hτ : tau X = √3 / 2) : sOff X = 1 / 2 := by
  unfold sOff
  rw [hτ, div_pow, Real.sq_sqrt (by norm_num)]
  rw [show (1 : ℝ) - 3 / 2 ^ 2 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ## Triangles and bases -/

/-- At `τ = √3/2` every two-rung vertex spans a triangle over a unit D–D base, which is bad or
(in one orientation) a good pure right T-edge.

TODO: none — proved.
What's missing: (was) `rung_offset` with `sOff = 1/2` gives `z − z′ = ±perp u_v` (`‖·‖ = 1`), so
`s(z, z′) ∈ edges`; if good, `good_dichotomy` (both ends in `D`, so no rung) makes it a T-edge,
and `tstep_flip`/`T2` orient it as `RowR`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `good_dichotomy`, `tstep_flip`, `T2`, `tgap_bounds_exact`.
Difficulty M. -/
theorem tri_of_twoRung (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v : Pt}
    (hv : v ∈ twoRungVerts X F) :
    ∃ a b, IsRung F v a ∧ IsRung F v b ∧ s(v, a) ∈ rungs X F ∧ s(v, b) ∈ rungs X F ∧ a ≠ b ∧
      s(a, b) ∈ edges X ∧ (s(a, b) ∈ bad X F ∨ IsTri F v a b) := by
  obtain ⟨z, z', hne, h1, h2, g1, g2⟩ := (mem_filter.1 hv).2
  obtain ⟨κ, hκ, hd, -⟩ := rung_pair_kappa F h1 h2 hne
  have hs := sOff_exact hτ
  have hdist : dist z z' = 1 := by
    rw [dist_eq_norm, hd, norm_smul, norm_perp, F.norm_u h1.1, hs]
    rcases hκ with rfl | rfl <;> norm_num
  have hz := h1.2.2.1
  have hz' := h2.2.2.1
  have hzD := h1.2.2.2.1
  have hz'D := h2.2.2.2.1
  have hedge : s(z, z') ∈ edges X := by
    refine mem_filter.2 ⟨?_, ?_⟩
    · simp only [pairsS, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
      exact ⟨⟨hz, hz'⟩, hne⟩
    · show dist z z' = minDist X
      rw [hX.minDist_eq, hdist]
  by_cases hgood : s(z, z') ∈ good X F
  · have hg : ang (F.u z) (F.u z') ≤ beta := (mem_filter.1 hgood).2 z z' rfl
    have hτ' : 2 * beta < tau X := by
      rw [hτ]
      have : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      unfold beta; linarith
    have hT : IsTEdge F z z' := by
      rcases good_dichotomy hX F hτ' hz hz' hdist hg with h | h | h
      · exact h
      · exact absurd hzD h.2.1
      · exact absurd hz'D h.2.1
    have hl := lagrange (z' - z) (F.u z)
    rw [F.norm_u' hz, ← dist_eq_norm, dist_comm z' z, hdist] at hl
    have ha := hT.2.1
    have hβ : beta = 1 / 100 := rfl
    rw [hβ] at ha
    have hDD : (z ∈ Dset X ↔ z' ∈ Dset X) := ⟨fun _ => hz'D, fun _ => hzD⟩
    rcases lt_or_gt_of_ne (show det2 (F.u z) (z' - z) ≠ 0 by
      intro h0; rw [h0] at hl; nlinarith [hT.1]) with hb | hb
    · exact ⟨z, z', h1, h2, g1, g2, hne, hedge, Or.inr ⟨h1, h2, g1, g2,
        ⟨⟨hz, hz', hdist, hg, hT, by linarith⟩, hDD⟩, hgood⟩⟩
    · have := tstep_flip hz hz' hdist hg hT.1 hT.2.1
      have hb' : det2 (F.u z') (z - z') < 0 := by nlinarith
      have hg' : ang (F.u z') (F.u z) ≤ beta := by
        rw [ang, InnerProductGeometry.angle_comm]; exact hg
      have hd' : dist z' z = 1 := by rw [dist_comm]; exact hdist
      have hR : RowR F z' z := ⟨⟨hz', hz, hd', hg', hT.symm, by linarith⟩, hDD.symm⟩
      have he' : s(z', z) ∈ edges X := Sym2.eq_swap ▸ hedge
      have hgood' : s(z', z) ∈ good X F := Sym2.eq_swap ▸ hgood
      exact ⟨z', z, h2, h1, g2, g1, hne.symm, he', Or.inr ⟨h2, h1, g2, g1, hR, hgood'⟩⟩
  · exact ⟨z, z', h1, h2, g1, g2, hne, hedge,
      Or.inl (mem_filter.2 ⟨hedge, fun h => hgood (mem_filter.2 ⟨hedge, h⟩)⟩)⟩

/-- **Base determines apex**: the other point `v̄ = z′ − τu + ½u^⊥` of `C(z,1) ∩ C(z′,1)` violates
Lemma 3.2(a) (`(v̄ − z′)·u_{z′} ≤ −τ cos β + ½ sin β < 0`), so two vertices with good rungs to
the same two ends coincide.

TODO: none — proved (no mirror argument: goodness at `a` gives `|u_v − u_{v′}| ≤ 2β`, hence the
same side `κ = κ′` of `a − b`, and then `|v − v′| ≤ 2β(τ + s) < 1`).
What's missing: (was) two circles of radius 1 meet in `≤ 2` points; the mirror apex contradicts
`exact_identity_a` at `z′` (`u_{z′}` within `β` of `u_v`).
Acceptance: no `sorry`.
Depends on: `rung_offset`, `exact_identity_a`, `RungM.ang`. Difficulty M. -/
theorem base_apex_unique (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v v' a b : Pt}
    (hab : a ≠ b) (h₁ : IsRung F v a) (h₂ : IsRung F v b) (h₃ : IsRung F v' a)
    (h₄ : IsRung F v' b) (g₁ : s(v, a) ∈ rungs X F) (g₂ : s(v, b) ∈ rungs X F)
    (g₃ : s(v', a) ∈ rungs X F) (g₄ : s(v', b) ∈ rungs X F) : v = v' := by
  obtain ⟨κ, hκ, hd, ho⟩ := rung_pair_kappa F h₁ h₂ hab
  obtain ⟨κ', hκ', hd', ho'⟩ := rung_pair_kappa F h₃ h₄ hab
  have hs := sOff_exact hτ
  have hga : ang (F.u v) (F.u a) ≤ beta := (mem_filter.1 (mem_filter.1 g₁).1).2 v a rfl
  have hga' : ang (F.u v') (F.u a) ≤ beta := (mem_filter.1 (mem_filter.1 g₃).1).2 v' a rfl
  have hu := F.norm_u h₁.1
  have hu' := F.norm_u h₃.1
  have hua := F.norm_u h₁.2.2.1
  have hb : beta = 1 / 100 := rfl
  have h1 : ‖F.u v - F.u a‖ ≤ 1 / 100 := hb ▸ (norm_sub_le_angR hu hua).trans hga
  have h2 : ‖F.u v' - F.u a‖ ≤ 1 / 100 := hb ▸ (norm_sub_le_angR hu' hua).trans hga'
  have hs0 : (0 : ℝ) < sOff X := by rw [hs]; norm_num
  -- the sign of `det(u_a, a − b)` is `κ` and `κ′`
  have e2 : 0 < κ' * det2 (F.u a) ((2 * sOff X * κ') • perp (F.u v')) := by
    rw [det2_smul_right', det2_perp_right']
    have := inner_pos_of_close hu' hua h2
    have hk : κ' * (2 * sOff X * κ' * inner ℝ (F.u a) (F.u v')) =
        (κ' * κ') * (2 * sOff X * inner ℝ (F.u a) (F.u v')) := by ring
    rw [hk, show κ' * κ' = 1 by rcases hκ' with rfl | rfl <;> norm_num, one_mul]
    positivity
  rw [← hd', hd] at e2
  have e1 := side_sign hu hua h1 hs0 e2
  have hκκ : κ = κ' := by
    rcases hκ with rfl | rfl <;> rcases hκ' with rfl | rfl <;> first | rfl | nlinarith
  subst hκκ
  have hw : ‖F.u v' - F.u v‖ ≤ 2 / 100 := by
    have := norm_sub_le (F.u v' - F.u a) (F.u v - F.u a)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have h3 : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine eq_of_same_offset hX F h₂ h₄ hw (c := -κ * sOff X) ?_ ?_ ho ho'
  · rw [hs]; rcases hκ with rfl | rfl <;> norm_num
  · rw [hτ, abs_le]; constructor <;> nlinarith [Real.sqrt_nonneg 3]

/-- **(R)** rows are cyclic orders (K-row): the cap of `K` cut off by the line of a pure K–K
T-edge `pq` (on the side away from `u_p`) lies within distance `< 1` of `p` or `q`.  Hence it
contains no other point of `X`.  *Not used by the slot formulation.*

TODO: prove.
What's missing: coordinates `p = (0,0)`, `q = (1,0)`, `u_p = (sin ε, cos ε)`,
`u_q = (−sin ε′, cos ε′)` with `ε, ε′ ∈ (0, arcsin β)`; the cap lies in the triangle
`{y ≤ 0, y ≥ −x tan ε, y ≥ (x − 1) tan ε′}`, every point of which is within
`√(1/4 + tan²(arcsin β)) < 1` of `p` or `q`.
Acceptance: no `sorry`.
Depends on: `neg_mem_normalCone`, `T2`. Difficulty M. -/
theorem rowR_cap_K (hX : Normal X) (F : DirField X) {p q n : Pt} (h : RowR F p q)
    (hpD : p ∉ Dset X) (hn : ‖n‖ = 1) (hnq : inner ℝ n (q - p) = 0)
    (hnu : 0 < inner ℝ n (F.u p)) {x : Pt} (hx : x ∈ KBall X) (hcap : inner ℝ (x - p) n ≤ 0) :
    dist x p < 1 ∨ dist x q < 1 := by
  sorry

/-! ## (B′), (W) -/

/-- **(B′)** the pure right D-walk from the right base end `b` of a triangle stays on
`C(w_v, Δ)`.

TODO: prove.
What's missing: induction on `k`; interior walk vertices have normal cones of `conv X` in the
cap of radius `arcsin β` around `u` (inwardness against both neighbours); the diametral
direction `ŵ_k = (w − z_k)/Δ` is such a normal, so `η = (z_{k+1} − z_k)·ŵ_k < sin(2 arcsin β)`
`< t`; `lemmaB`-type identity `|z_{k+1}w|² = 1 + Δ² − 2Δη > Δ₂²` forces `|z_{k+1}w| = Δ`.
Acceptance: no `sorry`.
Depends on: `exact_identity_a`, `dist_le_dist2`, `tgap_bounds_exact`. Difficulty L. -/
theorem Bprime_walk_right (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) :
    ∀ k ≤ N, dist (z k) (F.partner v) = diam X := by
  sorry

/-- **(B′)** the pure left D-walk from the left base end `a` stays on `C(w_v, Δ)`.

TODO: prove.
What's missing: mirror image of `Bprime_walk_right`.
Acceptance: no `sorry`.
Depends on: as `Bprime_walk_right`. Difficulty L. -/
theorem Bprime_walk_left (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = a)
    (hstep : ∀ k < N, RowR F (z (k + 1)) (z k)) :
    ∀ k ≤ N, dist (z k) (F.partner v) = diam X := by
  sorry

/-- **(B′)** consecutive walk vertices differ by the rotation `rot α₁` about `w = w_v`
(counterclockwise = right), starting with the base itself.

TODO: prove.
What's missing: two points of `C(w,Δ) ∩ C(z_k, 1)` are `w + rot (±α₁) (z_k − w)`; the right
T-neighbour is the counterclockwise one because `ŵ_k` is within `arcsin β` of `u_{z_k}`.
Acceptance: no `sorry`.
Depends on: `Bprime_walk_right`, `rot`, `alpha1`. Difficulty L. -/
theorem Bprime_rot (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) :
    b - F.partner v = rot (alpha1 X) (a - F.partner v) ∧
      ∀ k < N, z (k + 1) - F.partner v = rot (alpha1 X) (z k - F.partner v) := by
  sorry

/-- **(B′)** span: a walk of `N` right steps from the base satisfies `(N + 1)·α₁ ≤ π/3`
(points of `X` are `≤ Δ` apart; chord `2Δ sin(θ/2) ≤ Δ`), so D-walks are paths.

TODO: prove.
What's missing: `Bprime_rot` iterated: `z_N − w = rot((N+1)α₁)(a − w)`; `|z_N − a| ≤ Δ`.
Acceptance: no `sorry`.
Depends on: `Bprime_rot`, `dist_le_diam`. Difficulty M. -/
theorem Bprime_span (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) : ((N : ℝ) + 1) * alpha1 X ≤ π / 3 := by
  sorry

/-- **(W)** one centre per D-walk: if the base of a second triangle `A′` lies on the right walk
from the base of `A`, the two apexes have the same `Δ₂`-partner.

TODO: prove.
What's missing: both centres are at distance `Δ` from `a′, b′`; distinct centres are mirror
images in the line `a′b′`, and `a·e = ±1/(2Δ)` (second referee) gives `a·a* < 0`, contradicting
`exact_identity_a` at `b′`.
Acceptance: no `sorry`.
Depends on: `Bprime_walk_right`, `exact_identity_a`. Difficulty M–L. -/
theorem W_center (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b v' a' b' : Pt}
    (ht : IsTri F v a b) (ht' : IsTri F v' a' b') (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) (hk : ∃ k ≤ N, z k = a') :
    F.partner v = F.partner v' := by
  sorry

/-- The apex of a triangle sits on `C(w, Δ₂)` on the bisector of its base:
`v = w + (Δ₂/|m − w|)(m − w)` with `m` the base midpoint.

TODO: prove.
What's missing: `|va| = |vb| = 1`, `|aw| = |bw| = Δ`: `v, w` both on the perpendicular
bisector of `ab`; `|vw| = Δ₂ < |mw|` and `v` on the segment side (`exact_identity_c`).
Acceptance: no `sorry`.
Depends on: `rung_offset`, `IsRung`. Difficulty M. -/
theorem apex_eq (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) :
    v = F.partner v + (dist2 X / ‖midpoint ℝ a b - F.partner v‖) •
      (midpoint ℝ a b - F.partner v) := by
  sorry

/-! ## (Arc), (Rigid) -/

/-- **(Arc)** spindle convexity: if two points of `C(w, Δ₂)` (`w ∈ X`) at angles `θ₁ ≤ θ₂`,
`θ₂ − θ₁ < π`, lie in `K`, the whole short arc between them lies in `K`, hence in `∂K`.

TODO: prove.
What's missing: for `x ∈ X`, `D(x,Δ₂) ∩ C(w,Δ₂) = {θ : cos(θ − θ_x) ≥ |wx|/(2Δ₂)}` is an arc
of width `≤ π` (or everything if `x = w`) containing `θ₁, θ₂`, so containing `[θ₁, θ₂]`; frontier
since `w ∈ X` and the point is on `C(w,Δ₂)`.
Acceptance: no `sorry`.
Depends on: `mem_KBall`, `dirVec`, `Real.cos` monotonicity. Difficulty M. -/
theorem arc_sub_K (hX : Normal X) {w : Pt} (hw : w ∈ X) {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂)
    (hθπ : θ₂ - θ₁ < π) (h₁ : w + dist2 X • dirVec θ₁ ∈ KBall X)
    (h₂ : w + dist2 X • dirVec θ₂ ∈ KBall X) :
    ∀ θ ∈ Set.Icc θ₁ θ₂, w + dist2 X • dirVec θ ∈ KBall X ∩ frontier (KBall X) := by
  sorry

/-- **(Rigid), normal fact**: at a relative-interior point of an arc of `C(w, Δ₂)` contained in
`K`, the outer normal cone is the single ray through `dirVec θ`.

TODO: prove.
What's missing: `ν` normal ⇒ `(y − p)·ν ≤ 0` for `y` on the arc on both sides of `p`; divide by
the arc parameter and let it tend to `0` (or use the two chords): `ν ⊥ tangent`, and
`(w − p)·ν ≤ 0` fixes the sign.
Acceptance: no `sorry`.
Depends on: `normalCone`, `dirVec`. Difficulty M. -/
theorem normal_fact (hX : Normal X) {w : Pt} {θ₁ θ θ₂ : ℝ} (h₁ : θ₁ < θ) (h₂ : θ < θ₂)
    (harc : ∀ φ ∈ Set.Icc θ₁ θ₂, w + dist2 X • dirVec φ ∈ KBall X) {ν : Pt}
    (hν : ν ∈ normalCone (KBall X) (w + dist2 X • dirVec θ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ν = c • dirVec θ := by
  sorry

/-- **(Rigid), step**: on an arc `[θ, θ₂]` of `C(w, Δ₂)` inside `K`, with `u = −dirVec θ` at the
current K-row point and room for one step (`θ + α₂ ≤ θ₂`), the pure right K T-neighbour is the
next arc point `w + Δ₂ dirVec(θ + α₂)`.

TODO: prove.
What's missing: coordinates `(r, u)`; `v_{i+1} − v_i = (cos ψ, sin ψ)` with `ψ < arcsin β`;
`v_{i+1} ∈ D(w,Δ₂)` forces `ψ ≥ ψ* = arcsin(1/(2Δ₂))`; if `ψ > ψ*`, the normal `n = u_{v_{i+1}}`
(`|φ| ≤ β`) violates `v_i ∈ K` or `v* ∈ K` (both terms negative).  Float check B2.
Acceptance: no `sorry`.
Depends on: `arc_sub_K`, `neg_mem_normalCone`, `IsSideT`. Difficulty L. -/
theorem rigid_step (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {w : Pt} (hw : w ∈ X)
    {θ θ₂ : ℝ} (harc : ∀ φ ∈ Set.Icc θ θ₂, w + dist2 X • dirVec φ ∈ KBall X)
    (hroom : θ + alpha2 X ≤ θ₂) (hv : w + dist2 X • dirVec θ ∈ Sset X)
    (hvD : w + dist2 X • dirVec θ ∉ Dset X) (hu : F.u (w + dist2 X • dirVec θ) = -dirVec θ)
    {q : Pt} (hq : RowR F (w + dist2 X • dirVec θ) q) :
    q = w + dist2 X • dirVec (θ + alpha2 X) := by
  sorry

/-- **(Count), different centres**: a point in the relative interior of an arc of `C(w, Δ₂)`
inside `K` cannot be an endpoint of a nondegenerate arc of `C(w′, Δ₂)` inside `K` unless
`w = w′` (near such a point `∂K` is the arc of `C(w,Δ₂)`, and two circles share `≤ 2` points).

TODO: prove.
What's missing: points of the `w′`-arc near `p` are in `∂K` (`w′ ∈ X`); near `p` every boundary
point of `K` lies on `C(w, Δ₂)` (inside `D(w,Δ₂)` near `p` is interior to the circular segment
`conv(arc) ⊆ K`); infinitely many common points of two circles force `w = w′`.
Acceptance: no `sorry`.
Depends on: `arc_sub_K`, `KBall_convex`. Difficulty M–L. -/
theorem arc_centre_unique (hX : Normal X) {w w' : Pt} (hw : w ∈ X) (hw' : w' ∈ X)
    {θ₁ θ θ₂ φ₁ φ₂ : ℝ} (h₁ : θ₁ < θ) (h₂ : θ < θ₂)
    (harc : ∀ ψ ∈ Set.Icc θ₁ θ₂, w + dist2 X • dirVec ψ ∈ KBall X) (hφ : φ₁ < φ₂)
    (harc' : ∀ ψ ∈ Set.Icc φ₁ φ₂, w' + dist2 X • dirVec ψ ∈ KBall X)
    (hp : w + dist2 X • dirVec θ = w' + dist2 X • dirVec φ₁ ∨
      w + dist2 X • dirVec θ = w' + dist2 X • dirVec φ₂) : w = w' := by
  sorry

/-! ## (Count) -/

/-- Triangles over **bad** bases number at most `cBad` (base determines apex).

TODO: none — proved.
What's missing: (was) the map `v ↦ base` into `bad X F` is injective by `base_apex_unique`.
Acceptance: no `sorry`.
Depends on: `tri_of_twoRung`, `base_apex_unique`, `card_bad_le`. Difficulty M. -/
theorem card_badBase_le (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) :
    (((twoRungVerts X F).filter (fun v => ¬ ∃ a b, IsTri F v a b)).card : ℝ) ≤ cBad := by
  classical
  set V := (twoRungVerts X F).filter (fun v => ¬ ∃ a b, IsTri F v a b)
  let Q : Pt → Pt × Pt → Prop := fun v ab => IsRung F v ab.1 ∧ IsRung F v ab.2 ∧
    s(v, ab.1) ∈ rungs X F ∧ s(v, ab.2) ∈ rungs X F ∧ ab.1 ≠ ab.2 ∧ s(ab.1, ab.2) ∈ bad X F
  have hQ : ∀ v ∈ V, ∃ ab, Q v ab := by
    intro v hv
    obtain ⟨hv2, hnt⟩ := mem_filter.1 hv
    obtain ⟨a, b, h1, h2, g1, g2, hab, -, hbt⟩ := tri_of_twoRung hX F hτ hv2
    rcases hbt with hb | ht
    · exact ⟨(a, b), h1, h2, g1, g2, hab, hb⟩
    · exact absurd ⟨a, b, ht⟩ hnt
  let f : Pt → Sym2 Pt := fun v => if h : ∃ ab, Q v ab then s(h.choose.1, h.choose.2) else s(0, 0)
  have hf : ∀ v ∈ V, ∃ ab, Q v ab ∧ f v = s(ab.1, ab.2) := by
    intro v hv
    have h := hQ v hv
    exact ⟨h.choose, h.choose_spec, dif_pos h⟩
  have hmaps : ∀ v ∈ V, f v ∈ bad X F := by
    intro v hv
    obtain ⟨ab, hq, he⟩ := hf v hv
    rw [he]; exact hq.2.2.2.2.2
  have hinj : Set.InjOn f ↑V := by
    intro v hv v' hv' e
    obtain ⟨⟨a, b⟩, ⟨h1, h2, g1, g2, hab, -⟩, he⟩ := hf v hv
    obtain ⟨⟨a', b'⟩, ⟨h1', h2', g1', g2', -, -⟩, he'⟩ := hf v' hv'
    rw [he, he'] at e
    rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact base_apex_unique hX F hτ hab h1 h2 h1' h2' g1 g2 g1' g2'
    · exact base_apex_unique hX F hτ hab h1 h2 h2' h1' g1 g2 g2' g1'
  have h1 := card_le_card_of_injOn f hmaps hinj
  have h2 := card_bad_le hX F
  have : (V.card : ℝ) ≤ (bad X F).card := by exact_mod_cast h1
  linarith

/-- **(Count)** at `τ = √3/2`: `q₂ ≤ #breaks + cBad`.
Each good-base triangle `A` is charged to a break: the K-break `b_{AB} ∈ [v_A, v_B)` if `A` has a
successor `B` on its D-walk ((W), (Arc), (Rigid), (Arith)), else the right end of its D-walk (a
D-break, (B′)).  K-breaks of different triangles lie on disjoint half-open arcs
(`arc_centre_unique`, one triangle per apex); D-breaks of different walks are distinct
(`rowR_inj`); K- and D-breaks differ (`∉ D` vs `∈ D`).

TODO: prove.
What's missing: the injection and its well-definedness (walk iteration via `rowR_fun`, a
`Nat.find` for the first break), assembling the chain lemmas above.
Acceptance: no `sorry`.
Depends on: `card_badBase_le`, `tri_of_twoRung`, `Bprime_walk_right`, `Bprime_rot`,
`Bprime_span`, `W_center`, `apex_eq`, `arc_sub_K`, `normal_fact`, `rigid_step`,
`arith_no_land`, `tgap_bounds_exact`, `arc_centre_unique`, `rowR_fun`, `rowR_inj`.
Difficulty XL. -/
theorem exact_breaks (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) :
    ((twoRungVerts X F).card : ℝ) ≤ (breaks X F).card + cBad := by
  sorry

end

end Erdos132Main

import Erdos.E132Main15Defs

/-!
# Erdős Problem 132, `15/11` theorem — Region II: `e(S) ≤ |S| + |Q| + C`

`angle_R4.md` §2, for `√3/2 + 3β ≤ τ ≤ 1` (the case `τ > 1` is `regionII_high` of the `54/37`
development).  Replaces the ownership walks of §7.2 of WRITEUP_A2:

* **Lemma A** (corner lemma, all `τ ≤ 1`): a second `Δ₂`-partner `w′` of a rung K-end `v` is
  either of **type (i)** (`|zw′| ≠ Δ`; then `∠(u_v, u′) > π/2 − θ₀ > π/3`) or of **type (ii)**
  (`|zw′| = Δ`; then `u′` is the reflection of `u_v` in `ℝc`, `u_v·u′ = 2τ² − 1`).
  At most 5 vertices have a type-(i) partner (disjoint normal cones wider than `π/3`).
* **Lemma B**: `|yw|² = Δ² + 1 − 2Δη`; small `η` forces `|yw| = Δ`.
* **Lemma C**: the rung partner `z` of a *double* vertex (type-(ii) partner) has no T-neighbour.
* **Count**: `#T + #doubleEnds ≤ |S|`, `#rungs ≤ #doubleEnds + |P₁| + 5`, so
  `e(S) ≤ #T + #rungs + cBad ≤ |S| + |P₁| + 5 + cBad`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Definitions -/

/-- `v` is a **double** vertex with rung `z`: some second `Δ₂`-partner `w′ ≠ w_v` has
`|zw′| = Δ` (type (ii) of Lemma A). -/
def IsDouble (F : DirField X) (v z : Pt) : Prop :=
  IsRung F v z ∧ ∃ w' ∈ X, dist v w' = dist2 X ∧ w' ≠ F.partner v ∧ dist z w' = diam X

/-- Rung K-ends with a **type-(i)** second partner (`|zw′| ≠ Δ`). -/
def typeOneVerts (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (rungVerts X F).filter (fun v => ∃ z w', IsRung F v z ∧ w' ∈ X ∧ dist v w' = dist2 X ∧
    w' ≠ F.partner v ∧ dist z w' ≠ diam X)

/-- D-ends of good rungs whose K-end is double. -/
def doubleEnds (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (Sset X).filter (fun z => ∃ v, IsDouble F v z ∧ s(v, z) ∈ rungs X F)

/-! ## Lemma B -/

/-- **Lemma B, identity**: `|yw|² = |zw|² + |yz|² − 2 (y − z)·(w − z)`.

TODO: none — proved.
What's missing: expand norms (`dist_eq_norm`, `norm_sub_sq_real`).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lemmaB_sq (z w y : Pt) :
    dist y w ^ 2 = dist z w ^ 2 + dist y z ^ 2 - 2 * inner ℝ (y - z) (w - z) := by
  rw [dist_eq_norm y w, dist_eq_norm z w, dist_eq_norm y z,
    show y - w = (y - z) - (w - z) by abel, norm_sub_rev z w, @norm_sub_sq_real]
  ring

/-- **Lemma B**: if `|zw| = Δ`, `|yz| = 1` and `η' := (y − z)·(w − z) < (Δ² − Δ₂² + 1)/2`
(i.e. `η < (Δ² − Δ₂² + 1)/(2Δ)` for the unit direction), then `|yw| = Δ`.

TODO: none — proved.
What's missing: `lemmaB_sq` gives `|yw|² > Δ₂²`, so `|yw| > Δ₂`; there are no distances in
`(Δ₂, Δ)` (`dist_le_dist2`), so `|yw| = Δ`.
Acceptance: no `sorry`.
Depends on: `lemmaB_sq`, `dist_le_dist2`. Difficulty S–M. -/
theorem lemmaB (hX : Normal X) {z w y : Pt} (hw : w ∈ X) (hy : y ∈ X) (hzw : dist z w = diam X)
    (hzy : dist y z = 1) (hη : inner ℝ (y - z) (w - z) < (diam X ^ 2 - dist2 X ^ 2 + 1) / 2) :
    dist y w = diam X := by
  have hsq := lemmaB_sq z w y
  rw [hzw, hzy] at hsq
  by_contra hne
  have hle := dist_le_dist2 hy hw hne
  have h2 : dist y w ^ 2 ≤ dist2 X ^ 2 := pow_le_pow_left₀ dist_nonneg hle 2
  linarith

/-! ## Lemma A -/

/-- **Lemma A (i)** in Region II: a type-(i) partner direction makes an angle `> π/3` with `u_v`
(`u_v·u′ < √(1 − τ²) < 1/2`).

TODO: none — proved.
What's missing: as the second branch of `corner_lemma`: redirect `F` to `w′`
(`DirField.redirect`), `exact_identity_b` gives `c·u′ > 0`, `inner_lt_sOff` gives
`u_v·u′ < √(1 − τ²)`, and `√(1 − τ²) < 1/2 = cos(π/3)` as `τ > √3/2`; `lt_ang_of_inner_lt`.
Acceptance: no `sorry`.
Depends on: `DirField.redirect`, `exact_identity_b`, `inner_lt_sOff`, `lt_ang_of_inner_lt`.
Difficulty M. -/
theorem lemmaA_i (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v z w' : Pt} (hr : IsRung F v z) (hw' : w' ∈ X)
    (hw'v : dist v w' = dist2 X) (hne : w' ≠ F.partner v) (hzw : dist z w' ≠ diam X) :
    π / 3 < ang (F.u v) ((dist2 X)⁻¹ • (w' - v)) := by
  have hv := hr.1
  have hvD := hr.2.1
  have hpos := hr.two.1.pos
  set F' := F.redirect hw' hw'v hvD
  have hp' : F'.partner v = w' := F.redirect_partner hw' hw'v hvD
  have hu'eq : F'.u v = (dist2 X)⁻¹ • (w' - v) := by
    unfold DirField.u; rw [hp', hw'v]
  rw [← hu'eq]
  have hc := hr.norm_c
  have hu := F.norm_u hv
  have hu' := F'.norm_u hv
  have i₀ := hr.inner_eq
  have hπ := Real.pi_gt_three
  have h3 : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hτ0 : 0 < tau X := by unfold beta at hτ₁; linarith
  have hb := exact_identity_b F' hv hvD hr.memX.2
  rw [hp'] at hb
  have ha : 0 < inner ℝ (z - v) (F'.u v) := by
    rcases hb with hb | hb
    · refine lt_of_lt_of_le ?_ hb
      rw [dist_comm, hr.2.2.2.2.1]; positivity
    · exact absurd hb hzw
  have hlt := inner_lt_sOff hc hu hu' i₀ hτ0 ha
  refine lt_ang_of_inner_lt hu hu' (by positivity) (by linarith) (hlt.trans_le ?_)
  rw [Real.cos_pi_div_three, Real.sqrt_le_left (by norm_num)]
  have : √3 / 2 ≤ tau X := by unfold beta at hτ₁; linarith
  nlinarith

/-- **Lemma A (ii)**: a type-(ii) partner direction is the reflection of `u_v` in `ℝc`:
`u_v·u′ = 2τ² − 1` (so `∠(u_v, u′) = 2θ₀`).

TODO: none — proved.
What's missing: first branch of `corner_lemma`: `exact_identity_c` for the redirected field,
`inner_two_sol`.
Acceptance: no `sorry`.
Depends on: `DirField.redirect`, `exact_identity_c`, `inner_two_sol`, `u_ne`-style argument.
Difficulty S–M. -/
theorem lemmaA_ii (F : DirField X) {v z w' : Pt} (hr : IsRung F v z) (hw' : w' ∈ X)
    (hw'v : dist v w' = dist2 X) (hne : w' ≠ F.partner v) (hzw : dist z w' = diam X) :
    inner ℝ (F.u v) ((dist2 X)⁻¹ • (w' - v)) = 2 * tau X ^ 2 - 1 := by
  have hv := hr.1
  have hvD := hr.2.1
  have hpos := hr.two.1.pos
  set F' := F.redirect hw' hw'v hvD
  have hp' : F'.partner v = w' := F.redirect_partner hw' hw'v hvD
  have hu'eq : F'.u v = (dist2 X)⁻¹ • (w' - v) := by
    unfold DirField.u; rw [hp', hw'v]
  rw [← hu'eq]
  have i₁ : inner ℝ (z - v) (F'.u v) = - tau X :=
    exact_identity_c F' hv hvD (by rw [hp']; exact hzw) (by rw [dist_comm]; exact hr.2.2.2.2.1)
  have hne' : F.u v ≠ F'.u v := by
    intro e
    apply hne
    have hpK := F.partner_K v hv hvD
    unfold DirField.u at e
    rw [hp', hpK, hw'v] at e
    have := smul_right_injective Pt (inv_ne_zero hpos.ne') e
    simpa using this.symm
  exact inner_two_sol hr.norm_c (F.norm_u hv) (F'.norm_u hv) hr.inner_eq i₁ hne'

/-- **At most 5 type-(i) vertices** (their normal cones of `K` are wider than `π/3` and
interior-disjoint; `6·π/3 = 2π`).

TODO: prove.
What's missing: copy of `card_cornerVerts_le` with `lemmaA_i` in place of `corner_lemma` and
`6` in place of `7`.
Acceptance: no `sorry`.
Depends on: `lemmaA_i`, `turning_sum_le`, `turning_ge_angle`, `ball_polygon_b`,
`neg_mem_normalCone`. Difficulty M. -/
theorem card_typeOne_le_five (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) : (typeOneVerts X F).card ≤ 5 := by
  sorry

/-! ## Lemma C -/

/-- **Lemma C, numeric condition** (referee's sufficient condition, `r4_regionII_checks.py`
Part E): on all of Region II,
`2τ√(1 − τ²) + (β + arcsin β + 2/Δ₂) < τ(1 − 1/(2Δ₂))`.

TODO: none — proved.
What's missing: `√(1 − τ²) ≤ √(1 − τ_min²) < 0.4441` with `τ_min = √3/2 + 3β`;
`arcsin β ≤ β + β³` (or `≤ 0.0101`); `1/Δ₂ ≤ 10⁻⁴`; then `nlinarith` (margin `≈ 0.08`).
Acceptance: no `sorry`.
Depends on: nothing (real analysis). Difficulty S–M. -/
theorem lemmaC_numeric {τ R : ℝ} (h1 : √3 / 2 + 3 * beta ≤ τ) (h2 : τ ≤ 1) (hR : 10 ^ 4 ≤ R) :
    2 * τ * √(1 - τ ^ 2) + (beta + Real.arcsin beta + 2 / R) < τ * (1 - 1 / (2 * R)) := by
  have hb : beta = 1 / 100 := rfl
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hτ : (0.896 : ℝ) ≤ τ := by rw [hb] at h1; linarith
  have hs : √(1 - τ ^ 2) ≤ 0.445 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hA : Real.arcsin beta < 0.05 := by
    rw [Real.arcsin_lt_iff_lt_sin ⟨by rw [hb]; norm_num, by rw [hb]; norm_num⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩]
    have := Real.sin_gt_sub_cube (x := 0.05) (by norm_num)
    rw [hb]; linarith
  have hR0 : 0 < R := by linarith
  have hR1 : 2 / R ≤ 2 / 10 ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR
  have hR2 : τ * (1 / (2 * R)) ≤ 1 / 10 ^ 4 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hs0 := Real.sqrt_nonneg (1 - τ ^ 2)
  nlinarith

/-- **Lemma C** (all of Region II): the rung partner `z` of a double vertex `v` (good rung) has
no T-neighbour, pure or mixed.

TODO: prove.
What's missing (angle_R4 §2): `w = w_v`, `w*` the type-(ii) partner; `|zw| = |zw*| = Δ`.
`ŵ = (w − z)/Δ` is within `arcsin(1/Δ)` of `u_v`, `ŵ*` within `arcsin(1/Δ)` of `u*`
(`lemmaA_ii`: `∠(u_v, u*) = 2θ₀`), `∠(u_v, u_z) ≤ β` (good rung).  For a T-neighbour `z₁`,
`(z₁ − z)·u_z ∈ (0, β)`, so `η = (z₁ − z)·ŵ` and `η*` are
`≤ sin(2θ₀) + ε ≤ 2sτ + ε` with `ε = β + arcsin β + 2/Δ₂`; the threshold
`(Δ² − Δ₂² + 1)/(2Δ) ≥ τ(1 − 1/(2Δ₂))` (`t ≥ τ` for `t ≤ 1`); `lemmaC_numeric` then
`lemmaB` gives `|z₁w| = |z₁w*| = Δ`.  Two distinct points `z, z₁` of `C(w,Δ) ∩ C(w*,Δ)` are
mirror images in `ww*`, at distance `≥ √3Δ > 1`; contradiction with `|zz₁| = 1`.
Acceptance: no `sorry`.
Depends on: `lemmaA_ii`, `lemmaB`, `lemmaC_numeric`, `exact_identity_a`, `rung_offset`,
`tau_sub_tgap`, `IsRung.two`. Difficulty L. -/
theorem lemmaC (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v z z₁ : Pt} (hd : IsDouble F v z) (hg : s(v, z) ∈ good X F)
    (hT : s(z, z₁) ∈ tEdges X F) : False := by
  sorry

/-! ## Counting -/

/-- **T-edges with isolated vertices**: if no vertex of `Z ⊆ S` has a T-edge then
`#T + |Z| ≤ |S|` (each vertex has T-degree `≤ 2`, and `0` on `Z`).

TODO: prove.
What's missing: `two_mul_card_le_of_deg_le` on `V = S ∖ Z` (all T-edges avoid `Z`), with the
degree bound of `card_tEdges_le`.
Acceptance: no `sorry`.
Depends on: `two_mul_card_le_of_deg_le`, `T1`, proof of `card_tEdges_le`. Difficulty M. -/
theorem card_tEdges_add_le_of_isolated (hX : Normal X) (F : DirField X) (Z : Finset Pt)
    (hZ : Z ⊆ Sset X) (h0 : ∀ z ∈ Z, ∀ q, s(z, q) ∉ tEdges X F) :
    (tEdges X F).card + Z.card ≤ (Sset X).card := by
  sorry

/-- `#T + #doubleEnds ≤ |S|` (Lemma C isolates the double ends).

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `lemmaC`, `card_tEdges_add_le_of_isolated`. -/
theorem card_tEdges_add_doubleEnds_le (hX : Normal X) (F : DirField X)
    (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1) :
    (tEdges X F).card + (doubleEnds X F).card ≤ (Sset X).card := by
  refine card_tEdges_add_le_of_isolated hX F _ (filter_subset _ _) fun z hz q hq => ?_
  obtain ⟨v, hd, hr⟩ := (mem_filter.1 hz).2
  exact lemmaC hX F hτ₁ hτ₂ hd (mem_filter.1 hr).1 hq

/-- **Rung count in Region II**: `#rungs ≤ #doubleEnds + |P₁| + 5`.
Rungs form a matching (R1); a rung is double, or its K-end has `Δ₂`-degree 1 (`∈ P₁`), or its
K-end is of type (i) (`≤ 5`).

TODO: prove.
What's missing: split `rungs` by `IsDouble` of its (unique) orientation `(v, z)`; the double ones
inject into `doubleEnds` via the D-end (`R1_z`), the others into `P1set ∪ typeOneVerts` via the
K-end (`R1_v`); a non-double rung whose K-end has `deg2 ≥ 2` has a partner `w′ ≠ w_v` with
`|zw′| ≠ Δ`.
Acceptance: no `sorry`.
Depends on: `R1_v`, `R1_z`, `card_typeOne_le_five`, definitions. Difficulty M. -/
theorem card_rungs_le_II (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    (rungs X F).card ≤ (doubleEnds X F).card + (P1set X F).card + 5 := by
  sorry

/-- **Region II** (`√3/2 + 3β ≤ τ ≤ 1`): `e(S) ≤ |S| + |P₁| + cReg`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `good_subset_T_union_rungs`, `card_good_add_bad`, `card_bad_le`,
`card_tEdges_add_doubleEnds_le`, `card_rungs_le_II`, `two_beta_lt_of`. -/
theorem regionII15 (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    (eS X : ℝ) ≤ (Sset X).card + (P1set X F).card + cReg := by
  have hτ : 2 * beta < tau X := by
    have : (0 : ℝ) < √3 / 2 := by positivity
    unfold beta at hτ₁ ⊢; linarith
  have hsub := good_subset_T_union_rungs hX F hτ
  have hg := (card_le_card hsub).trans (card_union_le _ _)
  have h1 := card_tEdges_add_doubleEnds_le hX F hτ₁ hτ₂
  have h2 := card_rungs_le_II hX F hτ₁ hτ₂
  have hgood : ((good X F).card : ℝ) ≤ (Sset X).card + (P1set X F).card + 5 := by
    exact_mod_cast (show (good X F).card ≤ (Sset X).card + (P1set X F).card + 5 by omega)
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  unfold cReg
  have : (0 : ℝ) ≤ cBad := by norm_num [cBad]
  linarith

end

end Erdos132Main

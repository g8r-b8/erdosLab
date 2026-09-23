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
  sorry

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
  sorry

/-- **(R1) at `z`**: a D-vertex has at most one good rung (`|v − v′| ≤ 2s + 2β < 1`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`, rotation bound `|o(u) − o(u′)| ≤ ∠(u, u′)`.
Difficulty M. -/
theorem R1_z (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v₁ v₂ z : Pt} (h₁ : IsRung F v₁ z) (h₂ : IsRung F v₂ z)
    (hg₁ : ang (F.u v₁) (F.u z) ≤ beta) (hg₂ : ang (F.u v₂) (F.u z) ≤ beta) : v₁ = v₂ := by
  sorry

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
  sorry

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
  sorry

/-- **(R3a) no three parallel rungs**: `u_v` solves `c·u = −τ`, which has two unit solutions,
and K-ends have distinct normals (Lemma 3.3).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `u_ne`, `DirField.norm_u`. Difficulty M. -/
theorem R3_no_three_parallel (F : DirField X) {v₁ v₂ v₃ z₁ z₂ z₃ : Pt} (h₁ : IsRung F v₁ z₁)
    (h₂ : IsRung F v₂ z₂) (h₃ : IsRung F v₃ z₃) (e₁₂ : z₁ - v₁ = z₂ - v₂)
    (e₁₃ : z₁ - v₁ = z₃ - v₃) : v₁ = v₂ ∨ v₁ = v₃ ∨ v₂ = v₃ := by
  sorry

/-- **(R3b) rhombi force parallel rungs**: a unit rhombus `v₀v₁z₁z₀` has `z₀ − v₀ = z₁ − v₁`
(`v₁, z₀` are the two points of `C(v₀,1) ∩ C(z₁,1)`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: planar circle intersection. Difficulty M. -/
theorem R3_rhombus {v₀ v₁ z₀ z₁ : Pt} (h₀₁ : dist v₀ v₁ = 1) (h₁₁ : dist v₁ z₁ = 1)
    (h₁₀ : dist z₁ z₀ = 1) (h₀₀ : dist z₀ v₀ = 1) (hne : v₁ ≠ z₀) (hne' : v₀ ≠ z₁) :
    z₀ - v₀ = z₁ - v₁ := by
  sorry

/-- **(R3c) rhombi only near resonance**: two parallel rungs whose K-ends are joined by a good
edge force `τ ≥ cos(β/2)` (their normals are exactly `2θ₀` apart, `θ₀ = arccos τ`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `u_ne`. Difficulty M. -/
theorem R3_resonance (F : DirField X) {v₀ v₁ z₀ z₁ : Pt} (h₀ : IsRung F v₀ z₀)
    (h₁ : IsRung F v₁ z₁) (hpar : z₀ - v₀ = z₁ - v₁) (hne : v₀ ≠ v₁)
    (hg : ang (F.u v₀) (F.u v₁) ≤ beta) : Real.cos (beta / 2) ≤ tau X := by
  sorry

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

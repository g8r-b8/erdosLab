import Erdos.E132Main15Exact

/-!
# Erdős Problem 132, `15/11` theorem — Region III: `e(S) ≤ |S| + |Q| + C`

`angle_R4.md` §3, for `√3/2 − 2β < τ < √3/2 + 3β`.  With `q₂ = #twoRungVerts`:
`#rungs ≤ #rungVerts + q₂`, `#rungVerts ≤ |P₁| + 6` (corner lemma), so it suffices that

  `#T + q₂ ≤ |S| + C`   (`regionIII_key`).

* `τ > √3/2`: the two rung positions are `2s < 1` apart, so `q₂ = 0` (`twoRung_eq_empty`).
* `τ < √3/2`: **slot killing** (Lemma III.1, `slot_kill_one`) with injectivity
  (`slot_kill_inj`) kills `2q₂` distinct T-slots; `card_tEdges_slots` counts slots.
* `τ = √3/2`: breaks (`E132Main15Exact.exact_breaks`) and `card_tEdges_add_breaks_le`, with
  Lemma 7.1 in Region III (`card_mixedT_le_III`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Rung and slot bookkeeping -/

/-- `#rungs ≤ #rungVerts + #twoRungVerts` (each K-end carries `≤ 2` good rungs, and `2` only on
`twoRungVerts`).

TODO: prove.
What's missing: as `card_rungs_le`: map a rung to its K-end; fibres have size `≤ 2`, and size
`2` only over `twoRungVerts`; `card_le_card_biUnion`-style sum over fibres.
Acceptance: no `sorry`.
Depends on: `rung_offset`, proof of `card_rungs_le`. Difficulty M. -/
theorem card_rungs_le_add (hX : Normal X) (F : DirField X) :
    (rungs X F).card ≤ (rungVerts X F).card + (twoRungVerts X F).card := by
  sorry

/-- For `τ > √3/2` no vertex carries two rungs: the positions `v + o_±` are `2s < 1` apart.

TODO: prove.
What's missing: `rung_offset` for both rungs; `σ ≠ σ'` (else equal); `|z − z′| = 2 sOff < 1`
(`sOff² = 1 − τ² < 1/4`); `eq_of_dist_lt_one`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `eq_of_dist_lt_one`, `norm_perp`. Difficulty S–M. -/
theorem twoRung_eq_empty (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) : twoRungVerts X F = ∅ := by
  sorry

/-- **Slot counting**: each T-edge uses two slots (one at each end, by the sign of `det2`), each
slot is used at most once (T1); so `2#T + #(free slots) ≤ 2|S|`.

TODO: prove.
What's missing: injection `tEdges × {end} → S × {±1}` (via `tstep_flip`: the two ends see each
other on opposite sides, and `tnbr_unique`), disjoint from `Kill`; slots live in
`S ×ˢ {1, -1}` of size `2|S|`.
Acceptance: no `sorry`.
Depends on: `tnbr_unique`, `tstep_flip`, definitions. Difficulty M. -/
theorem card_tEdges_slots (hX : Normal X) (F : DirField X) (Kill : Finset (Pt × ℝ))
    (hK : ∀ x ∈ Kill, x.1 ∈ Sset X ∧ (x.2 = 1 ∨ x.2 = -1) ∧ SlotFree F x.1 x.2) :
    2 * (tEdges X F).card + Kill.card ≤ 2 * (Sset X).card := by
  sorry

/-- **Lemma III.1** (`τ < √3/2`, `2s > 1`): if `v` has rungs `z ≠ z′` (the one to `z′` good),
then `z′` has no T-neighbour on the side of `z`.
(`o₊ − o₋ = 2s·u^⊥`; a T-neighbour `y` of `z′` on that side has `∠(y − z′, z − z′) ≤ β + arcsin β`,
so `|y − z|² ≤ (2s − 1)² + 4s(1 − cos γ) < 1`, and `y ≠ z` since `|zz′| = 2s ≠ 1`.)

TODO: prove.
What's missing: the vector computation above with `rung_offset`, `RungM.ang`/good rung,
`IsTEdge` bounds, `eq_of_dist_lt_one`; float worst case `|y − z| ≤ 0.069`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `norm_offset_sub`, `same_side_close`, `eq_of_dist_lt_one`.
Difficulty M–L. -/
theorem slot_kill_one (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2) {v z z' : Pt} (hr : IsRung F v z) (hr' : IsRung F v z')
    (hg' : s(v, z') ∈ rungs X F) (hne : z ≠ z') {σ : ℝ}
    (hσ : 0 < σ * det2 (F.u z') (z - z')) : SlotFree F z' σ := by
  sorry

/-- **Injectivity of killed slots** (`τ < √3/2`): two two-rung vertices `v, v̄` sharing a rung end
`z′` and killing the same slot of `z′` coincide.  (`|z̄ − z| ≤ 2s·2β < 1` gives `z̄ = z`; then `v̄`
is the mirror image of `v` in `zz′`, contradicting Lemma 3.2(a) at `z′`.)

TODO: prove.
What's missing: `rung_offset` for the four rungs, goodness (`∠(u_v, u_{z′}), ∠(u_v̄, u_{z′}) ≤ β`),
`eq_of_dist_lt_one`, then the mirror argument with `exact_identity_a`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `exact_identity_a`, `eq_of_dist_lt_one`. Difficulty M–L. -/
theorem slot_kill_inj (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2) {v v' z z' z'' : Pt} (hr : IsRung F v z) (hr' : IsRung F v z')
    (hs' : IsRung F v' z') (hs'' : IsRung F v' z'') (g : s(v, z) ∈ rungs X F)
    (g' : s(v, z') ∈ rungs X F) (k' : s(v', z') ∈ rungs X F) (k'' : s(v', z'') ∈ rungs X F)
    (hne : z ≠ z') (hne' : z'' ≠ z') {σ : ℝ} (hσ : 0 < σ * det2 (F.u z') (z - z'))
    (hσ' : 0 < σ * det2 (F.u z') (z'' - z')) : v = v' := by
  sorry

/-- **Slot bound for `τ < √3/2`**: `#T + q₂ ≤ |S|`.

TODO: prove (wiring).
What's missing: `Kill := ⋃_{v ∈ twoRungVerts} {(z′, σ_v), (z, σ′_v)}` (the two killed slots of
`v`, chosen via `Classical.choose`); `slot_kill_one` gives `SlotFree`; `slot_kill_inj` and
`z ≠ z′` give `#Kill = 2q₂`; conclude with `card_tEdges_slots`.
Acceptance: no `sorry` (inherits).
Depends on: `card_tEdges_slots`, `slot_kill_one`, `slot_kill_inj`. Difficulty M. -/
theorem card_tEdges_add_twoRung_lt (hX : Normal X) (F : DirField X)
    (hτ₁ : √3 / 2 - 2 * beta < tau X) (hτ₂ : tau X < √3 / 2) :
    (tEdges X F).card + (twoRungVerts X F).card ≤ (Sset X).card := by
  sorry

/-- **Breaks**: `#T + #breaks ≤ |S| + #mixed` (a pure T-edge is charged to its left end, which
has a pure right T-neighbour; each vertex has `≤ 1` right T-neighbour).

TODO: prove.
What's missing: `tEdges = pure ⊔ mixedT`; the left-end map on pure T-edges is injective into
`S ∖ breaks` (`rowR_fun`; orientation from `tstep_flip`/`T2`).
Acceptance: no `sorry`.
Depends on: `rowR_fun`, `tstep_flip`, `T2`, `mixedT_data`. Difficulty M. -/
theorem card_tEdges_add_breaks_le (hX : Normal X) (F : DirField X) :
    (tEdges X F).card + (breaks X F).card ≤ (Sset X).card + (mixedT X F).card := by
  sorry

/-- **Lemma 7.1 in Region III** (F3): `#mixed T-edges ≤ 1500` for `√3/2 − 2β < τ < √3/2 + 3β`
(`t ≥ τ > 0.846`, so `t − arcsin β > 0.835`).

TODO: prove.
What's missing: re-run `lemma71` / `card_mixedT_le` with the Region III lower bound
`t − arcsin β ≥ 0.835` in place of `c5_tgap` (`0.886`); the count becomes
`2π·81/0.835·… ≤ 1500`.
Acceptance: no `sorry`.
Depends on: proofs of `lemma71`, `card_mixedT_le`, `c5_tgap`. Difficulty M–L. -/
theorem card_mixedT_le_III (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) : ((mixedT X F).card : ℝ) ≤ 1500 := by
  sorry

/-! ## Region III -/

/-- **Key bound**: `#T + q₂ ≤ |S| + cBad + 1500` on all of Region III.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `twoRung_eq_empty`, `card_tEdges_le`, `card_tEdges_add_twoRung_lt`,
`card_tEdges_add_breaks_le`, `exact_breaks`, `card_mixedT_le_III`. -/
theorem regionIII_key (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) :
    ((tEdges X F).card : ℝ) + (twoRungVerts X F).card ≤ (Sset X).card + (cBad + 1500) := by
  have hc : (0 : ℝ) ≤ cBad := by norm_num [cBad]
  rcases lt_trichotomy (tau X) (√3 / 2) with h | h | h
  · have := card_tEdges_add_twoRung_lt hX F hτ₁ h
    have : ((tEdges X F).card : ℝ) + (twoRungVerts X F).card ≤ (Sset X).card := by
      exact_mod_cast this
    linarith
  · have h1 := card_tEdges_add_breaks_le hX F
    have h1' : ((tEdges X F).card : ℝ) + (breaks X F).card ≤ (Sset X).card + (mixedT X F).card := by
      exact_mod_cast h1
    have h2 := exact_breaks hX F h
    have h3 := card_mixedT_le_III hX F hτ₁ hτ₂
    linarith
  · rw [twoRung_eq_empty hX F h hτ₂, card_empty, Nat.cast_zero, add_zero]
    have : ((tEdges X F).card : ℝ) ≤ (Sset X).card := by exact_mod_cast card_tEdges_le hX F
    linarith

/-- **Region III** (`√3/2 − 2β < τ < √3/2 + 3β`): `e(S) ≤ |S| + |P₁| + cReg`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `good_subset_T_union_rungs`, `card_rungs_le_add`, `card_rungVerts`,
`card_cornerVerts_le`, `regionIII_key`, `card_good_add_bad`, `card_bad_le`, `two_beta_lt_of`. -/
theorem regionIII15 (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) :
    (eS X : ℝ) ≤ (Sset X).card + (P1set X F).card + cReg := by
  have hsub := good_subset_T_union_rungs hX F (two_beta_lt_of hτ₁)
  have hg := (card_le_card hsub).trans (card_union_le _ _)
  have hR := card_rungs_le_add hX F
  have hV := card_rungVerts F
  have hC := card_cornerVerts_le hX F hτ₁ hτ₂
  have hgood : ((good X F).card : ℝ) ≤ (tEdges X F).card + (twoRungVerts X F).card +
      (P1set X F).card + 6 := by
    exact_mod_cast (show (good X F).card ≤ (tEdges X F).card + (twoRungVerts X F).card +
      (P1set X F).card + 6 by omega)
  have hkey := regionIII_key hX F hτ₁ hτ₂
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  unfold cReg
  linarith

end

end Erdos132Main

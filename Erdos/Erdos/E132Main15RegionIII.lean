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

TODO: none — proved.
What's missing: (was) as `card_rungs_le`: map a rung to its K-end; fibres have size `≤ 2`, and size
`2` only over `twoRungVerts`; `card_le_card_biUnion`-style sum over fibres.
Acceptance: no `sorry`.
Depends on: `rung_offset`, proof of `card_rungs_le`. Difficulty M. -/
theorem card_rungs_le_add (hX : Normal X) (F : DirField X) :
    (rungs X F).card ≤ (rungVerts X F).card + (twoRungVerts X F).card := by
  classical
  let f : Sym2 Pt → Pt := fun e =>
    if h : ∃ v w, e = s(v, w) ∧ IsRung F v w then h.choose else 0
  have hf : ∀ e, (h : ∃ v w, e = s(v, w) ∧ IsRung F v w) →
      ∃ w, e = s(f e, w) ∧ IsRung F (f e) w := by
    intro e h
    have : f e = h.choose := dif_pos h
    rw [this]; exact h.choose_spec
  have hmap : ∀ e ∈ rungs X F, f e ∈ rungVerts X F := by
    intro e he
    obtain ⟨w, -, hr⟩ := hf e (mem_filter.1 he).2
    exact mem_filter.2 ⟨mem_sdiff.2 ⟨hr.1, hr.2.1⟩, w, hr⟩
  rw [card_eq_sum_card_fiberwise hmap]
  have hfib : ∀ v ∈ rungVerts X F, ((rungs X F).filter (fun e => f e = v)).card ≤
      1 + if v ∈ twoRungVerts X F then 1 else 0 := by
    intro v hv
    split_ifs with h2
    · let o : ℝ → Pt := fun σ => v + ((-tau X) • F.u v + (σ * sOff X) • perp (F.u v))
      have hsub : (rungs X F).filter (fun e => f e = v) ⊆ {s(v, o 1), s(v, o (-1))} := by
        intro e he
        obtain ⟨he, hfe⟩ := mem_filter.1 he
        obtain ⟨w, hew, hr⟩ := hf e (mem_filter.1 he).2
        rw [hfe] at hew hr
        obtain ⟨σ, hσ, ho⟩ := rung_offset F hr
        have hw : w = o σ := by simp only [o]; rw [← ho]; abel
        rw [hew, hw]
        rcases hσ with rfl | rfl <;> simp
      exact (card_le_card hsub).trans card_le_two
    · refine (card_le_one.2 fun e he e' he' => ?_).trans (by omega)
      by_contra hne
      apply h2
      obtain ⟨he, hfe⟩ := mem_filter.1 he
      obtain ⟨he', hfe'⟩ := mem_filter.1 he'
      obtain ⟨w, hew, hr⟩ := hf e (mem_filter.1 he).2
      obtain ⟨w', hew', hr'⟩ := hf e' (mem_filter.1 he').2
      rw [hfe] at hew hr
      rw [hfe'] at hew' hr'
      refine mem_filter.2 ⟨hv, w, w', ?_, hr, hr', hew ▸ he, hew' ▸ he'⟩
      rintro rfl
      exact hne (hew.trans hew'.symm)
  refine (sum_le_sum hfib).trans ?_
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole]
  have : ((rungVerts X F).filter (fun v => v ∈ twoRungVerts X F)).card ≤
      (twoRungVerts X F).card := card_le_card fun v hv => (mem_filter.1 hv).2
  simp only [Nat.cast_id] at this ⊢
  omega

/-- For `τ > √3/2` no vertex carries two rungs: the positions `v + o_±` are `2s < 1` apart.

TODO: none — proved.
What's missing: (was) `rung_offset` for both rungs; `σ ≠ σ'` (else equal); `|z − z′| = 2 sOff < 1`
(`sOff² = 1 − τ² < 1/4`); `eq_of_dist_lt_one`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `eq_of_dist_lt_one`, `norm_perp`. Difficulty S–M. -/
theorem twoRung_eq_empty (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) : twoRungVerts X F = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨z, z', hne, h₁, h₂, -, -⟩ := (mem_filter.1 hv).2
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F h₁
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F h₂
  have hu := F.norm_u h₁.1
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hs : 2 * sOff X < 1 := by
    have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have : sOff X < 1 / 2 := by
      have e3 : (√3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      have : (√3 / 2) ^ 2 < tau X ^ 2 := pow_lt_pow_left₀ hτ₁ (by positivity) (by norm_num)
      unfold sOff; rw [Real.sqrt_lt' (by norm_num)]; nlinarith
    linarith
  refine hne (eq_of_dist_lt_one hX.minDist_eq h₁.memX.2 h₂.memX.2 ?_)
  have e : z - z' = (z - v) - (z' - v) := by abel
  rw [dist_eq_norm, e, e₁, e₂]
  refine (norm_offset_sub hu hu hs0 hσ₁ hσ₂).trans_lt ?_
  simpa using hs

/-- **Slot counting**: each T-edge uses two slots (one at each end, by the sign of `det2`), each
slot is used at most once (T1); so `2#T + #(free slots) ≤ 2|S|`.

TODO: none — proved.
What's missing: (was) injection `tEdges × {end} → S × {±1}` (via `tstep_flip`: the two ends see each
other on opposite sides, and `tnbr_unique`), disjoint from `Kill`; slots live in
`S ×ˢ {1, -1}` of size `2|S|`.
Acceptance: no `sorry`.
Depends on: `tnbr_unique`, `tstep_flip`, definitions. Difficulty M. -/
theorem card_tEdges_slots (hX : Normal X) (F : DirField X) (Kill : Finset (Pt × ℝ))
    (hK : ∀ x ∈ Kill, x.1 ∈ Sset X ∧ (x.2 = 1 ∨ x.2 = -1) ∧ SlotFree F x.1 x.2) :
    2 * (tEdges X F).card + Kill.card ≤ 2 * (Sset X).card := by
  classical
  set S := Sset X
  set T := tEdges X F
  have hE : ∀ z ∈ T, ¬ z.IsDiag ∧ ∀ p ∈ z, p ∈ S := fun z hz =>
    mem_edges (mem_filter.1 (mem_filter.1 hz).1).1
  have tdata : ∀ {p q : Pt}, s(p, q) ∈ T → dist p q = 1 ∧ IsTEdge F p q := by
    intro p q h
    obtain ⟨hg, hTall⟩ := mem_filter.1 h
    obtain ⟨hee, -⟩ := mem_filter.1 hg
    have hd : pairDist s(p, q) = minDist X := (mem_filter.1 hee).2
    exact ⟨by rw [← hX.minDist_eq, ← hd]; rfl, hTall p q rfl⟩
  have h2 : ∀ z ∈ T, (S.filter (fun p => p ∈ z)).card = 2 := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨hd, hV⟩ := hE _ hz
      have hab : a ≠ b := by simpa using hd
      have : S.filter (fun p => p ∈ s(a, b)) = {a, b} := by
        ext x
        simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hV _ (Sym2.mem_mk_left _ _), Or.inl rfl⟩
          · exact ⟨hV _ (Sym2.mem_mk_right _ _), Or.inr rfl⟩
      rw [this, card_pair hab]
  have hdc : ∑ z ∈ T, (S.filter (fun p => p ∈ z)).card =
      ∑ p ∈ S, (T.filter (fun z => p ∈ z)).card := by
    simp only [card_filter]; exact sum_comm
  have hT2 : 2 * T.card = ∑ p ∈ S, (T.filter (fun z => p ∈ z)).card := by
    rw [← hdc, sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
  have hK2 : Kill.card = ∑ p ∈ S, (Kill.filter (fun x => x.1 = p)).card :=
    card_eq_sum_card_fiberwise (fun x hx => (hK x hx).1)
  have hloc : ∀ p ∈ S, (T.filter (fun z => p ∈ z)).card +
      (Kill.filter (fun x => x.1 = p)).card ≤ 2 := by
    intro p hp
    let B : ℝ → Finset Pt := fun σ =>
      S.filter (fun q => s(p, q) ∈ T ∧ 0 < σ * det2 (F.u p) (q - p))
    let k : ℝ → ℕ := fun σ => if (p, σ) ∈ Kill then 1 else 0
    have hB : ∀ σ, (B σ).card + k σ ≤ 1 := by
      intro σ
      by_cases hk : (p, σ) ∈ Kill
      · have hfree := (hK _ hk).2.2
        have : B σ = ∅ := by
          refine eq_empty_of_forall_notMem fun q hq => ?_
          obtain ⟨-, hqT, hs⟩ := mem_filter.1 hq
          exact hfree q hqT hs
        simp [k, hk, this]
      · simp only [k, hk, if_false, add_zero]
        refine card_le_one.2 fun a ha b hb => ?_
        obtain ⟨haS, haT, has⟩ := mem_filter.1 ha
        obtain ⟨hbS, hbT, hbs⟩ := mem_filter.1 hb
        obtain ⟨da, ta⟩ := tdata haT
        obtain ⟨db, tb⟩ := tdata hbT
        exact tnbr_unique hX hp haS hbS da db ta tb has hbs
    have hsub : T.filter (fun z => p ∈ z) ⊆ (B 1 ∪ B (-1)).image (fun q => s(p, q)) := by
      intro z hz
      obtain ⟨hzT, hpz⟩ := mem_filter.1 hz
      obtain ⟨q, rfl⟩ := Sym2.mem_iff_exists.1 hpz
      obtain ⟨hd, hTe⟩ := tdata hzT
      have hq : q ∈ S := (hE _ hzT).2 q (Sym2.mem_mk_right _ _)
      rw [mem_image]
      refine ⟨q, ?_, rfl⟩
      have hl := lagrange (q - p) (F.u p)
      rw [F.norm_u' hp, ← dist_eq_norm, dist_comm q p, hd] at hl
      have ha := hTe.2.1
      have hβ : beta = 1 / 100 := rfl
      rw [hβ] at ha
      rcases lt_or_gt_of_ne (show det2 (F.u p) (q - p) ≠ 0 by
        intro h0; rw [h0] at hl; nlinarith [hTe.1]) with hb | hb
      · exact mem_union_right _ (mem_filter.2 ⟨hq, hzT, by linarith⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hq, hzT, by linarith⟩)
    have hKp : (Kill.filter (fun x => x.1 = p)).card ≤ k 1 + k (-1) := by
      have : Kill.filter (fun x => x.1 = p) ⊆
          (if (p, (1 : ℝ)) ∈ Kill then {(p, 1)} else ∅) ∪
            (if (p, (-1 : ℝ)) ∈ Kill then {(p, -1)} else ∅) := by
        intro x hx
        obtain ⟨hxK, hx1⟩ := mem_filter.1 hx
        obtain ⟨-, hσ, -⟩ := hK x hxK
        obtain ⟨a, σ⟩ := x
        simp only at hx1 hσ
        subst hx1
        rcases hσ with rfl | rfl
        · apply mem_union_left; rw [if_pos hxK]; exact mem_singleton_self _
        · apply mem_union_right; rw [if_pos hxK]; exact mem_singleton_self _
      refine (card_le_card this).trans ((card_union_le _ _).trans ?_)
      simp only [k]; split_ifs <;> simp
    have c1 := hB 1
    have c2 := hB (-1)
    have := (card_le_card hsub).trans (card_image_le.trans (card_union_le _ _))
    omega
  have := sum_le_sum hloc
  rw [sum_add_distrib, sum_const, smul_eq_mul, ← hT2, ← hK2] at this
  omega

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

TODO: none — proved.
What's missing: (was) `tEdges = pure ⊔ mixedT`; the left-end map on pure T-edges is injective into
`S ∖ breaks` (`rowR_fun`; orientation from `tstep_flip`/`T2`).
Acceptance: no `sorry`.
Depends on: `rowR_fun`, `tstep_flip`, `T2`, `mixedT_data`. Difficulty M. -/
theorem card_tEdges_add_breaks_le (hX : Normal X) (F : DirField X) :
    (tEdges X F).card + (breaks X F).card ≤ (Sset X).card + (mixedT X F).card := by
  classical
  have tdata : ∀ {p q : Pt}, s(p, q) ∈ tEdges X F → dist p q = 1 ∧ IsTEdge F p q := by
    intro p q h
    obtain ⟨hg, hTall⟩ := mem_filter.1 h
    obtain ⟨hee, -⟩ := mem_filter.1 hg
    have hd : pairDist s(p, q) = minDist X := (mem_filter.1 hee).2
    exact ⟨by rw [← hX.minDist_eq, ← hd]; rfl, hTall p q rfl⟩
  have hleft : ∀ z ∈ tEdges X F \ mixedT X F, ∃ a b, z = s(a, b) ∧ RowR F a b := by
    intro z hz
    obtain ⟨hzT, hzM⟩ := mem_sdiff.1 hz
    induction z using Sym2.ind with
    | h p q =>
    obtain ⟨hd, hTe⟩ := tdata hzT
    have hS := (mem_edges (mem_filter.1 (mem_filter.1 hzT).1).1).2
    have hp := hS p (Sym2.mem_mk_left _ _)
    have hq := hS q (Sym2.mem_mk_right _ _)
    have hg : ang (F.u p) (F.u q) ≤ beta := (mem_filter.1 (mem_filter.1 hzT).1).2 p q rfl
    have hDD : (p ∈ Dset X ↔ q ∈ Dset X) := by
      constructor
      · intro hpD; by_contra hqD
        exact hzM (mem_filter.2 ⟨hzT, q, p, Sym2.eq_swap, hqD, hpD⟩)
      · intro hqD; by_contra hpD
        exact hzM (mem_filter.2 ⟨hzT, p, q, rfl, hpD, hqD⟩)
    have hl := lagrange (q - p) (F.u p)
    rw [F.norm_u' hp, ← dist_eq_norm, dist_comm q p, hd] at hl
    have ha := hTe.2.1
    have hβ : beta = 1 / 100 := rfl
    rw [hβ] at ha
    rcases lt_or_gt_of_ne (show det2 (F.u p) (q - p) ≠ 0 by
      intro h0; rw [h0] at hl; nlinarith [hTe.1]) with hb | hb
    · exact ⟨p, q, rfl, ⟨hp, hq, hd, hg, hTe, by linarith⟩, hDD⟩
    · have := tstep_flip hp hq hd hg hTe.1 hTe.2.1
      have hb' : det2 (F.u q) (p - q) < 0 := by nlinarith
      exact ⟨q, p, Sym2.eq_swap, ⟨hq, hp, by rw [dist_comm]; exact hd,
        by rw [ang, InnerProductGeometry.angle_comm]; exact hg, hTe.symm, by linarith⟩, hDD.symm⟩
  let g : Sym2 Pt → Pt := fun z =>
    if h : ∃ a b, z = s(a, b) ∧ RowR F a b then h.choose else 0
  have hg : ∀ z, (h : ∃ a b, z = s(a, b) ∧ RowR F a b) → ∃ b, z = s(g z, b) ∧ RowR F (g z) b := by
    intro z h
    have : g z = h.choose := dif_pos h
    rw [this]; exact h.choose_spec
  have hinj : Set.InjOn g ↑(tEdges X F \ mixedT X F) := by
    intro z hz z' hz' e
    obtain ⟨b, hzb, hr⟩ := hg z (hleft z hz)
    obtain ⟨b', hzb', hr'⟩ := hg z' (hleft z' hz')
    rw [e] at hzb hr
    rw [rowR_fun hX hr hr'] at hzb
    exact hzb.trans hzb'.symm
  have hmaps : ∀ z ∈ tEdges X F \ mixedT X F, g z ∈ Sset X \ breaks X F := by
    intro z hz
    obtain ⟨b, -, hr⟩ := hg z (hleft z hz)
    exact mem_sdiff.2 ⟨hr.1.1, fun hb => (mem_filter.1 hb).2 ⟨b, hr⟩⟩
  have h1 := card_le_card_of_injOn g hmaps hinj
  have h2 := card_sdiff_add_card_eq_card (show breaks X F ⊆ Sset X from filter_subset _ _)
  have h3 : (tEdges X F).card ≤ (tEdges X F \ mixedT X F).card + (mixedT X F).card :=
    card_le_card_sdiff_add_card
  omega

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

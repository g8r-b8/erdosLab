import Erdos.E132Main97Defs

/-!
# Erdős Problem 132, `τ > 1`: the `D`-part and the splitting `G = G[D] ⊔ G[X ∖ D]`

`problems/132/angle_R6.md` §5.3, steps 1–2.

* `t = Δ − Δ₂ > 1` ⇒ no unit distance between `D` and `X ∖ D` (`one_lt_dist_D_Y`): for `z ∈ D`
  with diametral partner `x`, every `y ∉ D` has `|y − x| ≤ Δ₂`, so `|z − y| ≥ Δ − Δ₂ > 1`.
  Hence `e(X) = e(D) + e(X ∖ D)` (`mult_split`).
* `Def(G[D]) ≥ 2|S ∩ D| − cBad` (`dpart`).  Deviation from the paper (which extends the
  T-edge machinery of WRITEUP_A2 to all of `D`): the repo's `DirField` lives on `S` only, so we
  use `deg ≤ 3` on `D` for the points of `D ∖ S`, and on `S ∩ D`: good edges are T-edges (no
  rungs for `τ > 1`), at most one left and one right T-neighbour each (`T1`), bad edges
  `≤ cBad` (`card_bad_le`).  So `e(D) ≤ |S ∩ D| + cBad + 3|D ∖ S|`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- **Arc packing, open half-circle**: points at distance `1` from `y`, pairwise `≥ 1` apart, with
`(q − y)·n ≥ ε > 0`, number at most 3 (copy of `card_sep_arc_le_four` with `arccos ε < π/2`). -/
theorem card_sep_arc_le_three {y n : Pt} (hn : ‖n‖ = 1) (P : Finset Pt)
    (h1 : ∀ q ∈ P, dist q y = 1) (hsep : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → 1 ≤ dist q q')
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcone : ∀ q ∈ P, ε ≤ inner ℝ (q - y) n) : P.card ≤ 3 := by
  have hπ := Real.pi_pos
  obtain ⟨θn, hθn⟩ := exists_dirVec hn
  have hu : ∀ q ∈ P, ‖q - y‖ = 1 := fun q hq => by rw [← dist_eq_norm, h1 q hq]
  have hp : (0 : ℝ) < 2 * π := by linarith
  have hang : ∀ q ∈ P, ∃ ψ : ℝ, ψ ∈ Set.Ioc (-π) π ∧ dirVec (θn + ψ) = q - y := by
    intro q hq
    obtain ⟨φ, -, hφ⟩ := exists_angle (hu q hq)
    refine ⟨toIocMod hp (-π) (φ - θn), ?_, ?_⟩
    · have := toIocMod_mem_Ioc hp (-π) (φ - θn)
      refine ⟨this.1, ?_⟩
      linarith [this.2]
    · have e := toIocMod_add_toIocDiv_zsmul hp (-π) (φ - θn)
      rw [← hφ]
      have : θn + toIocMod hp (-π) (φ - θn) =
          φ + ((-(toIocDiv hp (-π) (φ - θn)) : ℤ) : ℝ) * (2 * π) := by
        rw [zsmul_eq_mul] at e; push_cast; linarith
      rw [this, dirVec_add_int]
  choose! ψ hψ hψd using hang
  set A := Real.arccos ε with hAdef
  have hA0 : 0 ≤ A := Real.arccos_nonneg _
  have hA : A < π / 2 := by
    rw [hAdef, ← Real.arccos_zero]
    exact Real.arccos_lt_arccos (by norm_num) hε hε1
  have hbound : ∀ q ∈ P, |ψ q| ≤ A := by
    intro q hq
    have hc : Real.cos (ψ q) = inner ℝ (q - y) n := by
      rw [← hψd q hq, ← hθn, Curve.inner_dirVec]; congr 1; ring
    have hcos : ε ≤ Real.cos |ψ q| := by rw [Real.cos_abs, hc]; exact hcone q hq
    have hm0 : 0 ≤ |ψ q| := abs_nonneg _
    have hm1 : |ψ q| ≤ π := abs_le.2 ⟨by linarith [(hψ q hq).1], (hψ q hq).2⟩
    rw [← Real.arccos_cos hm0 hm1]
    exact Real.arccos_le_arccos hcos
  have hsep' : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → π / 3 ≤ |ψ q - ψ q'| := by
    intro q hq q' hq' hne
    by_contra hlt
    push Not at hlt
    have hlt' := Defs.sqd_lt_of_arg one_pos (a := θn + ψ q) (b := θn + ψ q')
      (by rwa [add_sub_add_left_eq_sub])
    have hd := hsep q hq q' hq' hne
    have e : dist q q' ^ 2 = (1 * Real.cos (θn + ψ q) - 1 * Real.cos (θn + ψ q')) ^ 2 +
        (1 * Real.sin (θn + ψ q) - 1 * Real.sin (θn + ψ q')) ^ 2 := by
      have e0 : dist q q' = dist (q - y) (q' - y) := by
        rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]
      rw [e0, dist_sq_pt, ← hψd q hq, ← hψd q' hq']
      simp only [dirVec_apply0, dirVec_apply1, one_mul]
    nlinarith [dist_nonneg (x := q) (y := q')]
  have hc3 : 0 < π / 3 := by positivity
  have hinj : Set.InjOn (fun q => ψ q / (π / 3)) P := by
    intro q hq q' hq' h
    by_contra hne
    have h3 := hsep' q hq q' hq' hne
    simp only at h
    have : ψ q = ψ q' := by
      have := congrArg (· * (π / 3)) h
      simpa [div_mul_cancel₀ _ hc3.ne'] using this
    rw [this, sub_self, abs_zero] at h3
    linarith
  have hcard := card_le_of_sep_real (a := -(A / (π / 3))) (P.image fun q => ψ q / (π / 3))
    (A / (π / 3)) (by have : 0 ≤ A / (π / 3) := by positivity
                      linarith)
    (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
      have hb := abs_le.1 (hbound q hq)
      constructor
      · rw [← neg_div]; exact div_le_div_of_nonneg_right hb.1 hc3.le
      · exact div_le_div_of_nonneg_right hb.2 hc3.le)
    (by
      intro x hx x' hx' hne
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
      obtain ⟨q', hq', rfl⟩ := mem_image.1 hx'
      have hqq : q ≠ q' := by rintro rfl; exact hne rfl
      have h3 := hsep' q hq q' hq' hqq
      rw [← sub_div, abs_div, abs_of_pos hc3, le_div_iff₀ hc3, one_mul]
      exact h3)
  rw [card_image_of_injOn hinj] at hcard
  have : A / (π / 3) < 3 / 2 := by rw [div_lt_iff₀ hc3]; linarith
  have h5 : (P.card : ℝ) < 4 := by linarith
  have : P.card < 4 := by exact_mod_cast h5
  omega

/-- A diametral point has `δ`-degree `≤ 3` (own copy: `degδ_le_three_of_D` of
`E132Main43Defs` is still a `sorry` there, and that file is not ours to edit).

TODO: none — proved.
What's missing: for a diametral partner `w` of `z` (`|zw| = Δ`) every `δ`-neighbour `q` has
`|q − w| ≤ Δ`, hence `(q − z)·(w − z) ≥ |q − z|²/2 > 0`: the unit vectors `q − z` lie in the
open half-circle around `(w − z)/Δ`; pairwise `≥ 1` apart means pairwise angle `≥ 60°`, so at
most 3.  Copy `card_sep_arc_le_four` (E132MainLocal / Main15N1) with the open half-circle cone.
Acceptance: no `sorry`.
Depends on: `dist_le_diam`, `one_le_dist`, `card_sep_arc_le_four` pattern. Difficulty M. -/
theorem degδ_le_three_of_D97 (hX : Normal X) {z : Pt} (hz : z ∈ Dset X) : degδ X z ≤ 3 := by
  obtain ⟨w, hw⟩ := (mem_filter.1 hz).2
  obtain ⟨hwX, hwy, hdw⟩ := mem_partners.1 hw
  have hΔ : 0 < diam X := by rw [← hdw]; exact dist_pos.2 (Ne.symm hwy)
  set n : Pt := (diam X)⁻¹ • (w - z) with hndef
  have hn : ‖n‖ = 1 := by
    rw [hndef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΔ), ← dist_eq_norm,
      dist_comm, hdw, inv_mul_cancel₀ hΔ.ne']
  have hzX : z ∈ X := (mem_filter.1 hz).1
  have hΔ1 : 1 ≤ diam X := by
    rw [← hdw]; exact one_le_dist hX.minDist_eq hzX hwX (Ne.symm hwy)
  unfold degδ
  apply card_sep_arc_le_three (y := z) hn (ε := (2 * diam X)⁻¹)
  · intro q hq
    obtain ⟨-, -, hd⟩ := mem_partners.1 hq
    rw [dist_comm, hd, hX.minDist_eq]
  · intro q hq q' hq' hne
    exact one_le_dist hX.minDist_eq (mem_partners.1 hq).1 (mem_partners.1 hq').1 hne
  · positivity
  · rw [inv_le_one₀ (by positivity)]; linarith
  · intro q hq
    obtain ⟨hqX, -, hd⟩ := mem_partners.1 hq
    rw [hX.minDist_eq] at hd
    have hqw := dist_le_diam hqX hwX
    have e1 := dist_sq_pt q w
    have e2 := dist_sq_pt z q
    have e3 := dist_sq_pt z w
    rw [hd] at e2; rw [hdw] at e3
    have hsq : dist q w ^ 2 ≤ diam X ^ 2 := pow_le_pow_left₀ dist_nonneg hqw 2
    rw [hndef, inner_smul_right, inner_pt]
    simp only [PiLp.sub_apply]
    have : 1 / 2 ≤ (q 0 - z 0) * (w 0 - z 0) + (q 1 - z 1) * (w 1 - z 1) := by nlinarith
    rw [mul_inv, ← div_eq_inv_mul (diam X)⁻¹ 2]
    calc (diam X)⁻¹ / 2 = (diam X)⁻¹ * (1 / 2) := by ring
      _ ≤ (diam X)⁻¹ * ((q 0 - z 0) * (w 0 - z 0) + (q 1 - z 1) * (w 1 - z 1)) :=
        mul_le_mul_of_nonneg_left this (by positivity)

/-- `t > 1` ⇒ points of `D` are at distance `> 1` from points of `X ∖ D`.

TODO: none — proved.
What's missing: partner `x ∈ X` of `z` with `dist z x = diam X`; `y ∉ D` gives
`dist y x ≤ dist2 X` (`dist_le_dist2`, `dist_ne_diam_of_not_mem_Dset`; if `x = y` then
`dist z y = diam X ≥ tgap X > 1` directly); triangle inequality.
Acceptance: no `sorry`.
Depends on: `dist_le_dist2`, `dist_ne_diam_of_not_mem_Dset`, `mem_partners`. Difficulty S. -/
theorem one_lt_dist_D_Y (ht : 1 < tgap X) {z y : Pt} (hz : z ∈ Dset X) (hy : y ∈ Yset X) :
    1 < dist z y := by
  obtain ⟨hyX, hyD⟩ := mem_sdiff.1 hy
  obtain ⟨hzX, x, hx⟩ := mem_filter.1 hz
  obtain ⟨hxX, hxz, hzx⟩ := mem_partners.1 hx
  have hxy : x ≠ y := by
    rintro rfl
    exact hyD (mem_filter.2 ⟨hxX, z, mem_partners.2 ⟨hzX, fun h => hxz h.symm,
      by rw [dist_comm]; exact hzx⟩⟩)
  have hyx : dist y x ≤ dist2 X :=
    dist_le_dist2 hyX hxX (dist_ne_diam_of_not_mem_Dset hyX hyD hxX hxy)
  have := dist_triangle z y x
  unfold tgap at ht
  linarith

/-- `e(X) = e(D) + e(X ∖ D)` when `t > 1`.

TODO: none — proved.
What's missing: every unit pair of `X` lies in `D` or in `Yset X` (by `one_lt_dist_D_Y`);
`mult_eq_card` and a filter/disjoint-union count on `pairsS`.  (`≤` suffices downstream.)
Acceptance: no `sorry`.
Depends on: `one_lt_dist_D_Y`, `mult_eq_card`, `mem_pairsAt`. Difficulty M. -/
theorem mult_split (ht : 1 < tgap X) :
    (mult X 1 : ℝ) ≤ mult (Dset X) 1 + mult (Yset X) 1 := by
  have h : mult X 1 ≤ mult (Dset X) 1 + mult (Yset X) 1 := by
    rw [Defs.mult_eq_card, Defs.mult_eq_card, Defs.mult_eq_card]
    refine (card_le_card fun z hz => ?_).trans (card_union_le _ _)
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨ha, hb, hab, hd⟩ := Defs.mem_pairsAt.1 hz
      by_cases haD : a ∈ Dset X
      · by_cases hbD : b ∈ Dset X
        · exact mem_union_left _ (Defs.mem_pairsAt.2 ⟨haD, hbD, hab, hd⟩)
        · have := one_lt_dist_D_Y ht haD (mem_sdiff.2 ⟨hb, hbD⟩); linarith
      · by_cases hbD : b ∈ Dset X
        · have := one_lt_dist_D_Y ht hbD (mem_sdiff.2 ⟨ha, haD⟩)
          rw [dist_comm] at this; linarith
        · exact mem_union_right _
            (Defs.mem_pairsAt.2 ⟨mem_sdiff.2 ⟨ha, haD⟩, mem_sdiff.2 ⟨hb, hbD⟩, hab, hd⟩)
  exact_mod_cast h

/-- Unit edges inside `S ∩ D` number `≤ |S ∩ D| + cBad` for `τ > 1`.

TODO: none — proved.
What's missing: unit pairs of `S ∩ D` are `edges X` whose both ends are in `D`; good ones are
T-edges (`good_subset_T_union_rungs`, `rungs_eq_empty`); a T-edge `pq` with both ends in `S ∩ D`
makes `q` the left or right T-neighbour of `p` (as in `card_tEdges_le`), each unique (`T1`), so
`two_mul_card_le_of_deg_le` with `V = S ∩ D`, `k = 2`; bad ones `≤ cBad` (`card_bad_le`).
Acceptance: no `sorry`.
Depends on: `dirField_nonempty`, `good_subset_T_union_rungs`, `rungs_eq_empty`, `T1`,
`card_bad_le`, `two_mul_card_le_of_deg_le`. Difficulty M. -/
theorem mult_SD_le (hX : Normal X) (hτ : 1 < tau X) :
    (mult (Sset X ∩ Dset X) 1 : ℝ) ≤ (Sset X ∩ Dset X).card + cBad := by
  obtain ⟨F⟩ := dirField_nonempty X
  set V := Sset X ∩ Dset X with hV
  set E' := (tEdges X F).filter (fun z => ∀ p ∈ z, p ∈ V) with hE'
  have hsub : (pairsS V).filter (fun z => pairDist z = 1) ⊆ E' ∪ bad X F := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨ha, hb, hab, hd⟩ := Defs.mem_pairsAt.1 hz
      have hze : s(a, b) ∈ edges X := by
        unfold edges
        rw [hX.minDist_eq]
        exact Defs.mem_pairsAt.2 ⟨(mem_inter.1 ha).1, (mem_inter.1 hb).1, hab, hd⟩
      by_cases hg : IsGood F s(a, b)
      · have hgood : s(a, b) ∈ good X F := mem_filter.2 ⟨hze, hg⟩
        have := good_subset_T_union_rungs hX F (by unfold beta; linarith) hgood
        rw [rungs_eq_empty F hτ, union_empty] at this
        refine mem_union_left _ (mem_filter.2 ⟨this, fun p hp => ?_⟩)
        rcases Sym2.mem_iff.1 hp with rfl | rfl
        · exact ha
        · exact hb
      · exact mem_union_right _ (mem_filter.2 ⟨hze, hg⟩)
  have h2 := two_mul_card_le_of_deg_le (V := V) (E := E') (k := 2) ?_ ?_
  · have hc : mult V 1 ≤ E'.card + (bad X F).card := by
      rw [Defs.mult_eq_card]; exact (card_le_card hsub).trans (card_union_le _ _)
    have hb := card_bad_le hX F
    have : (mult V 1 : ℝ) ≤ E'.card + (bad X F).card := by exact_mod_cast hc
    have : (E'.card : ℝ) ≤ V.card := by exact_mod_cast (by omega : E'.card ≤ V.card)
    linarith
  · intro z hz
    obtain ⟨hzT, hzV⟩ := mem_filter.1 hz
    have hz' : z ∈ edges X := (mem_filter.1 (mem_filter.1 hzT).1).1
    exact ⟨(mem_edges hz').1, hzV⟩
  · intro p _
    have hsub : E'.filter (fun z => p ∈ z) ⊆
        ((Sset X).filter (IsSideT F 1 p) ∪ (Sset X).filter (IsSideT F (-1) p)).image
          (fun q => s(p, q)) := by
      intro z hz
      obtain ⟨hzE, hpz⟩ := mem_filter.1 hz
      have hzT := (mem_filter.1 hzE).1
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
      have hl := Curve.lagrange (q - p) (F.u p)
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

/-- **The `D`-part** (§5.3 step 2): `Def(G[D]) ≥ 2|S ∩ D| − cBad`.

TODO: none — proved.
What's missing: `mult_le_add_sum (S ∩ D) D 1`: `e(D) ≤ e(S ∩ D) + Σ_{z ∈ D ∖ S} deg z`;
`deg ≤ 3` (`degδ_le_three_of_D97`; `partners (Dset X) 1 z ⊆ partners X (minDist X) z`);
`|D| = |S ∩ D| + |D ∖ S|`; `mult_SD_le`.
Acceptance: no `sorry`.
Depends on: `mult_le_add_sum`, `degδ_le_three_of_D97`, `mult_SD_le`. Difficulty M. -/
theorem dpart (hX : Normal X) (hτ : 1 < tau X) :
    2 * ((Sset X ∩ Dset X).card : ℝ) - cBad ≤ defc (Dset X) := by
  have hSD : Sset X ∩ Dset X ⊆ Dset X := inter_subset_right
  have h := Defs.mult_le_add_sum (Sset X ∩ Dset X) (Dset X) 1
  have hs : ∑ x ∈ Dset X \ (Sset X ∩ Dset X), (partners (Dset X) 1 x).card ≤
      3 * (Dset X \ (Sset X ∩ Dset X)).card := by
    calc ∑ x ∈ Dset X \ (Sset X ∩ Dset X), (partners (Dset X) 1 x).card
        ≤ ∑ _x ∈ Dset X \ (Sset X ∩ Dset X), 3 := by
          refine sum_le_sum fun x hx => le_trans (card_le_card fun q hq => ?_)
            (degδ_le_three_of_D97 hX (mem_sdiff.1 hx).1)
          obtain ⟨hqD, hqx, hd⟩ := Defs.mem_partners.1 hq
          exact Defs.mem_partners.2 ⟨(mem_filter.1 hqD).1, hqx, by rw [hX.minDist_eq]; exact hd⟩
      _ = 3 * (Dset X \ (Sset X ∩ Dset X)).card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hcard := card_sdiff_add_card_eq_card hSD
  have hm := mult_SD_le hX hτ
  have : (mult (Dset X) 1 : ℝ) ≤ mult (Sset X ∩ Dset X) 1 +
      3 * (Dset X \ (Sset X ∩ Dset X)).card := by exact_mod_cast (by omega)
  have hc' : ((Dset X \ (Sset X ∩ Dset X)).card : ℝ) + (Sset X ∩ Dset X).card = (Dset X).card := by
    exact_mod_cast hcard
  unfold defc
  linarith

end

end Erdos132Main

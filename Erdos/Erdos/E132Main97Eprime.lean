import Erdos.E132Main97Defs

/-!
# Erdős Problem 132, Theorem E′ (outer layer): `Def(G[X ∖ D]) ≥ 2|S ∖ D| − CE·n^{2/3}`

`problems/132/angle_R6.md` §5.2, Step 0 (parameters, fallback F1), Step 1 (shell removal),
Step 7 (assembly of the error terms).  The topological heart (Steps 2–7) is the hypothesis
`hcore : CoreE` (proved, or not, in `E132Main97Core.lean`).

Deviations from the paper:
* fallbacks (F2), (F3) are replaced by the single case `|A| ≤ 1000h` (perimeter-free; `CoreE`
  absorbs the implication `|A| > 1000h ⇒ r_in(K) > h ∧ per K ≥ 100h`);
* (F1) is not needed: `Normal X` has `Δ₂ ≥ 10⁴`, so `ρ₀ ≥ 1`;
* packing `n ≤ (2Δ + 2)²` (grid of cells of side `7/10`) instead of `(2Δ + 1)²`; `CE = 2·10⁷` (absorbs `Eh = 3·10⁶h²`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open Erdos132Layer (sqd dist_sq_eq_sqd)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- **Step 1 (shell removal)**: `Def(G[Y]) ≥ Def(G[Yout ρ]) − 3|Yshell ρ|`.

TODO: none — proved.
What's missing: no unit pair joins `Yout` and `Yin` (`one_lt_dist_out_in`), so
`e(Y) ≤ e(Yout) + e(Yin) + Σ_{y ∈ shell} deg y ≤ e(Yout) + 3|Yin| + 6|shell|`
(`mult_le_add_sum` twice; `defc_nonneg` for `Yin`; degree `≤ 6` from
`card_partners_minDist_le`), and `card_Yset_split`.
Acceptance: no `sorry`.
Depends on: `one_lt_dist_out_in`, `card_Yset_split`, `defc_nonneg`, `mult_le_add_sum`,
`card_partners_minDist_le`. Difficulty M. -/
theorem shell_removal (h1 : minDist X = 1) (ρ : ℝ) :
    defc (Yout X ρ) - 3 * (Yshell X ρ).card ≤ defc (Yset X) := by
  obtain ⟨hcard, -, hdo, -⟩ := card_Yset_split (X := X) ρ
  have hYX : Yset X ⊆ X := sdiff_subset
  have hout : Yout X ρ ⊆ Yset X := filter_subset _ _
  have hin : Yin X ρ ⊆ Yset X := filter_subset _ _
  have hOI : Yout X ρ ∪ Yin X ρ ⊆ Yset X := union_subset hout hin
  -- `e(Y) ≤ e(Yout ∪ Yin) + Σ_{shell} deg`
  have h := Defs.mult_le_add_sum (Yout X ρ ∪ Yin X ρ) (Yset X) 1
  have hs : ∑ x ∈ Yset X \ (Yout X ρ ∪ Yin X ρ), (partners (Yset X) 1 x).card ≤
      6 * (Yset X \ (Yout X ρ ∪ Yin X ρ)).card := by
    calc ∑ x ∈ Yset X \ (Yout X ρ ∪ Yin X ρ), (partners (Yset X) 1 x).card
        ≤ ∑ _x ∈ Yset X \ (Yout X ρ ∪ Yin X ρ), 6 := by
          refine sum_le_sum fun x _ => le_trans (card_le_card fun q hq => ?_)
            (card_partners_minDist_le X x)
          obtain ⟨hqY, hqx, hd⟩ := Defs.mem_partners.1 hq
          exact Defs.mem_partners.2 ⟨hYX hqY, hqx, by rw [h1]; exact hd⟩
      _ = 6 * (Yset X \ (Yout X ρ ∪ Yin X ρ)).card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hsd := card_sdiff_add_card_eq_card hOI
  rw [card_union_of_disjoint hdo] at hsd
  -- `e(Yout ∪ Yin) ≤ e(Yout) + e(Yin)`
  have hsplit : mult (Yout X ρ ∪ Yin X ρ) 1 ≤ mult (Yout X ρ) 1 + mult (Yin X ρ) 1 := by
    rw [Defs.mult_eq_card, Defs.mult_eq_card, Defs.mult_eq_card]
    refine (card_le_card fun z hz => ?_).trans (card_union_le _ _)
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨ha, hb, hab, hd⟩ := Defs.mem_pairsAt.1 hz
      rcases mem_union.1 ha with ha | ha <;> rcases mem_union.1 hb with hb | hb
      · exact mem_union_left _ (Defs.mem_pairsAt.2 ⟨ha, hb, hab, hd⟩)
      · have := one_lt_dist_out_in ha hb; linarith
      · have := one_lt_dist_out_in hb ha; rw [dist_comm] at this; linarith
      · exact mem_union_right _ (Defs.mem_pairsAt.2 ⟨ha, hb, hab, hd⟩)
  have hinD := defc_nonneg h1 (hin.trans hYX)
  unfold defc at hinD ⊢
  have e1 : (mult (Yset X) 1 : ℝ) ≤ mult (Yout X ρ) 1 + mult (Yin X ρ) 1 +
      6 * (Yset X \ (Yout X ρ ∪ Yin X ρ)).card := by exact_mod_cast (by omega)
  have e2 : ((Yset X \ (Yout X ρ ∪ Yin X ρ)).card : ℝ) = (Yshell X ρ).card := by
    have : (Yset X \ (Yout X ρ ∪ Yin X ρ)).card = (Yshell X ρ).card := by omega
    exact_mod_cast this
  have e3 : ((Yset X).card : ℝ) = (Yout X ρ).card + (Yshell X ρ).card + (Yin X ρ).card := by
    exact_mod_cast hcard
  rw [e2] at e1
  linarith

/-- **Step 0 (pigeonhole)**: among the `ρ₀` disjoint shells `ρ ∈ [ρ₀, 2ρ₀)` one has
`|Yshell ρ| · ρ₀ ≤ n`.

TODO: none — proved.
What's missing: `disjoint_Yshell`; `Σ_{ρ ∈ [ρ₀, 2ρ₀)} |Yshell ρ| ≤ |X|` (`card_biUnion`,
subsets of `X`); `exists_le_of_sum_le` / min ≤ average on `Finset.Ico ρ₀ (2ρ₀)`.
Acceptance: no `sorry`.
Depends on: `disjoint_Yshell`. Difficulty S–M. -/
theorem shell_pigeonhole (ρ₀ : ℕ) (hρ₀ : 1 ≤ ρ₀) :
    ∃ ρ : ℕ, ρ₀ ≤ ρ ∧ ρ < 2 * ρ₀ ∧ ((Yshell X ρ).card : ℝ) * ρ₀ ≤ X.card := by
  set I := Finset.Ico ρ₀ (2 * ρ₀)
  have hI : I.Nonempty := ⟨ρ₀, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
  have hIc : I.card = ρ₀ := by simp [I]; omega
  have hdisj : (I : Set ℕ).PairwiseDisjoint (fun ρ : ℕ => Yshell X ρ) :=
    fun a _ b _ hab => disjoint_Yshell hab
  have hsub : I.biUnion (fun ρ : ℕ => Yshell X ρ) ⊆ X := by
    intro y hy
    obtain ⟨ρ, -, hy⟩ := mem_biUnion.1 hy
    exact (mem_sdiff.1 (mem_filter.1 hy).1).1
  have hsum : ∑ ρ ∈ I, (Yshell X ρ).card ≤ X.card := by
    rw [← card_biUnion hdisj]; exact card_le_card hsub
  have hsum' : ∑ ρ ∈ I, ((Yshell X ρ).card : ℝ) * ρ₀ ≤ ∑ _ρ ∈ I, (X.card : ℝ) := by
    rw [← sum_mul, sum_const, hIc, nsmul_eq_mul, mul_comm]
    have : (∑ ρ ∈ I, ((Yshell X ρ).card : ℝ)) ≤ X.card := by exact_mod_cast hsum
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  obtain ⟨ρ, hρ, hle⟩ := exists_le_of_sum_le hI hsum'
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hρ
  exact ⟨ρ, h1, h2, hle⟩

/-- **Packing**: with `δ = 1`, `n ≤ (2Δ + 2)²`.

TODO: none — proved.
What's missing: the grid argument of `card_lt_N0` (E132MainDefs) with a general diameter:
`X` lies in an axis-parallel square of side `Δ`; cells of side `7/10` hold `≤ 1` point each;
at most `(⌊Δ/0.7⌋ + 1)² ≤ (2Δ + 2)²` cells.  (Or reuse `card_sep_ball_le` if its bound fits.)
Acceptance: no `sorry`.
Depends on: `card_lt_N0` pattern (`floor_cell_lt`, `close_of_floor_eq`). Difficulty M. -/
theorem card_le_sq_diam (h1 : minDist X = 1) : (X.card : ℝ) ≤ (2 * diam X + 2) ^ 2 := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simp; positivity
  have hD0 := Defs.diam_nonneg X
  set m0 := X.inf' hne (fun x : Pt => x 0)
  set m1 := X.inf' hne (fun x : Pt => x 1)
  obtain ⟨a, ha, hma⟩ := exists_mem_eq_inf' hne (fun x : Pt => x 0)
  obtain ⟨b, hb, hmb⟩ := exists_mem_eq_inf' hne (fun x : Pt => x 1)
  have lo0 : ∀ x ∈ X, 0 ≤ x 0 - m0 := fun x hx => sub_nonneg.2 (inf'_le _ hx)
  have lo1 : ∀ x ∈ X, 0 ≤ x 1 - m1 := fun x hx => sub_nonneg.2 (inf'_le _ hx)
  have hi0 : ∀ x ∈ X, x 0 - m0 ≤ diam X := fun x hx => by
    have h := (Defs.coord_sq_le x a).1
    have hd := Defs.dist_le_diam hx ha
    have := lo0 x hx
    have hm : m0 = a 0 := hma
    rw [hm] at this ⊢
    nlinarith [dist_nonneg (x := x) (y := a)]
  have hi1 : ∀ x ∈ X, x 1 - m1 ≤ diam X := fun x hx => by
    have h := (Defs.coord_sq_le x b).2
    have hd := Defs.dist_le_diam hx hb
    have := lo1 x hx
    have hm : m1 = b 1 := hmb
    rw [hm] at this ⊢
    nlinarith [dist_nonneg (x := x) (y := b)]
  set K : ℕ := ⌊diam X / (7 / 10)⌋₊ + 1 with hK
  have hcell : ∀ {t : ℝ}, 0 ≤ t → t ≤ diam X → ⌊t / (7 / 10)⌋₊ < K := by
    intro t ht htD
    rw [hK, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right htD (by norm_num))
  let f : Pt → ℕ × ℕ := fun x => (⌊(x 0 - m0) / (7 / 10)⌋₊, ⌊(x 1 - m1) / (7 / 10)⌋₊)
  have hmaps : ∀ x ∈ X, f x ∈ range K ×ˢ range K := fun x hx => by
    rw [mem_product, mem_range, mem_range]
    exact ⟨hcell (lo0 x hx) (hi0 x hx), hcell (lo1 x hx) (hi1 x hx)⟩
  have hinj : Set.InjOn f X := by
    intro x hx y hy hxy
    by_contra hne'
    have e := Prod.mk.inj hxy
    have c0 := Defs.close_of_floor_eq (lo0 x hx) (lo0 y hy) e.1
    have c1 := Defs.close_of_floor_eq (lo1 x hx) (lo1 y hy) e.2
    have hge := minDist_le_dist hx hy hne'
    rw [h1] at hge
    have hsq : 1 ≤ sqd x y := by
      rw [← dist_sq_eq_sqd]; nlinarith
    have e0 : x 0 - m0 - (y 0 - m0) = x 0 - y 0 := by ring
    have e1 : x 1 - m1 - (y 1 - m1) = x 1 - y 1 := by ring
    rw [e0] at c0; rw [e1] at c1
    rw [sqd] at hsq
    norm_num at c0 c1
    linarith
  have hcard := card_le_card_of_injOn f hmaps hinj
  rw [card_product, card_range] at hcard
  have hKr : (K : ℝ) ≤ 2 * diam X + 2 := by
    rw [hK]; push_cast
    have := Nat.floor_le (show 0 ≤ diam X / (7 / 10) by positivity)
    have : diam X / (7 / 10) ≤ 2 * diam X + 1 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have : (X.card : ℝ) ≤ (K : ℝ) * K := by exact_mod_cast hcard
  nlinarith [Nat.cast_nonneg (α := ℝ) K]

/-- **Step 7, arithmetic**: the error terms.  With `n ≥ 4`, `Δ₂ ≥ 10⁴`, `n ≤ (4Δ₂)²`,
`ρ₀ = ⌊min(n^{1/3}, Δ₂/400)⌋`, `ρ₀ ≤ ρ < 2ρ₀`, `h = ρ + ½`:
`h < Δ₂/200`, `2000 h ≤ CE n^{2/3}`, and `E(h) + 3n/ρ₀ ≤ CE n^{2/3}`.

TODO: none — proved.
What's missing: real arithmetic with `rpow`: `h < 2n^{1/3}`, `⌊m⌋ ≥ m/2` for `m ≥ 1`,
`3n/ρ₀ ≤ 6n^{2/3} + 2400 n/Δ₂ ≤ 6n^{2/3} + 9600 √n`, `E(h) ≤ 1.2·10⁷ n^{2/3}`,
`√n ≤ n^{2/3}`, `n^{1/3} ≤ n^{2/3}` (`n ≥ 1`).
Acceptance: no `sorry`.
Depends on: nothing (analysis of `Real.rpow`, `Nat.floor`). Difficulty M. -/
theorem eprime_arith {n D₂ : ℝ} {ρ₀ ρ : ℕ} (hn : 4 ≤ n) (hD : 10 ^ 4 ≤ D₂) (hnD : n ≤ (4 * D₂) ^ 2)
    (hρ₀ : ρ₀ = ⌊min (n ^ (1 / 3 : ℝ)) (D₂ / 400)⌋₊) (_h₁ : ρ₀ ≤ ρ) (h₂ : ρ < 2 * ρ₀) :
    1 ≤ ρ₀ ∧ ((ρ : ℝ) + 1 / 2) < D₂ / 200 ∧ 2000 * ((ρ : ℝ) + 1 / 2) ≤ CE * n ^ (2 / 3 : ℝ) ∧
      Eh ((ρ : ℝ) + 1 / 2) + 3 * n / ρ₀ ≤ CE * n ^ (2 / 3 : ℝ) := by
  have hn0 : 0 ≤ n := by linarith
  set c := n ^ (1 / 3 : ℝ) with hcdef
  have hc3 : c ^ 3 = n := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have hn23 : n ^ (2 / 3 : ℝ) = c ^ 2 := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  rw [hn23]
  have hc1 : 1 ≤ c := Real.one_le_rpow (by linarith) (by norm_num)
  set m := min c (D₂ / 400) with hm
  have hm1 : 1 ≤ m := le_min hc1 (by linarith)
  have hmc : m ≤ c := min_le_left _ _
  have hmD : m ≤ D₂ / 400 := min_le_right _ _
  have hρ₀1 : 1 ≤ ρ₀ := by rw [hρ₀]; exact Nat.le_floor (by simpa using hm1)
  have hρ₀m : (ρ₀ : ℝ) ≤ m := by rw [hρ₀]; exact Nat.floor_le (by linarith)
  have hmρ₀ : m < ρ₀ + 1 := by rw [hρ₀]; exact Nat.lt_floor_add_one m
  have hρ₀r : (1 : ℝ) ≤ ρ₀ := by exact_mod_cast hρ₀1
  have hρ : (ρ : ℝ) + 1 ≤ 2 * ρ₀ := by exact_mod_cast h₂
  have hh2c : (ρ : ℝ) + 1 / 2 < 2 * c := by linarith
  have hh0 : (0 : ℝ) ≤ (ρ : ℝ) + 1 / 2 := by positivity
  refine ⟨hρ₀1, by linarith, ?_, ?_⟩
  · have : c ≤ c ^ 2 := by nlinarith
    unfold CE; nlinarith
  · have hE : Eh ((ρ : ℝ) + 1 / 2) ≤ 12 * 10 ^ 6 * c ^ 2 := by
      unfold Eh
      have h1 : ((ρ : ℝ) + 1 / 2) ^ 2 ≤ 4 * c ^ 2 := by nlinarith
      nlinarith
    have hm2 : m ≤ 2 * ρ₀ := by linarith
    have hshell : 3 * n / ρ₀ ≤ 9600 * c ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      rcases min_choice c (D₂ / 400) with hmin | hmin
      · -- `m = c`: `3n ≤ 6 c² · c ≤ 9600 c² ρ₀`
        rw [hm, hmin] at hm2
        rw [← hc3]; nlinarith
      · -- `m = Δ₂/400`: `c ≤ 4Δ₂`, so `3n = 3c³ ≤ 12 c² Δ₂ ≤ 9600 c² ρ₀`
        rw [hm, hmin] at hm2
        have hc4 : c ≤ 4 * D₂ := by
          by_contra hlt
          push Not at hlt
          have : (4 * D₂) ^ 3 < c ^ 3 := by
            exact pow_lt_pow_left₀ hlt (by linarith) (by norm_num)
          nlinarith
        rw [← hc3]; nlinarith
    have := sq_nonneg c
    unfold CE; linarith

/-- **Theorem E′** (applied to `Y = X ∖ D`, §5.1 "Application"), from `CoreE`:
`Def(G[X ∖ D]) ≥ 2|S ∖ D| − CE·n^{2/3}`.

TODO: none — proved (modulo `hcore`).
What's missing: `n ≤ (2Δ + 2)² ≤ (4Δ₂)²` (`card_le_sq_diam`, `Normal.nondeg`, `Δ₂ ≥ 10⁴`);
choose `ρ₀`, `ρ` (`shell_pigeonhole`), `eprime_arith`; case `|A| ≤ 1000h`: `defc_nonneg`;
case `|A| > 1000h`: `hcore` + `shell_removal`.
Acceptance: no `sorry` (modulo `hcore`).
Depends on: `card_le_sq_diam`, `shell_pigeonhole`, `eprime_arith`, `shell_removal`,
`defc_nonneg`. Difficulty M. -/
theorem eprime (hcore : CoreE) (hX : Normal X) :
    2 * ((Aset X).card : ℝ) - CE * (X.card : ℝ) ^ (2 / 3 : ℝ) ≤ defc (Yset X) := by
  have h1 := hX.minDist_eq
  have hn : (4 : ℝ) ≤ X.card := by exact_mod_cast hX.four_le
  have hD := hX.large
  have hnd := hX.nondeg
  have hΔ0 := Defs.diam_nonneg X
  have hnD : (X.card : ℝ) ≤ (4 * dist2 X) ^ 2 := by
    have := card_le_sq_diam h1
    have h2 : 2 * diam X + 2 ≤ 4 * dist2 X := by linarith
    have h3 : (2 * diam X + 2) ^ 2 ≤ (4 * dist2 X) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
    linarith
  set ρ₀ := ⌊min ((X.card : ℝ) ^ (1 / 3 : ℝ)) (dist2 X / 400)⌋₊ with hρ₀
  have hρ₀1 : 1 ≤ ρ₀ := by
    rw [hρ₀]
    refine Nat.le_floor ?_
    push_cast
    exact le_min (Real.one_le_rpow (by linarith) (by norm_num)) (by linarith)
  obtain ⟨ρ, hρ1, hρ2, hsh⟩ := shell_pigeonhole (X := X) ρ₀ hρ₀1
  obtain ⟨-, hh, hA2000, hEh⟩ := eprime_arith hn hD hnD hρ₀ hρ1 hρ2
  have hsr := shell_removal h1 (ρ : ℝ)
  have hdn : 0 ≤ defc (Yset X) := defc_nonneg h1 sdiff_subset
  have hρ₀r : (0 : ℝ) < ρ₀ := by exact_mod_cast hρ₀1
  have hshell : 3 * ((Yshell X ρ).card : ℝ) ≤ 3 * (X.card : ℝ) / ρ₀ := by
    rw [le_div_iff₀ hρ₀r]; linarith
  by_cases hA : 1000 * ((ρ : ℝ) + 1 / 2) < (Aset X).card
  · have := hcore X ρ hX (by omega) hh hA
    linarith
  · push Not at hA
    linarith

end

end Erdos132Main

import Mathlib

/-!
# Erdős Problem 468 — a disproof of `f(N) = o(N)` (even for almost all `N`)

For `n` let `D_n` be the set of sums `d₁, d₁+d₂, d₁+d₂+d₃, …` where `1 < d₁ < d₂ < ⋯` are the
divisors of `n`, and let `f(N)` be the least `n` with `N ∈ D_n`. Erdős and Graham asked whether
`f(N) = o(N)`, perhaps just for almost all `N` ([erdosproblems.com/468]).

We show the answer is **no**: for every `K ≥ 1`,
`#{N ≤ X : ∃ n, K n ≤ N ∧ N ∈ D_n} ≤ S X / K²` for an absolute constant `S`. Hence for large `K`
at least half of all `N` have `f(N) > N / K` (or no `f(N)` at all).

Proof idea. If `N ∈ D_n` is the prefix sum up to the divisor `d = n / e`, then
`N ≤ ∑_{d' ∣ n, d' ≤ d} d' = n · T_e(n)` with `T_e(n) = ∑_{e' ∣ n, e' ≥ e} 1/e'`.
So `K n ≤ N` forces `T_e(n) ≥ K`, and by Markov
`#{(n, e) : n ≤ Y, T_e(n) ≥ K} ≤ K⁻¹ ∑_{n ≤ Y} ∑_{e ∣ n} T_e(n) ≤ K⁻¹ S Y`, where
`∑_{n ≤ Y} ∑_{e ∣ n} T_e(n) = ∑_{e ≤ e'} (1/e') #{n ≤ Y : lcm(e,e') ∣ n}
  ≤ Y ∑_{e'} e'⁻² ∑_{g ∣ e'} H(e'/g) ≤ Y ζ(2) ∑_b H_b / b²`.
-/

open Finset Filter Asymptotics Real

namespace Erdos468

/-- The sum of the divisors `d` of `n` with `1 < d ≤ x` (same definition as the
formal-conjectures PR #4076). For `x` a divisor of `n`, this is a prefix sum `d₁ + ⋯ + dⱼ`. -/
def divisorPrefixSum (n x : ℕ) : ℕ :=
  ∑ d ∈ (Nat.divisors n).filter (fun d => 1 < d ∧ d ≤ x), d

/-- The set `D_n` of prefix sums of the divisors `> 1` of `n`. -/
def D (n : ℕ) : Finset ℕ :=
  ((Nat.divisors n).filter (1 < ·)).image (divisorPrefixSum n)

/-- `n` is the least index with `N ∈ D_n`. -/
def IsMinimalDPreimage (N n : ℕ) : Prop :=
  N ∈ D n ∧ ∀ m : ℕ, N ∈ D m → n ≤ m

/-- Proportion of `N < X` lying in `s`. -/
noncomputable def partialDensity (s : Set ℕ) (X : ℕ) : ℝ := by
  classical
  exact ((range X).filter (· ∈ s)).card / X

/-- `s` has natural density `a`. -/
def HasDensity (s : Set ℕ) (a : ℝ) : Prop :=
  Tendsto (partialDensity s) atTop (nhds a)

/-- The "almost all" version of Erdős 468 (as in formal-conjectures PR #4076). -/
def Erdos468AlmostAll : Prop :=
  ∃ f : ℕ → ℕ, HasDensity {N | IsMinimalDPreimage N (f N)} 1 ∧
    (fun N : ℕ => (f N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

/-- `T n e = ∑_{e' ∣ n, e ≤ e'} 1/e'`. -/
noncomputable def T (n e : ℕ) : ℝ :=
  ∑ e' ∈ (Nat.divisors n).filter (e ≤ ·), (e' : ℝ)⁻¹

/-- `N < X` is "covered at level `K`" if `N ∈ D_n` for some `n` with `K n ≤ N`. -/
noncomputable def covered (K X : ℕ) : Finset ℕ := by
  classical
  exact (range X).filter (fun N => ∃ n, K * n ≤ N ∧ N ∈ D n)

/-- The absolute constant `S = (∑ 1/g²) (∑ H_b / b²)`. -/
noncomputable def S : ℝ :=
  (∑' g : ℕ, ((g : ℝ) ^ 2)⁻¹) * ∑' b : ℕ, (harmonic b : ℝ) / (b : ℝ) ^ 2

/-! ### Step 1: a prefix sum at `d = n / e` is at most `n · T n e` -/

/-- Prefix-sum bound.
Depends on: nothing. -/
theorem prefixSum_le (n e : ℕ) (hn : 0 < n) (he : e ∣ n) :
    (divisorPrefixSum n (n / e) : ℝ) ≤ n * T n e := by
  classical
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hn
  unfold divisorPrefixSum T
  push_cast
  rw [Finset.mul_sum]
  set A := (Nat.divisors n).filter (fun d => 1 < d ∧ d ≤ n / e) with hA
  set B := (Nat.divisors n).filter (e ≤ ·) with hB
  have hmemA : ∀ d ∈ A, d ∣ n ∧ 1 < d ∧ d ≤ n / e := by
    intro d hd
    simp only [hA, Finset.mem_filter, Nat.mem_divisors] at hd
    exact ⟨hd.1.1, hd.2⟩
  have hinj : Set.InjOn (fun d => n / d) A := by
    intro a ha b hb hab
    obtain ⟨ha1, -, -⟩ := hmemA a ha
    obtain ⟨hb1, -, -⟩ := hmemA b hb
    simp only at hab
    rw [← Nat.div_div_self ha1 hn.ne', hab, Nat.div_div_self hb1 hn.ne']
  have himg : A.image (fun d => n / d) ⊆ B := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hd1, hd2, hd3⟩ := hmemA d hd
    have hd0 : 0 < d := by omega
    simp only [hB, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.div_dvd_of_dvd hd1, hn.ne'⟩, ?_⟩
    rw [Nat.le_div_iff_mul_le hd0]
    have := (Nat.le_div_iff_mul_le he0).1 hd3
    linarith [mul_comm d e]
  calc ∑ d ∈ A, (d : ℝ) = ∑ d ∈ A, (n : ℝ) * (((n / d : ℕ) : ℝ))⁻¹ := by
        refine Finset.sum_congr rfl (fun d hd => ?_)
        obtain ⟨hd1, hd2, -⟩ := hmemA d hd
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
        rw [Nat.cast_div hd1 hd0]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
    _ = ∑ x ∈ A.image (fun d => n / d), (n : ℝ) * (x : ℝ)⁻¹ :=
        (Finset.sum_image (f := fun x : ℕ => (n : ℝ) * (x : ℝ)⁻¹) hinj).symm
    _ ≤ ∑ x ∈ B, (n : ℝ) * (x : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)

/-! ### Step 2: covered values come from pairs `(n, e)` with `T n e ≥ K` -/

/-- Covered count ≤ number of pairs.
Depends on: `prefixSum_le`. -/
theorem card_covered_le_pairs (K X : ℕ) (hK : 1 ≤ K) :
    ((covered K X).card : ℝ) ≤
      ∑ n ∈ Icc 1 (X / K), (((Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e)).card : ℝ) := by
  classical
  set P := (Icc 1 (X / K)).sigma (fun n => (Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e))
    with hP
  have hsub : covered K X ⊆ P.image (fun p => divisorPrefixSum p.1 (p.1 / p.2)) := by
    intro N hN
    simp only [covered, mem_filter, mem_range] at hN
    obtain ⟨hNX, n, hKn, hND⟩ := hN
    simp only [D, mem_image, mem_filter, Nat.mem_divisors] at hND
    obtain ⟨d, ⟨⟨hdn, hn0⟩, hd1⟩, rfl⟩ := hND
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    refine mem_image.2 ⟨⟨n, n / d⟩, ?_, ?_⟩
    · simp only [hP, mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors]
      refine ⟨⟨hnpos, ?_⟩, ⟨Nat.div_dvd_of_dvd hdn, hn0⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
        omega
      · have h1 := prefixSum_le n (n / d) hnpos (Nat.div_dvd_of_dvd hdn)
        rw [Nat.div_div_self hdn hn0] at h1
        have h2 : ((K * n : ℕ) : ℝ) ≤ divisorPrefixSum n d := by exact_mod_cast hKn
        push_cast at h2
        have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
        exact le_of_mul_le_mul_left (by linarith) hn'
    · simp [Nat.div_div_self hdn hn0]
  calc ((covered K X).card : ℝ) ≤ (P.image (fun p => divisorPrefixSum p.1 (p.1 / p.2))).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ P.card := by exact_mod_cast card_image_le
    _ = _ := by rw [hP, card_sigma]; push_cast; rfl

/-! ### Step 3: Markov -/

/-- Markov inequality on divisors.
Depends on: `T` nonneg. -/
theorem markov_divisors (n K : ℕ) :
    (K : ℝ) * ((Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e)).card ≤
      ∑ e ∈ Nat.divisors n, T n e := by
  classical
  have hT : ∀ e, 0 ≤ T n e := fun e => Finset.sum_nonneg (fun _ _ => by positivity)
  calc (K : ℝ) * ((Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e)).card
      = ∑ e ∈ (Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e), (K : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ e ∈ (Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e), T n e :=
        Finset.sum_le_sum (fun e he => (Finset.mem_filter.1 he).2)
    _ ≤ ∑ e ∈ Nat.divisors n, T n e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hT _)

/-! ### Step 4: the average of `∑_{e ∣ n} T n e` is bounded -/

/-- Summability of `H_b / b²`.
Depends on: `harmonic_le_one_add_log`, p-series. -/
theorem summable_harmonic_div_sq :
    Summable (fun b : ℕ => (harmonic b : ℝ) / (b : ℝ) ^ 2) := by
  have hs : Summable (fun b : ℕ => 2 * ((b : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
  have hHnn : ∀ b : ℕ, (0 : ℝ) ≤ harmonic b := fun b => by
    unfold harmonic; push_cast; positivity
  refine Summable.of_nonneg_of_le (fun b => div_nonneg (hHnn b) (by positivity)) (fun b => ?_) hs
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hH : (harmonic b : ℝ) ≤ 1 + Real.log b := harmonic_le_one_add_log b
  have hlog : Real.log b ≤ 2 * Real.sqrt b - 2 := by
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hb0)
    rw [Real.log_sqrt hb0.le] at this
    linarith
  have hsq : (harmonic b : ℝ) ≤ 2 * Real.sqrt b := by linarith
  have hpow : (b : ℝ) ^ 2 = (b : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb0]
    norm_num
  have hp0 : (0 : ℝ) < (b : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  rw [div_le_iff₀ (by positivity), hpow]
  have : 2 * ((b : ℝ) ^ ((3 : ℝ) / 2))⁻¹ * ((b : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt b)
      = 2 * Real.sqrt b := by field_simp
  rw [this]
  exact hsq

/-- The key average bound `∑_{n ∈ [1,Y]} ∑_{e ∣ n} T n e ≤ S * Y`. -/
lemma harmonic_nonneg' (b : ℕ) : (0 : ℝ) ≤ harmonic b := by
  unfold harmonic; push_cast; positivity

lemma divisors_eq_filter {n Y : ℕ} (hn : n ∈ Icc 1 Y) :
    Nat.divisors n = (Icc 1 Y).filter (· ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc] at hn ⊢
  constructor
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, by omega⟩

lemma lhs_eq_box (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, ∑ e ∈ Nat.divisors n, T n e =
    ∑ n ∈ Icc 1 Y, ∑ e ∈ Icc 1 Y, ∑ e' ∈ Icc 1 Y,
      (if e ∣ n ∧ e' ∣ n ∧ e ≤ e' then (e' : ℝ)⁻¹ else 0) := by
  apply sum_congr rfl
  intro n hn
  unfold T
  simp only [divisors_eq_filter hn, filter_filter, sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases h : e ∣ n <;> simp [h]

lemma inner_count_le (Y e e' : ℕ) (he : 1 ≤ e) (he' : 1 ≤ e') :
    ∑ n ∈ Icc 1 Y, (if e ∣ n ∧ e' ∣ n ∧ e ≤ e' then (e' : ℝ)⁻¹ else 0) ≤
    if e ≤ e' then (Y : ℝ) * ((Nat.gcd e e' : ℝ) / e) * ((e' : ℝ) ^ 2)⁻¹ else 0 := by
  split_ifs with hle
  · have h1 : ∀ n, (e ∣ n ∧ e' ∣ n ∧ e ≤ e') ↔ Nat.lcm e e' ∣ n := by
      intro n; rw [Nat.lcm_dvd_iff]; tauto
    simp only [h1]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hfilt : (Icc 1 Y).filter (fun n => Nat.lcm e e' ∣ n)
        = (Ioc 0 Y).filter (fun n => Nat.lcm e e' ∣ n) := by
      congr 1
    rw [hfilt, Nat.Ioc_filter_dvd_card_eq_div]
    have hL : 0 < Nat.lcm e e' := Nat.lcm_pos he he'
    have hG : 0 < Nat.gcd e e' := Nat.gcd_pos_of_pos_left _ he
    have hGL : (Nat.gcd e e' : ℝ) * (Nat.lcm e e' : ℝ) = (e : ℝ) * e' := by
      exact_mod_cast Nat.gcd_mul_lcm e e'
    have hLr : (0:ℝ) < Nat.lcm e e' := by exact_mod_cast hL
    have hGr : (0:ℝ) < Nat.gcd e e' := by exact_mod_cast hG
    have her : (0:ℝ) < e := by exact_mod_cast he
    have he'r : (0:ℝ) < e' := by exact_mod_cast he'
    calc ((Y / Nat.lcm e e' : ℕ) : ℝ) * (e' : ℝ)⁻¹ ≤ ((Y : ℝ) / Nat.lcm e e') * (e' : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
      _ = _ := by
          have : (Nat.lcm e e' : ℝ) = e * e' / Nat.gcd e e' := by
            rw [eq_div_iff hGr.ne']; linarith
          rw [this]; field_simp
  · simp [hle]

lemma gcd_le_sum (e e' : ℕ) (he' : 0 < e') :
    (Nat.gcd e e' : ℝ) / e ≤ ∑ g ∈ Nat.divisors e', if g ∣ e then (g : ℝ) / e else 0 := by
  have hmem : Nat.gcd e e' ∈ Nat.divisors e' :=
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, he'.ne'⟩
  calc (Nat.gcd e e' : ℝ) / e
      = (if Nat.gcd e e' ∣ e then ((Nat.gcd e e' : ℕ) : ℝ) / e else 0) := by
        rw [ite_eq_left (Nat.gcd_dvd_left _ _)]
    _ ≤ _ := Finset.single_le_sum (f := fun g => if g ∣ e then (g : ℝ) / e else 0)
        (fun g _ => by split_ifs <;> positivity) hmem

lemma inner_harm (Y e' g : ℕ) (hg : 0 < g) :
    ∑ e ∈ Icc 1 Y, (if e ≤ e' ∧ g ∣ e then (g : ℝ) / e else 0) ≤ (harmonic (e' / g) : ℝ) := by
  rw [← sum_filter, harmonic_eq_sum_Icc]
  push_cast
  have hsub : (Icc 1 Y).filter (fun e => e ≤ e' ∧ g ∣ e) ⊆ (Icc 1 (e' / g)).image (g * ·) := by
    intro x hx
    simp only [mem_filter, mem_Icc] at hx
    obtain ⟨⟨h1, _⟩, hxe, c, rfl⟩ := hx
    simp only [mem_image, mem_Icc]
    refine ⟨c, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp at h1
      · exact hc
    · rw [Nat.le_div_iff_mul_le hg, Nat.mul_comm]; exact hxe
  have hgr : (g : ℝ) ≠ 0 := (Nat.cast_pos.2 hg).ne'
  calc _ ≤ ∑ x ∈ (Icc 1 (e' / g)).image (g * ·), (g : ℝ) / x :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ a ∈ Icc 1 (e' / g), (g : ℝ) / ((g * a : ℕ) : ℝ) := by
        rw [sum_image]; intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hg h
    _ = ∑ a ∈ Icc 1 (e' / g), ((a : ℕ) : ℝ)⁻¹ := by
        apply sum_congr rfl; intro a _; push_cast; exact div_mul_cancel_left₀ hgr _

lemma G_le (Y e' : ℕ) (he' : 0 < e') :
    ∑ e ∈ Icc 1 Y, (if e ≤ e' then (Nat.gcd e e' : ℝ) / e else 0) ≤
    ∑ g ∈ Nat.divisors e', (harmonic (e' / g) : ℝ) := by
  calc _ ≤ ∑ e ∈ Icc 1 Y, ∑ g ∈ Nat.divisors e',
          (if e ≤ e' ∧ g ∣ e then (g : ℝ) / e else 0) := by
        apply sum_le_sum; intro e _
        split_ifs with h
        · simpa only [h, true_and] using gcd_le_sum e e' he'
        · simp [h]
    _ = ∑ g ∈ Nat.divisors e', ∑ e ∈ Icc 1 Y,
          (if e ≤ e' ∧ g ∣ e then (g : ℝ) / e else 0) := sum_comm
    _ ≤ _ := sum_le_sum (fun g hg => inner_harm Y e' g (Nat.pos_of_mem_divisors hg))

lemma step5_pt (Y e' : ℕ) (he' : e' ∈ Icc 1 Y) :
    ((e' : ℝ) ^ 2)⁻¹ * ∑ g ∈ Nat.divisors e', (harmonic (e' / g) : ℝ) ≤
    ∑ g ∈ Icc 1 Y, ∑ b ∈ Icc 1 Y,
      (if g * b = e' then ((g : ℝ) ^ 2)⁻¹ * ((harmonic b : ℝ) / (b : ℝ) ^ 2) else 0) := by
  have hnn : ∀ g b : ℕ, (0:ℝ) ≤
      (if g * b = e' then ((g : ℝ) ^ 2)⁻¹ * ((harmonic b : ℝ) / (b : ℝ) ^ 2) else 0) := by
    intro g b; split_ifs
    · exact mul_nonneg (by positivity) (div_nonneg (harmonic_nonneg' b) (by positivity))
    · exact le_refl _
  rw [mul_sum]
  have hsub : Nat.divisors e' ⊆ Icc 1 Y := by
    intro d hd; rw [divisors_eq_filter he'] at hd; exact (mem_filter.1 hd).1
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub
    (fun g _ _ => sum_nonneg (fun b _ => hnn g b)))
  apply sum_le_sum
  intro g hg
  have hgd : g ∣ e' := Nat.dvd_of_mem_divisors hg
  simp only [mem_Icc] at he'
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  have hb : e' / g ∈ Icc 1 Y := by
    simp only [mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hgd) hg0, (Nat.div_le_self _ _).trans he'.2⟩
  refine le_trans (le_of_eq ?_) (single_le_sum (fun b _ => hnn g b) hb)
  rw [ite_eq_left (Nat.mul_div_cancel' hgd)]
  have hgr : (g : ℝ) ≠ 0 := (Nat.cast_pos.2 hg0).ne'
  have her : (e' : ℝ) ≠ 0 := (Nat.cast_pos.2 (by omega : 0 < e')).ne'
  rw [Nat.cast_div hgd hgr]
  field_simp

lemma step5 (Y : ℕ) :
    ∑ e' ∈ Icc 1 Y, ((e' : ℝ) ^ 2)⁻¹ * ∑ g ∈ Nat.divisors e', (harmonic (e' / g) : ℝ) ≤
    (∑ g ∈ Icc 1 Y, ((g : ℝ) ^ 2)⁻¹) * ∑ b ∈ Icc 1 Y, (harmonic b : ℝ) / (b : ℝ) ^ 2 := by
  calc _ ≤ ∑ e' ∈ Icc 1 Y, ∑ g ∈ Icc 1 Y, ∑ b ∈ Icc 1 Y,
      (if g * b = e' then ((g : ℝ) ^ 2)⁻¹ * ((harmonic b : ℝ) / (b : ℝ) ^ 2) else 0) :=
        sum_le_sum (fun e' he' => step5_pt Y e' he')
    _ = ∑ g ∈ Icc 1 Y, ∑ b ∈ Icc 1 Y, ∑ e' ∈ Icc 1 Y,
      (if g * b = e' then ((g : ℝ) ^ 2)⁻¹ * ((harmonic b : ℝ) / (b : ℝ) ^ 2) else 0) := by
        rw [sum_comm]; apply sum_congr rfl; intro g _; rw [sum_comm]
    _ ≤ ∑ g ∈ Icc 1 Y, ∑ b ∈ Icc 1 Y, ((g : ℝ) ^ 2)⁻¹ * ((harmonic b : ℝ) / (b : ℝ) ^ 2) := by
        apply sum_le_sum; intro g _; apply sum_le_sum; intro b _
        rw [sum_ite_eq]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (by positivity) (div_nonneg (harmonic_nonneg' b) (by positivity))
    _ = _ := by rw [sum_mul_sum]

lemma finite_le_S (Y : ℕ) :
    (∑ g ∈ Icc 1 Y, ((g : ℝ) ^ 2)⁻¹) * ∑ b ∈ Icc 1 Y, (harmonic b : ℝ) / (b : ℝ) ^ 2 ≤ S := by
  have h1 : ∑ g ∈ Icc 1 Y, ((g : ℝ) ^ 2)⁻¹ ≤ ∑' g : ℕ, ((g : ℝ) ^ 2)⁻¹ :=
    (Real.summable_nat_pow_inv.2 (by norm_num)).sum_le_tsum _ (fun _ _ => by positivity)
  have h2 : ∑ b ∈ Icc 1 Y, (harmonic b : ℝ) / (b : ℝ) ^ 2
      ≤ ∑' b : ℕ, (harmonic b : ℝ) / (b : ℝ) ^ 2 :=
    summable_harmonic_div_sq.sum_le_tsum _
      (fun b _ => div_nonneg (harmonic_nonneg' b) (by positivity))
  have h3 : 0 ≤ ∑ b ∈ Icc 1 Y, (harmonic b : ℝ) / (b : ℝ) ^ 2 :=
    sum_nonneg (fun b _ => div_nonneg (harmonic_nonneg' b) (by positivity))
  have h4 : 0 ≤ ∑' g : ℕ, ((g : ℝ) ^ 2)⁻¹ := tsum_nonneg (fun _ => by positivity)
  unfold S
  exact mul_le_mul h1 h2 h3 h4

theorem sum_T_le (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, ∑ e ∈ Nat.divisors n, T n e ≤ S * Y := by
  have hA : ∑ n ∈ Icc 1 Y, ∑ e ∈ Nat.divisors n, T n e ≤
      ∑ e ∈ Icc 1 Y, ∑ e' ∈ Icc 1 Y,
        (if e ≤ e' then (Y : ℝ) * ((Nat.gcd e e' : ℝ) / e) * ((e' : ℝ) ^ 2)⁻¹ else 0) := by
    rw [lhs_eq_box, sum_comm]
    apply sum_le_sum; intro e he
    rw [sum_comm]
    apply sum_le_sum; intro e' he'
    exact inner_count_le Y e e' (mem_Icc.1 he).1 (mem_Icc.1 he').1
  have hB : ∑ e ∈ Icc 1 Y, ∑ e' ∈ Icc 1 Y,
        (if e ≤ e' then (Y : ℝ) * ((Nat.gcd e e' : ℝ) / e) * ((e' : ℝ) ^ 2)⁻¹ else 0)
      = (Y : ℝ) * ∑ e' ∈ Icc 1 Y, ((e' : ℝ) ^ 2)⁻¹ *
          ∑ e ∈ Icc 1 Y, (if e ≤ e' then (Nat.gcd e e' : ℝ) / e else 0) := by
    rw [sum_comm, mul_sum]; apply sum_congr rfl; intro e' _
    rw [mul_sum, mul_sum]; apply sum_congr rfl; intro e _; split_ifs <;> ring
  have hC : ∑ e' ∈ Icc 1 Y, ((e' : ℝ) ^ 2)⁻¹ *
          ∑ e ∈ Icc 1 Y, (if e ≤ e' then (Nat.gcd e e' : ℝ) / e else 0) ≤ S := by
    refine le_trans ?_ ((step5 Y).trans (finite_le_S Y))
    apply sum_le_sum; intro e' he'
    exact mul_le_mul_of_nonneg_left (G_le Y e' (mem_Icc.1 he').1) (by positivity)
  calc _ ≤ _ := hA
    _ = _ := hB
    _ ≤ (Y : ℝ) * S := mul_le_mul_of_nonneg_left hC (by positivity)
    _ = S * Y := mul_comm _ _

/-! ### Step 5: main counting theorem -/

/-- Main counting bound `#covered(K, X) ≤ S X / K²`.
Depends on: Steps 2–4. -/
theorem card_covered_le (K X : ℕ) (hK : 1 ≤ K) :
    ((covered K X).card : ℝ) ≤ S * X / (K : ℝ) ^ 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hS : 0 ≤ S := mul_nonneg (tsum_nonneg (fun _ => by positivity))
    (tsum_nonneg (fun b => div_nonneg (by unfold harmonic; push_cast; positivity) (by positivity)))
  calc ((covered K X).card : ℝ)
      ≤ ∑ n ∈ Icc 1 (X / K), (((Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e)).card : ℝ) :=
        card_covered_le_pairs K X hK
    _ ≤ ∑ n ∈ Icc 1 (X / K), (K : ℝ)⁻¹ * ∑ e ∈ Nat.divisors n, T n e := by
        refine sum_le_sum (fun n _ => ?_)
        rw [inv_mul_eq_div, le_div_iff₀ hK0, mul_comm]
        exact markov_divisors n K
    _ = (K : ℝ)⁻¹ * ∑ n ∈ Icc 1 (X / K), ∑ e ∈ Nat.divisors n, T n e := by rw [mul_sum]
    _ ≤ (K : ℝ)⁻¹ * (S * ((X / K : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_T_le _) (by positivity)
    _ ≤ (K : ℝ)⁻¹ * (S * ((X : ℝ) / K)) := by
        gcongr
        exact Nat.cast_div_le
    _ = S * X / (K : ℝ) ^ 2 := by field_simp

/-- For some `K`, at least half of all `N < X` are not covered: every `n` with `N ∈ D_n`
has `N < K n`.
Depends on: `card_covered_le`. -/
theorem exists_K_half_uncovered :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ X : ℕ, ((covered K X).card : ℝ) ≤ X / 2 := by
  refine ⟨Nat.ceil (2 * S) + 1, by omega, fun X => ?_⟩
  set K := Nat.ceil (2 * S) + 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have h2S : 2 * S ≤ K := by
    have := Nat.le_ceil (2 * S)
    have : ((Nat.ceil (2 * S) : ℕ) : ℝ) + 1 = K := by rw [hKdef]; push_cast; ring
    linarith
  have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have hX : (0 : ℝ) ≤ X := by positivity
  calc ((covered K X).card : ℝ) ≤ S * X / (K : ℝ) ^ 2 := card_covered_le K X (by omega)
    _ ≤ X / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

/-! ### Step 6: answer to Erdős 468 -/

/-- **Erdős 468, almost-all version, is false.**
Depends on: `exists_K_half_uncovered`. -/
theorem not_erdos468AlmostAll : ¬ Erdos468AlmostAll := by
  classical
  obtain ⟨K, hK1, hK⟩ := exists_K_half_uncovered
  rintro ⟨f, hden, ho⟩
  set s := {N | IsMinimalDPreimage N (f N)} with hs
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hev := ho.def (show (0 : ℝ) < (K : ℝ)⁻¹ by positivity)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  have hev2 : ∀ᶠ X in atTop, partialDensity s X ∈ Set.Ioi ((3 : ℝ) / 4) :=
    hden (Ioi_mem_nhds (by norm_num))
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 hev2
  set X := max X0 (4 * N0 + 1) with hXdef
  have h1 : (3 : ℝ) / 4 < partialDensity s X := hX0 X (le_max_left _ _)
  have hXpos : 4 * N0 + 1 ≤ X := le_max_right _ _
  have hsub : (range X).filter (· ∈ s) ⊆ range N0 ∪ covered K X := by
    intro N hN
    simp only [mem_filter, mem_range] at hN
    obtain ⟨hNX, hNs⟩ := hN
    rw [mem_union]
    by_cases hlt : N < N0
    · exact Or.inl (mem_range.2 hlt)
    · right
      have hb := hN0 N (by omega)
      simp only [Real.norm_natCast] at hb
      have hKf : K * f N ≤ N := by
        have : (K : ℝ) * f N ≤ N := by
          have := mul_le_mul_of_nonneg_left hb hK0.le
          rwa [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul] at this
        exact_mod_cast this
      simp only [covered, mem_filter, mem_range]
      exact ⟨hNX, f N, hKf, hNs.1⟩
  have hcard : (((range X).filter (· ∈ s)).card : ℝ) ≤ N0 + X / 2 := by
    have := card_le_card hsub
    have h2 := card_union_le (range N0) (covered K X)
    rw [card_range] at h2
    have h3 : (((range X).filter (· ∈ s)).card : ℝ) ≤ N0 + (covered K X).card := by
      exact_mod_cast this.trans h2
    linarith [hK X]
  have hXr : (4 : ℝ) * N0 + 1 ≤ X := by exact_mod_cast hXpos
  have hX0' : (0 : ℝ) < X := by linarith [show (0 : ℝ) ≤ N0 by positivity]
  have : partialDensity s X ≤ 3 / 4 := by
    unfold partialDensity
    rw [div_le_iff₀ hX0']
    linarith
  linarith

end Erdos468

#print axioms Erdos468.not_erdos468AlmostAll
#print axioms Erdos468.card_covered_le

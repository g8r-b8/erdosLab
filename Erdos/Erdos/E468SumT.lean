import Mathlib
open Finset Filter Real
namespace Erdos468

noncomputable def T (n e : ℕ) : ℝ :=
  ∑ e' ∈ (Nat.divisors n).filter (e ≤ ·), (e' : ℝ)⁻¹

noncomputable def S : ℝ :=
  (∑' g : ℕ, ((g : ℝ) ^ 2)⁻¹) * ∑' b : ℕ, (harmonic b : ℝ) / (b : ℝ) ^ 2

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
      congr 1; ext n; simp only [mem_Icc, mem_Ioc]; omega
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
            field_simp; linarith
          rw [this]; field_simp
  · simp [hle]

lemma gcd_le_sum (e e' : ℕ) (he' : 0 < e') :
    (Nat.gcd e e' : ℝ) / e ≤ ∑ g ∈ Nat.divisors e', if g ∣ e then (g : ℝ) / e else 0 := by
  have hmem : Nat.gcd e e' ∈ Nat.divisors e' :=
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, he'.ne'⟩
  calc (Nat.gcd e e' : ℝ) / e
      = (if Nat.gcd e e' ∣ e then ((Nat.gcd e e' : ℕ) : ℝ) / e else 0) := by
        rw [if_pos (Nat.gcd_dvd_left _ _)]
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
  beta_reduce
  rw [if_pos (Nat.mul_div_cancel' hgd)]
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

end Erdos468

#print axioms Erdos468.sum_T_le

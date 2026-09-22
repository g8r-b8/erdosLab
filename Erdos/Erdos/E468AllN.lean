import Mathlib

/-!
# Erdős Problem 468 — the literal "all `N`" version

Let `R = {N : ∃ n, N ∈ D n}`. We show:

* (`mem_D_two_pow_mul_prime`) for `p` prime with `2 ^ k < p`,
  `p + 2 ^ (k + 1) - 2 ∈ D (2 ^ k * p)`; hence `R ⊇ {p + 2^(k+1) - 2 : 2^k < p}`, a set of
  positive lower density by Romanov's theorem (see `WRITEUP_468.md`);
* (`not_erdos468MinimalPreimageLittleO_of_density`) conditionally on (i) the covering bound
  `#covered K X ≤ C X / K²` (proved as `Erdos468.card_covered_le` in `E468.lean`) and
  (ii) `R` having positive upper density, the literal statement
  `Erdos468MinimalPreimageLittleO` is false.

Both hypotheses are explicit theorem arguments, not axioms.
-/

open Finset Filter Asymptotics

namespace Erdos468AllN

/-- Same as `Erdos468.divisorPrefixSum`. -/
def divisorPrefixSum (n x : ℕ) : ℕ :=
  ∑ d ∈ (Nat.divisors n).filter (fun d => 1 < d ∧ d ≤ x), d

/-- Same as `Erdos468.D`. -/
def D (n : ℕ) : Finset ℕ :=
  ((Nat.divisors n).filter (1 < ·)).image (divisorPrefixSum n)

/-- Same as `Erdos468.IsMinimalDPreimage`. -/
def IsMinimalDPreimage (N n : ℕ) : Prop :=
  N ∈ D n ∧ ∀ m : ℕ, N ∈ D m → n ≤ m

/-- Same as `Erdos468.covered`. -/
noncomputable def covered (K X : ℕ) : Finset ℕ := by
  classical
  exact (range X).filter (fun N => ∃ n, K * n ≤ N ∧ N ∈ D n)

/-- The literal "all `N`" version of Erdős 468 (formal-conjectures PR #4076 style). -/
def Erdos468MinimalPreimageLittleO : Prop :=
  ∃ f : ℕ → ℕ, (∀ N, (∃ n, N ∈ D n) → IsMinimalDPreimage N (f N)) ∧
    (fun N : ℕ => (f N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

/-- The set `R` of `N` lying in some `D n`, counted below `X`. -/
noncomputable def reachable (X : ℕ) : Finset ℕ := by
  classical
  exact (range X).filter (fun N => ∃ n, N ∈ D n)

/-! ### Part (a): membership lemma -/

lemma sum_two_pow_Ioc (k : ℕ) : ∑ i ∈ Ioc 0 k, 2 ^ i + 2 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), pow_succ 2 (k + 1)]
    omega

/-- The divisors `d` of `2^k p` with `1 < d ≤ p` are exactly `2, 4, …, 2^k` and `p`. -/
lemma filter_divisors_eq (k p : ℕ) (hp : p.Prime) (hkp : 2 ^ k < p) :
    (Nat.divisors (2 ^ k * p)).filter (fun d => 1 < d ∧ d ≤ p) =
      insert p ((Ioc 0 k).image (2 ^ ·)) := by
  have hn : 2 ^ k * p ≠ 0 := Nat.mul_ne_zero (by positivity) hp.ne_zero
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_insert, mem_image, mem_Ioc]
  constructor
  · rintro ⟨⟨hd, -⟩, h1, hdp⟩
    by_cases hpd : p ∣ d
    · left
      exact le_antisymm hdp (Nat.le_of_dvd (by omega) hpd)
    · right
      have hcop : Nat.Coprime d p :=
        (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd))
      have h2 : d ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right hd
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
      refine ⟨i, ⟨?_, hi⟩, rfl⟩
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp at h1
      · exact h
  · rintro (rfl | ⟨i, ⟨hi0, hik⟩, rfl⟩)
    · exact ⟨⟨dvd_mul_left _ _, hn⟩, hp.one_lt, le_rfl⟩
    · refine ⟨⟨(pow_dvd_pow 2 hik).mul_right p, hn⟩, ?_, ?_⟩
      · exact Nat.one_lt_two_pow (by omega)
      · exact ((Nat.pow_le_pow_right (by norm_num) hik).trans hkp.le)

/-- **Membership lemma.** For `p` prime with `2 ^ k < p`,
`p + 2^(k+1) - 2 ∈ D (2^k p)`: the divisors of `2^k p` up to `p` are `2, 4, …, 2^k, p`. -/
theorem mem_D_two_pow_mul_prime (k p : ℕ) (hp : p.Prime) (hkp : 2 ^ k < p) :
    p + 2 ^ (k + 1) - 2 ∈ D (2 ^ k * p) := by
  have hn : 2 ^ k * p ≠ 0 := Nat.mul_ne_zero (by positivity) hp.ne_zero
  unfold D
  rw [mem_image]
  refine ⟨p, mem_filter.2 ⟨Nat.mem_divisors.2 ⟨dvd_mul_left _ _, hn⟩, hp.one_lt⟩, ?_⟩
  unfold divisorPrefixSum
  rw [filter_divisors_eq k p hp hkp]
  have hnot : p ∉ (Ioc 0 k).image (2 ^ ·) := by
    simp only [mem_image, mem_Ioc, not_exists, not_and]
    intro i hi heq
    have := (Nat.pow_le_pow_right (by norm_num : 0 < 2) hi.2)
    omega
  rw [sum_insert hnot, sum_image (fun i _ j _ h => Nat.pow_right_injective le_rfl h)]
  have := sum_two_pow_Ioc k
  omega

/-! ### Part (b): conditional disproof of the literal version -/

/-- **Conditional disproof of the literal "all `N`" version.**
Hypotheses: (i) the covering bound `#covered K X ≤ C X / K²` for all `K ≥ 1` (this is
`Erdos468.card_covered_le` with `C = S`, modulo the identification of the copied definitions);
(ii) `R = {N : ∃ n, N ∈ D n}` has positive upper density. -/
theorem not_erdos468MinimalPreimageLittleO_of_density (C : ℝ)
    (hcov : ∀ K X : ℕ, 1 ≤ K → ((covered K X).card : ℝ) ≤ C * X / (K : ℝ) ^ 2)
    (hdens : ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ X : ℕ in atTop, δ * X ≤ ((reachable X).card : ℝ)) :
    ¬ Erdos468MinimalPreimageLittleO := by
  classical
  obtain ⟨δ, hδ, hfreq⟩ := hdens
  rintro ⟨f, hf, ho⟩
  -- choose `K` with `C / K ≤ δ / 4`
  set K : ℕ := Nat.ceil (4 * |C| / δ) + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKbig : 4 * |C| / δ ≤ K := by
    have := Nat.le_ceil (4 * |C| / δ)
    have : ((Nat.ceil (4 * |C| / δ) : ℕ) : ℝ) + 1 = K := by rw [hKdef]; push_cast; ring
    linarith
  have hCK : C / (K : ℝ) ^ 2 ≤ δ / 4 := by
    have h1 : C ≤ |C| := le_abs_self C
    have h2 : 4 * |C| ≤ δ * K := by rw [div_le_iff₀ hδ] at hKbig; linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  -- eventually `K f N ≤ N`
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (ho.def (show (0 : ℝ) < (K : ℝ)⁻¹ by positivity))
  have hsub : ∀ X, reachable X ⊆ range N0 ∪ covered K X := by
    intro X N hN
    simp only [reachable, mem_filter, mem_range] at hN
    obtain ⟨hNX, hNR⟩ := hN
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
      exact ⟨hNX, f N, hKf, (hf N hNR).1⟩
  have hbound : ∀ X : ℕ, ((reachable X).card : ℝ) ≤ N0 + δ / 4 * X := by
    intro X
    have h1 := card_le_card (hsub X)
    have h2 := card_union_le (range N0) (covered K X)
    rw [card_range] at h2
    have h3 : ((reachable X).card : ℝ) ≤ N0 + (covered K X).card := by
      exact_mod_cast h1.trans h2
    have h4 : C * X / (K : ℝ) ^ 2 ≤ δ / 4 * X := by
      rw [mul_comm C, mul_div_assoc, mul_comm (X : ℝ)]
      exact mul_le_mul_of_nonneg_right hCK (by positivity)
    linarith [hcov K X hK1]
  -- but frequently `δ X ≤ #R ∩ [0, X)`, with `X` arbitrarily large
  obtain ⟨X, hδX, hX⟩ := (hfreq.and_eventually (eventually_gt_atTop
    (Nat.ceil (4 * (N0 : ℝ) / δ)))).exists
  have hXr : 4 * (N0 : ℝ) / δ < X := by
    have := Nat.le_ceil (4 * (N0 : ℝ) / δ)
    have : ((Nat.ceil (4 * (N0 : ℝ) / δ) : ℕ) : ℝ) < X := by exact_mod_cast hX
    linarith
  rw [div_lt_iff₀ hδ] at hXr
  linarith [hbound X]

end Erdos468AllN

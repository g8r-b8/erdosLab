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

/-- TODO: Prefix-sum bound.
What's missing: reindex `d' ↦ n / d'` on divisors.
Acceptance: for `e ∣ n`, `0 < n`, `divisorPrefixSum n (n / e) ≤ n * T n e`.
Depends on: nothing. -/
theorem prefixSum_le (n e : ℕ) (hn : 0 < n) (he : e ∣ n) :
    (divisorPrefixSum n (n / e) : ℝ) ≤ n * T n e := by
  sorry

/-! ### Step 2: covered values come from pairs `(n, e)` with `T n e ≥ K` -/

/-- TODO: Covered count ≤ number of pairs.
What's missing: surjection from pairs `(n, e)`, `n < X/K + 1`, `e ∣ n`, `K ≤ T n e` onto covered.
Acceptance: as stated.
Depends on: `prefixSum_le`. -/
theorem card_covered_le_pairs (K X : ℕ) (hK : 1 ≤ K) :
    ((covered K X).card : ℝ) ≤
      ∑ n ∈ Icc 1 (X / K), (((Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e)).card : ℝ) := by
  sorry

/-! ### Step 3: Markov -/

/-- TODO: Markov inequality on divisors.
Acceptance: `K * #{e ∣ n : K ≤ T n e} ≤ ∑_{e ∣ n} T n e`.
Depends on: `T` nonneg. -/
theorem markov_divisors (n K : ℕ) :
    (K : ℝ) * ((Nat.divisors n).filter (fun e => (K : ℝ) ≤ T n e)).card ≤
      ∑ e ∈ Nat.divisors n, T n e := by
  sorry

/-! ### Step 4: the average of `∑_{e ∣ n} T n e` is bounded -/

/-- TODO: Summability of `H_b / b²`.
Acceptance: `Summable (fun b => (harmonic b : ℝ) / b ^ 2)`.
Depends on: `harmonic_le_one_add_log`, p-series. -/
theorem summable_harmonic_div_sq :
    Summable (fun b : ℕ => (harmonic b : ℝ) / (b : ℝ) ^ 2) := by
  sorry

/-- TODO: The key average bound.
Acceptance: `∑_{n ∈ [1,Y]} ∑_{e ∣ n} T n e ≤ S * Y`.
Depends on: `summable_harmonic_div_sq`, lcm counting, gcd ≤ ∑ common divisors. -/
theorem sum_T_le (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, ∑ e ∈ Nat.divisors n, T n e ≤ S * Y := by
  sorry

/-! ### Step 5: main counting theorem -/

/-- TODO: Main counting bound `#covered(K, X) ≤ S X / K²`.
Depends on: Steps 2–4. -/
theorem card_covered_le (K X : ℕ) (hK : 1 ≤ K) :
    ((covered K X).card : ℝ) ≤ S * X / (K : ℝ) ^ 2 := by
  sorry

/-- TODO: For some `K`, at least half of all `N < X` are not covered: every `n` with `N ∈ D_n`
has `N < K n`.
Depends on: `card_covered_le`. -/
theorem exists_K_half_uncovered :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ X : ℕ, ((covered K X).card : ℝ) ≤ X / 2 := by
  sorry

/-! ### Step 6: answer to Erdős 468 -/

/-- TODO: **Erdős 468, almost-all version, is false.**
Depends on: `exists_K_half_uncovered`. -/
theorem not_erdos468AlmostAll : ¬ Erdos468AlmostAll := by
  sorry

end Erdos468

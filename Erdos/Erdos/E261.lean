import Mathlib

/-!
# Erdős Problem 261: a rational with two infinite representations

The formal-conjectures statement `erdos_261.variants.two_representations` asks for a rational `x`
with at least two representations `x = ∑ a_k / 2^{a_k}` by strictly increasing positive integers.
Following Z. Rafik (erdosproblems.com forum, 27 Apr 2026): since `4/2^4 = 5/2^5 + 6/2^6` and
`∑_{m ≥ 1} m/2^m = 2`, both `ℕ₊ \ {4}` and `ℕ₊ \ {5, 6}` represent `7/4`.
-/

open scoped Cardinal

namespace Erdos261

/-- Same definition as in formal-conjectures `ErdosProblems/261.lean`. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

/-- `ℕ₊ \ {4}` enumerated increasingly: `1, 2, 3, 5, 6, 7, …`. -/
def seqA (k : ℕ) : ℕ := if k < 3 then k + 1 else k + 2

/-- `ℕ₊ \ {5, 6}` enumerated increasingly: `1, 2, 3, 4, 7, 8, …`. -/
def seqB (k : ℕ) : ℕ := if k < 4 then k + 1 else k + 3

/-- Tail sums: `∑_{n} (n + c) / 2^{n + c} = (2c + 2) / 2^c` in `ℝ`. -/
lemma hasSum_tail (c : ℕ) :
    HasSum (fun n : ℕ => ((n + c : ℕ) : ℝ) / 2 ^ (n + c)) ((2 * c + 2) / 2 ^ c) := by
  sorry

/-- Transfer a real `HasSum` of rational terms back to `ℚ`. -/
lemma hasSum_rat_of_real {f : ℕ → ℚ} {q : ℚ} (h : HasSum (fun n => (f n : ℝ)) (q : ℝ)) :
    HasSum f q := by
  sorry

lemma hasSum_seqA : HasSum (fun k => (seqA k : ℚ) / (2 ^ (seqA k) : ℚ)) (7 / 4) := by
  sorry

lemma hasSum_seqB : HasSum (fun k => (seqB k : ℚ) / (2 ^ (seqB k) : ℚ)) (7 / 4) := by
  sorry

lemma rep_seqA : Erdos261InfiniteRepresentation (7 / 4) seqA := by
  sorry

lemma rep_seqB : Erdos261InfiniteRepresentation (7 / 4) seqB := by
  sorry

/-- The formal-conjectures variant, with `answer(True)` unfolded. -/
theorem two_representations :
    ∃ x : ℚ, 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  sorry

end Erdos261

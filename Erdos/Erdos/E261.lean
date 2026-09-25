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
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) 2 := by
    have := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    convert this using 1; norm_num
  have h3 := (h1.add (hasSum_geometric_two.mul_left (c : ℝ))).mul_left ((1 / 2 : ℝ) ^ c)
  convert h3 using 1
  · funext n
    push_cast
    rw [pow_add]
    simp only [one_div, inv_pow]
    field_simp
  · simp only [one_div, inv_pow]
    field_simp
    ring

/-- Transfer a real `HasSum` of rational terms back to `ℚ`. -/
lemma hasSum_rat_of_real {f : ℕ → ℚ} {q : ℚ} (h : HasSum (fun n => (f n : ℝ)) (q : ℝ)) :
    HasSum f q := by
  have hi : Topology.IsInducing (Rat.castHom ℝ) := Rat.isUniformEmbedding_coe_real.isUniformInducing.isInducing
  exact (hi.hasSum_iff f q).1 h

lemma hasSum_seqA : HasSum (fun k => (seqA k : ℚ) / (2 ^ (seqA k) : ℚ)) (7 / 4) := by
  apply hasSum_rat_of_real
  have e : ∀ n, seqA (n + 3) = n + 5 := fun n => by simp [seqA]
  have key : HasSum (fun n => ((seqA (n + 3) : ℕ) : ℝ) / 2 ^ (seqA (n + 3)))
      (7 / 4 - ∑ i ∈ Finset.range 3, ((seqA i : ℕ) : ℝ) / 2 ^ (seqA i)) := by
    simp only [e]
    convert hasSum_tail 5 using 1
    simp [Finset.sum_range_succ, seqA]
    norm_num
  push_cast
  exact (hasSum_nat_add_iff' 3).1 key

lemma hasSum_seqB : HasSum (fun k => (seqB k : ℚ) / (2 ^ (seqB k) : ℚ)) (7 / 4) := by
  apply hasSum_rat_of_real
  have e : ∀ n, seqB (n + 4) = n + 7 := fun n => by simp [seqB]
  have key : HasSum (fun n => ((seqB (n + 4) : ℕ) : ℝ) / 2 ^ (seqB (n + 4)))
      (7 / 4 - ∑ i ∈ Finset.range 4, ((seqB i : ℕ) : ℝ) / 2 ^ (seqB i)) := by
    simp only [e]
    convert hasSum_tail 7 using 1
    simp [Finset.sum_range_succ, seqB]
    norm_num
  push_cast
  exact (hasSum_nat_add_iff' 4).1 key

lemma rep_seqA : Erdos261InfiniteRepresentation (7 / 4) seqA := by
  refine ⟨strictMono_nat_of_lt_succ fun n => ?_, fun k => ?_, hasSum_seqA.summable,
    hasSum_seqA.tsum_eq.symm⟩
  · simp only [seqA]; split_ifs <;> omega
  · simp only [Pi.one_apply, seqA]; split_ifs <;> omega

lemma rep_seqB : Erdos261InfiniteRepresentation (7 / 4) seqB := by
  refine ⟨strictMono_nat_of_lt_succ fun n => ?_, fun k => ?_, hasSum_seqB.summable,
    hasSum_seqB.tsum_eq.symm⟩
  · simp only [seqB]; split_ifs <;> omega
  · simp only [Pi.one_apply, seqB]; split_ifs <;> omega

/-- The formal-conjectures variant, with `answer(True)` unfolded. -/
theorem two_representations :
    ∃ x : ℚ, 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  refine ⟨7 / 4, Cardinal.two_le_iff.2 ⟨⟨seqA, rep_seqA⟩, ⟨seqB, rep_seqB⟩, fun h => ?_⟩⟩
  have := congrFun (congrArg Subtype.val h) 3
  simp [seqA, seqB] at this

end Erdos261


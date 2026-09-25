import Erdos.E132Main15

/-!
# Erdős Problem 132, `τ > 1`: `min{μ(Δ₂), μ(δ)} ≤ 9n/7 + O(n^{2/3})` — definitions

`problems/132/angle_R6.md` §5.2–5.3 (Theorem E′ and its corollary); paper v3 §12.
Plan, Mathlib gap analysis and DAG: `problems/132/lean/MAIN97_PLAN.md`.

Everything of the `54/37` and `15/11` developments is reused unchanged.  This file adds

* the deficiency `defc Z = 3|Z| − e(G[Z])` of the unit-distance graph (`δ = 1`);
* `Yset X = X ∖ D` (⊆ `K`), `Aset X = S ∖ D` (= `Y ∩ ∂K`);
* the depth shells `Yout ρ` (`depth < ρ`), `Yshell ρ` (`ρ ≤ depth < ρ + 1`), `Yin ρ`
  (`depth ≥ ρ + 1`), where `depth y = min_w (Δ₂ − |y − w|)` is encoded without an infimum:
  `depth y < ρ ⇔ ∃ w ∈ X, |y − w| > Δ₂ − ρ`;
* the error polynomial `Eh`, the constants `CE`, `C97`;
* `CoreE`: the perimeter-free topological heart of Theorem E′ (Steps 2–7 of §5.2).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Definitions -/

/-- Deficiency of the unit-distance graph on `Z`: `Def(Z) = 3|Z| − e(G[Z])`. -/
def defc (Z : Finset Pt) : ℝ := 3 * Z.card - mult Z 1

/-- `Y = X ∖ D`: the non-diametral points (they lie in `K`). -/
def Yset (X : Finset Pt) : Finset Pt := X \ Dset X

/-- `A = S ∖ D` (= `Y ∩ ∂K`, Lemma 3.1(b)). -/
def Aset (X : Finset Pt) : Finset Pt := Sset X \ Dset X

/-- Outer part: `depth < ρ`. -/
def Yout (X : Finset Pt) (ρ : ℝ) : Finset Pt :=
  (Yset X).filter (fun y => ∃ w ∈ X, dist2 X - ρ < dist y w)

/-- Inner part: `depth ≥ ρ + 1`. -/
def Yin (X : Finset Pt) (ρ : ℝ) : Finset Pt :=
  (Yset X).filter (fun y => ∀ w ∈ X, dist y w ≤ dist2 X - (ρ + 1))

/-- The shell `ρ ≤ depth < ρ + 1`. -/
def Yshell (X : Finset Pt) (ρ : ℝ) : Finset Pt :=
  (Yset X).filter (fun y => (∀ w ∈ X, dist y w ≤ dist2 X - ρ) ∧ ∃ w ∈ X, dist2 X - (ρ + 1) < dist y w)

/-- The error `E(h) = 1764h² + 223h + 4` of §5.2 Step 7. -/
def Eh (h : ℝ) : ℝ := 1764 * h ^ 2 + 223 * h + 4

/-- The constant of Theorem E′ (paper: `3·10⁴`; generous here). -/
def CE : ℝ := 10 ^ 5

/-- The constant of the main theorem. -/
def C97 : ℝ := 10 ^ 11

/-- **The topological heart of Theorem E′** (angle_R6 §5.2, Steps 2–7), perimeter-free.

For `δ = 1`, `Δ ≤ 1.94Δ₂`, an integer shell parameter `ρ ≥ 1` with `h = ρ + ½ < Δ₂/200`,
and `|A| > 1000h`: `Def(G[Yout ρ]) ≥ 2|A| − E(h)`.

Why this is what §5.2 proves: `|A| > 1000h` gives `per K ≥ |A| − 1 > 100h` (P7) and, by
Lemma F, `r_in(K) ≥ diam K/300 ≥ per K/(300π) > h`; so the fallbacks (F2), (F3) do not apply
and Steps 2–7 give `Def(H_out) ≥ 2|A| − E(h)`.  See MAIN97_PLAN.md (routes A/B/C). -/
def CoreE : Prop :=
  ∀ (X : Finset Pt) (ρ : ℕ), Normal X → 1 ≤ ρ → ((ρ : ℝ) + 1 / 2) < dist2 X / 200 →
    1000 * ((ρ : ℝ) + 1 / 2) < (Aset X).card →
    2 * ((Aset X).card : ℝ) - Eh ((ρ : ℝ) + 1 / 2) ≤ defc (Yout X ρ)

/-! ## Basic lemmas -/

/-- A subset of a normalised set spans at most `3|Z|` unit distances; hence `Def ≥ 0`.

TODO: prove.
What's missing: `mult Z 1 ≤ 3|Z|`: if `minDist Z = 1` use `mult_minDist_le Z`; otherwise
`minDist Z > 1` (all distances of `Z ⊆ X` are `≥ 1`) or `Z` has `< 2` points, and then no pair of
`Z` is at distance `1`, so `mult Z 1 = 0`.  Simpler alternative: degree `≤ 6`
(`card_partners_minDist_le` for `X`, restricted to `Z`) and `two_mul_card_le_of_deg_le`.
Acceptance: no `sorry`.
Depends on: `mult_minDist_le`, `card_partners_minDist_le`, `Defs.mult_mono`. Difficulty S–M. -/
theorem defc_nonneg (h1 : minDist X = 1) {Z : Finset Pt} (hZ : Z ⊆ X) : 0 ≤ defc Z := by
  sorry

/-- `A ⊆ Yout ρ` for `ρ > 0` (points of `S ∖ D` have depth `0`).

TODO: prove.
What's missing: `a ∈ S` gives a `Δ₂`-partner `w` (`dist a w = dist2 X > dist2 X − ρ`).
Acceptance: no `sorry`.
Depends on: definitions, `mem_partners`. Difficulty S. -/
theorem Aset_subset_Yout {ρ : ℝ} (hρ : 0 < ρ) : Aset X ⊆ Yout X ρ := by
  sorry

/-- Depth is 1-Lipschitz: a point of `Yout ρ` and a point of `Yin ρ` are more than `1` apart.

TODO: prove.
What's missing: `dist y w > Δ₂ − ρ` and `dist y' w ≤ Δ₂ − ρ − 1` give
`dist y y' ≥ dist y w − dist y' w > 1` (triangle inequality).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem one_lt_dist_out_in {ρ : ℝ} {y y' : Pt} (hy : y ∈ Yout X ρ) (hy' : y' ∈ Yin X ρ) :
    1 < dist y y' := by
  sorry

/-- The three parts partition `Y`: `|Y| = |Yout| + |Yshell| + |Yin|`, and they are pairwise
disjoint subsets of `Y`.

TODO: prove.
What's missing: pure logic on the three filter predicates (`Yshell` is exactly "not out and not
in"); `card_filter` / `filter_card_add_filter_neg_card_eq_card`.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_Yset_split (ρ : ℝ) :
    (Yset X).card = (Yout X ρ).card + (Yshell X ρ).card + (Yin X ρ).card ∧
      Disjoint (Yout X ρ) (Yshell X ρ) ∧ Disjoint (Yout X ρ) (Yin X ρ) ∧
      Disjoint (Yshell X ρ) (Yin X ρ) := by
  sorry

/-- Shells of distinct integer parameters are disjoint.

TODO: prove.
What's missing: `y ∈ Yshell ρ ∩ Yshell ρ'` with integers `ρ < ρ'` gives `∃ w, dist y w >
Δ₂ − ρ − 1 ≥ Δ₂ − ρ'` and `∀ w, dist y w ≤ Δ₂ − ρ'`: contradiction.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem disjoint_Yshell {ρ ρ' : ℕ} (h : ρ ≠ ρ') :
    Disjoint (Yshell X ρ) (Yshell X ρ') := by
  sorry

end

end Erdos132Main

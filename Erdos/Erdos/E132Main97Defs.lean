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

/-- Handshake with a degree bound: `2 e(G[Z]) ≤ k|Z|` if every vertex has `≤ k` unit neighbours
in `Z`. -/
theorem two_mul_mult_one_le {Z : Finset Pt} {k : ℕ} (hdeg : ∀ v ∈ Z, (Erdos132Layer.nbr Z 1 v).card ≤ k) :
    2 * mult Z 1 ≤ k * Z.card := by
  have h2 := Erdos132Layer.two_mul_multS (by norm_num : (0 : ℝ) < 1) Z
  have hle : Erdos132Layer.esum Z 1 ≤ k * Z.card := by
    unfold Erdos132Layer.esum
    calc ∑ v ∈ Z, (Erdos132Layer.nbr Z 1 v).card ≤ ∑ _v ∈ Z, k := sum_le_sum hdeg
      _ = k * Z.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have e : mult Z 1 = multS Z 1 := rfl
  omega

/-- Unit neighbours inside `Z ⊆ X` are `δ`-partners in `X` (`δ = 1`). -/
theorem nbr_subset_partners (h1 : minDist X = 1) {Z : Finset Pt} (hZ : Z ⊆ X) (v : Pt) :
    Erdos132Layer.nbr Z 1 v ⊆ partners X (minDist X) v := by
  intro x hx
  obtain ⟨hxZ, hd⟩ := Erdos132Layer.mem_nbr.1 hx
  refine Defs.mem_partners.2 ⟨hZ hxZ, fun h => ?_, by rw [h1]; exact hd⟩
  rw [h, dist_self] at hd; norm_num at hd

/-- Unit degree inside `Z ⊆ X` is `≤ 6`. -/
theorem card_nbr_le_six (h1 : minDist X = 1) {Z : Finset Pt} (hZ : Z ⊆ X) (v : Pt) :
    (Erdos132Layer.nbr Z 1 v).card ≤ 6 :=
  (card_le_card (nbr_subset_partners h1 hZ v)).trans (card_partners_minDist_le X v)

/-- A subset of a normalised set spans at most `3|Z|` unit distances; hence `Def ≥ 0`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `two_mul_mult_one_le`, `card_nbr_le_six`. Difficulty S–M. -/
theorem defc_nonneg (h1 : minDist X = 1) {Z : Finset Pt} (hZ : Z ⊆ X) : 0 ≤ defc Z := by
  have h := two_mul_mult_one_le (k := 6) fun v _ => card_nbr_le_six h1 hZ v
  have : (mult Z 1 : ℝ) ≤ 3 * Z.card := by
    have : mult Z 1 ≤ 3 * Z.card := by omega
    exact_mod_cast this
  unfold defc; linarith

/-- `A ⊆ Yout ρ` for `ρ > 0` (points of `S ∖ D` have depth `0`).

TODO: none — proved.
What's missing: `a ∈ S` gives a `Δ₂`-partner `w` (`dist a w = dist2 X > dist2 X − ρ`).
Acceptance: no `sorry`.
Depends on: definitions, `mem_partners`. Difficulty S. -/
theorem Aset_subset_Yout {ρ : ℝ} (hρ : 0 < ρ) : Aset X ⊆ Yout X ρ := by
  intro a ha
  obtain ⟨haS, haD⟩ := mem_sdiff.1 ha
  obtain ⟨haX, w, hw⟩ := mem_filter.1 haS
  obtain ⟨hwX, -, hd⟩ := Defs.mem_partners.1 hw
  exact mem_filter.2 ⟨mem_sdiff.2 ⟨haX, haD⟩, w, hwX, by rw [hd]; linarith⟩

/-- Depth is 1-Lipschitz: a point of `Yout ρ` and a point of `Yin ρ` are more than `1` apart.

TODO: none — proved.
What's missing: `dist y w > Δ₂ − ρ` and `dist y' w ≤ Δ₂ − ρ − 1` give
`dist y y' ≥ dist y w − dist y' w > 1` (triangle inequality).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem one_lt_dist_out_in {ρ : ℝ} {y y' : Pt} (hy : y ∈ Yout X ρ) (hy' : y' ∈ Yin X ρ) :
    1 < dist y y' := by
  obtain ⟨w, hw, hyw⟩ := (mem_filter.1 hy).2
  have hy'w := (mem_filter.1 hy').2 w hw
  have := dist_triangle y y' w
  linarith

/-- The three parts partition `Y`: `|Y| = |Yout| + |Yshell| + |Yin|`, and they are pairwise
disjoint subsets of `Y`.

TODO: none — proved.
What's missing: pure logic on the three filter predicates (`Yshell` is exactly "not out and not
in"); `card_filter` / `filter_card_add_filter_neg_card_eq_card`.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_Yset_split (ρ : ℝ) :
    (Yset X).card = (Yout X ρ).card + (Yshell X ρ).card + (Yin X ρ).card ∧
      Disjoint (Yout X ρ) (Yshell X ρ) ∧ Disjoint (Yout X ρ) (Yin X ρ) ∧
      Disjoint (Yshell X ρ) (Yin X ρ) := by
  have hdo : Disjoint (Yout X ρ) (Yin X ρ) := by
    rw [disjoint_left]
    intro y hy hy'
    obtain ⟨w, hw, hyw⟩ := (mem_filter.1 hy).2
    have := (mem_filter.1 hy').2 w hw
    linarith
  have hds : Disjoint (Yout X ρ) (Yshell X ρ) := by
    rw [disjoint_left]
    intro y hy hy'
    obtain ⟨w, hw, hyw⟩ := (mem_filter.1 hy).2
    have := (mem_filter.1 hy').2.1 w hw
    linarith
  have hsi : Disjoint (Yshell X ρ) (Yin X ρ) := by
    rw [disjoint_left]
    intro y hy hy'
    obtain ⟨w, hw, hyw⟩ := (mem_filter.1 hy).2.2
    have := (mem_filter.1 hy').2 w hw
    linarith
  refine ⟨?_, hds, hdo, hsi⟩
  have hU : Yset X = Yout X ρ ∪ Yshell X ρ ∪ Yin X ρ := by
    ext y
    simp only [Yout, Yshell, Yin, mem_union, mem_filter]
    constructor
    · intro hy
      by_cases h₁ : ∃ w ∈ X, dist2 X - ρ < dist y w
      · exact Or.inl (Or.inl ⟨hy, h₁⟩)
      push Not at h₁
      by_cases h₂ : ∃ w ∈ X, dist2 X - (ρ + 1) < dist y w
      · exact Or.inl (Or.inr ⟨hy, h₁, h₂⟩)
      push Not at h₂
      exact Or.inr ⟨hy, h₂⟩
    · rintro ((⟨hy, -⟩ | ⟨hy, -⟩) | ⟨hy, -⟩) <;> exact hy
  rw [hU, card_union_of_disjoint (disjoint_union_left.2 ⟨hdo, hsi⟩),
    card_union_of_disjoint hds]

/-- Shells of distinct integer parameters are disjoint.

TODO: none — proved.
What's missing: `y ∈ Yshell ρ ∩ Yshell ρ'` with integers `ρ < ρ'` gives `∃ w, dist y w >
Δ₂ − ρ − 1 ≥ Δ₂ − ρ'` and `∀ w, dist y w ≤ Δ₂ − ρ'`: contradiction.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem disjoint_Yshell {ρ ρ' : ℕ} (h : ρ ≠ ρ') :
    Disjoint (Yshell X ρ) (Yshell X ρ') := by
  have key : ∀ {a b : ℕ}, a < b → Disjoint (Yshell X a) (Yshell X b) := by
    intro a b hab
    rw [disjoint_left]
    intro y hy hy'
    obtain ⟨w, hw, hyw⟩ := (mem_filter.1 hy).2.2
    have h1 := (mem_filter.1 hy').2.1 w hw
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    linarith
  rcases lt_or_gt_of_ne h with h | h
  · exact key h
  · exact (key h).symm

end

end Erdos132Main

import Erdos.E132Main97DPart
import Erdos.E132Main97Eprime
import Erdos.E132Main97Core

/-!
# Erdős Problem 132 — `τ > 1`: `min{μ(Δ₂), μ(δ)} ≤ 9n/7 + O(n^{2/3})` (assembly)

`problems/132/angle_R6.md` §5.3 (corollary of Theorem E′); paper v3 §12.  This matches the
global lower bound `9/7` (the `9/7` constructions have `τ < 1`); it does not claim attainment.

* `τ > 1 ⇔ t > 1` for `δ = 1` (`one_lt_tau_of`, `one_lt_tgap_of`); scale-invariantly the
  hypothesis is `δ < Δ − Δ₂`.
* `e(X) = e(D) + e(X ∖ D)` (`mult_split`); `Def(G[D]) ≥ 2|S ∩ D| − cBad` (`dpart`);
  `Def(G[X ∖ D]) ≥ 2|S ∖ D| − CE n^{2/3}` (`eprime`, from `CoreE`).
* (VS) `μ(Δ₂) ≤ 3s/2`; LP `min(3s/2, 3n − 2s + E) ≤ 9n/7 + 3E/7` (`lp97`).

`erdos132_main97_of_core` is proved from the statement `CoreE`; `erdos132_main97` applies it
to `core` (the one topological statement, `E132Main97Core.lean`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open Erdos132Layer (dist_mem_distSetS pos_of_mem_distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- `t > 1 ⇒ τ > 1` (for `Δ₂ > 0`): `τ − t = (t² − 1)/(2Δ₂)`.

TODO: none — proved.
What's missing: unfold `tau`; `(1 − t²)/(2Δ₂) < 0`.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem one_lt_tau_of (hd : 0 < dist2 X) (ht : 1 < tgap X) : 1 < tau X := by
  unfold tau
  have : (1 - tgap X ^ 2) / (2 * dist2 X) < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by linarith)
  linarith

/-- `τ > 1 ⇒ t > 1` (for `Δ₂ ≥ 0`, `t ≥ 0`).

TODO: none — proved.
What's missing: if `0 ≤ t ≤ 1` then `(1 − t²)/(2Δ₂) ≥ 0` (also for `Δ₂ = 0`, where Lean's
division gives `0`), so `τ ≤ t ≤ 1`.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem one_lt_tgap_of (hd : 0 ≤ dist2 X) (ht0 : 0 ≤ tgap X) (hτ : 1 < tau X) : 1 < tgap X := by
  by_contra hle
  rw [not_lt] at hle
  unfold tau at hτ
  have : 0 ≤ (1 - tgap X ^ 2) / (2 * dist2 X) := div_nonneg (by nlinarith) (by linarith)
  linarith

/-- `Δ₂ ≤ Δ`.

TODO: none — proved.
What's missing: unfold `dist2`; the max of `distSetS X` with `diam X` erased is `≤ diam X`
(`le_diam`); the empty case gives `dist2 X = 0 ≤ diam X` (`diam_nonneg`).
Acceptance: no `sorry`.
Depends on: `Defs.le_diam`, `Defs.diam_nonneg`. Difficulty S. -/
theorem tgap_nonneg (X : Finset Pt) : 0 ≤ tgap X := by
  unfold tgap dist2
  split_ifs with h
  · have := Defs.le_diam (mem_of_mem_erase (max'_mem _ h)); linarith
  · have := Defs.diam_nonneg X; linarith

/-- Normalisation keeping the scale-invariant hypothesis `δ < t`.

TODO: none — proved.
What's missing: as `exists_normalize` with `c = δ⁻¹`, plus `diam_smul`, `dist2_smul`
(`tgap (cX) = c·tgap X > c·δ = 1`).
Acceptance: no `sorry`.
Depends on: `minDist_smul`, `dist2_smul`, `diam_smul`, `mult_smul`. Difficulty S–M. -/
theorem exists_normalize97 (hX : 2 ≤ X.card) (ht : minDist X < tgap X) :
    ∃ Y : Finset Pt, Y.card = X.card ∧ minDist Y = 1 ∧ 1 < tgap Y ∧
      mult Y (dist2 Y) = mult X (dist2 X) ∧ mult Y (minDist Y) = mult X (minDist X) := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < X.card)
  have hne : (distSetS X).Nonempty := ⟨_, dist_mem_distSetS ha hb hab⟩
  have hδ : 0 < minDist X := by
    rw [minDist, dite_eq_left hne]; exact pos_of_mem_distSetS (min'_mem _ _)
  set c := (minDist X)⁻¹
  have hc : 0 < c := inv_pos.2 hδ
  refine ⟨X.image (c • ·), card_image_of_injective _ (smul_right_injective Pt hc.ne'), ?_, ?_, ?_, ?_⟩
  · rw [Defs.minDist_smul hc, inv_mul_cancel₀ hδ.ne']
  · unfold tgap at ht ⊢
    rw [Defs.diam_smul hc, Defs.dist2_smul hc, ← mul_sub]
    calc (1 : ℝ) = c * minDist X := (inv_mul_cancel₀ hδ.ne').symm
      _ < c * (diam X - dist2 X) := mul_lt_mul_of_pos_left ht hc
  · rw [Defs.dist2_smul hc, Defs.mult_smul hc]
  · rw [Defs.minDist_smul hc, Defs.mult_smul hc]

/-- **LP**: `min(μ₂, μ_δ) ≤ (4/7)μ₂ + (3/7)μ_δ ≤ 9n/7 + 3E/7`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp97 {μ₂ μδ s n E : ℝ} (h₂ : μ₂ ≤ 3 / 2 * s) (hδ : μδ ≤ 3 * n - 2 * s + E) :
    min μ₂ μδ ≤ 9 / 7 * n + 3 / 7 * E := by
  rcases le_total μ₂ μδ with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- `n^{2/3} ≥ 1` for `n ≥ 1`. -/
theorem one_le_rpow_two_thirds {n : ℝ} (hn : 1 ≤ n) : 1 ≤ n ^ (2 / 3 : ℝ) :=
  Real.one_le_rpow hn (by norm_num)

/-- **The `9/7` bound in the nondegenerate large regime** (`Normal`, `τ > 1`), from `CoreE`.

TODO: none — proved from the statements.
Acceptance: no `sorry` (modulo the statements it uses).
Depends on: `mult_split`, `dpart`, `eprime`, `VS`, `lp97`. -/
theorem main97_normal (hcore : CoreE) (hN : Normal X) (hτ : 1 < tau X) (ht : 1 < tgap X) :
    min (mult X (dist2 X) : ℝ) (mult X (minDist X)) ≤
      9 / 7 * X.card + 3 / 7 * (cBad + CE * (X.card : ℝ) ^ (2 / 3 : ℝ)) := by
  have hsplit := mult_split ht
  have hD := dpart hN hτ
  have hE := eprime hcore hN
  have hVS := VS X
  have hDX : Dset X ⊆ X := filter_subset _ _
  have hcardDY : ((Dset X).card : ℝ) + (Yset X).card = X.card := by
    have := card_sdiff_add_card_eq_card hDX
    unfold Yset; exact_mod_cast (by omega : (Dset X).card + (X \ Dset X).card = X.card)
  have hcardS : ((Sset X ∩ Dset X).card : ℝ) + (Aset X).card = (Sset X).card := by
    have := card_inter_add_card_sdiff (Sset X) (Dset X)
    unfold Aset; exact_mod_cast this
  rw [hN.minDist_eq]
  unfold defc at hD hE
  exact lp97 hVS (by linarith)

/-- The theorem for a normalised set (`δ = 1`, `t > 1`), from `CoreE`.

TODO: none — proved from the statements.
Acceptance: no `sorry` (modulo the statements it uses). -/
theorem main97_normalized (hcore : CoreE) (Y : Finset Pt) (h2 : 2 ≤ Y.card) (h1 : minDist Y = 1)
    (ht : 1 < tgap Y) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤
      9 / 7 * Y.card + C97 * (Y.card : ℝ) ^ (2 / 3 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ Y.card := by exact_mod_cast (by omega : 1 ≤ Y.card)
  have hr := one_le_rpow_two_thirds hn1
  have hn0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ C97 := by norm_num [C97]
  have hCr : C97 ≤ C97 * (Y.card : ℝ) ^ (2 / 3 : ℝ) := le_mul_of_one_le_right hC hr
  have hm₂ := min_le_left (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hmδ := min_le_right (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hδ3 := mult_minDist_le Y
  -- `n ≤ 3`
  by_cases h4 : Y.card < 4
  · have : (Y.card : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 h4
    have : (10 : ℝ) ≤ C97 := by norm_num [C97]
    linarith
  rw [not_lt] at h4
  -- degenerate regime
  by_cases hd : 1.94 * dist2 Y < diam Y
  · have := degenerate h4 hd
    have : (1 : ℝ) ≤ C97 := by norm_num [C97]
    linarith
  rw [not_lt] at hd
  -- nondegenerate, small `Δ₂`
  by_cases hs : dist2 Y < 10 ^ 4
  · have := card_lt_N0 h1 hd hs
    have : 3 * N₀ ≤ C97 := by norm_num [N₀, C97]
    linarith
  rw [not_lt] at hs
  have hN : Normal Y := ⟨h4, h1, hd, hs⟩
  have hτ := one_lt_tau_of hN.dist2_pos ht
  have h := main97_normal hcore hN hτ ht
  have hcb : 3 / 7 * cBad ≤ C97 / 2 := by norm_num [cBad, C97]
  have hce : 3 / 7 * CE ≤ C97 / 2 := by norm_num [CE, C97]
  have hce' : 3 / 7 * CE * (Y.card : ℝ) ^ (2 / 3 : ℝ) ≤ C97 / 2 * (Y.card : ℝ) ^ (2 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right hce (by positivity)
  nlinarith

/-- **Erdős #132, `τ > 1` (conditional on `CoreE`)**: for every `n`-point planar set with
`δ < Δ − Δ₂` (i.e. `τ > 1` after normalising `δ = 1`),
`min{μ(Δ₂), μ(δ)} ≤ 9n/7 + C·n^{2/3}`.

TODO: none — proved from the statements.
Acceptance: no `sorry` once the non-core lemmas are filled; `#print axioms` standard. -/
theorem erdos132_main97_of_core (hcore : CoreE) :
    ∃ C : ℝ, ∀ X : Finset Pt, 2 ≤ X.card → minDist X < diam X - dist2 X →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤
        9 / 7 * X.card + C * (X.card : ℝ) ^ (2 / 3 : ℝ) := by
  refine ⟨C97, fun X hX ht => ?_⟩
  obtain ⟨Y, hc, h1, htY, hm₂, hmδ⟩ := exists_normalize97 hX ht
  rw [← hm₂, ← hmδ, ← hc]
  exact main97_normalized hcore Y (hc ▸ hX) h1 htY

/-- **Erdős #132, `τ > 1`**: `min{μ(Δ₂), μ(δ)} ≤ 9n/7 + C·n^{2/3}` whenever `δ < Δ − Δ₂`.

TODO: none beyond `core`.
Acceptance: inherits exactly the `sorry` of `core` (and of unfilled lemmas). -/
theorem erdos132_main97 :
    ∃ C : ℝ, ∀ X : Finset Pt, 2 ≤ X.card → minDist X < diam X - dist2 X →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤
        9 / 7 * X.card + C * (X.card : ℝ) ^ (2 / 3 : ℝ) :=
  erdos132_main97_of_core core

/-- The same with the literal hypotheses `δ = 1`, `τ > 1`.

TODO: none — proved from the statements.
Acceptance: as `erdos132_main97`. -/
theorem erdos132_main97_tau :
    ∃ C : ℝ, ∀ X : Finset Pt, 2 ≤ X.card → minDist X = 1 → 1 < tau X →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤
        9 / 7 * X.card + C * (X.card : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨C, hC⟩ := erdos132_main97
  refine ⟨C, fun X hX h1 hτ => hC X hX ?_⟩
  rw [h1]
  exact one_lt_tgap_of (dist2_nonnegR X) (tgap_nonneg X) hτ

end

end Erdos132Main

#print axioms Erdos132Main.erdos132_main97_of_core
#print axioms Erdos132Main.erdos132_main97

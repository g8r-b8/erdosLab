import Erdos.E132Main2116Good
import Erdos.E132Main2116ClassI
import Erdos.E132Main2116DischI
import Erdos.E132Main2116RegionIIw
import Erdos.E132Main2116RegionIIe

/-!
# Erdős Problem 132 — Theorem 1(b): `min{μ(Δ₂), μ(δ)} ≤ (21/16)n + C₁` off Region III

Paper §10 (proof of Theorem 1(b) for `τ(X) ≤ √3/2 − 1/50` and for `τ(X) > 1`, from Theorem P4)
and §11 (thm:IIone, from thm:IIe and thm:IIw).

* **Theorem P4** (`W7_I`): Region I or `τ > 1`, `Δ₂ ≥ 2·10¹⁵` ⇒ `Σ_R v ≤ 7r + 5cEP`
  (`weight7_of_rules` with the rules `ShapeI`: `classI_shape`, `recvI_dest`, `loadI`;
  exceptions `card_EP_le`).
* **Theorem IIw** (`W7_II`): the same in Region II with `τ ≤ 1` (rules `ShapeII`).
* **Theorem IIe** (`regionIIe`): `e(S) ≤ s + |Q|/2 + cIIe` in Region II with `τ ≤ 1`.
* `e(S) ≤ s + C` in Region I (`regionI`) and for `τ > 1` (`regionII_high`) — unchanged `54/37`.
* LP with weights `5/8, 3/8` (`lp2116`, lem:lpavg(b), lem:IIlp), weighted (VS) `VS_weighted`
  with `Q = Q2` (all points of `S` of `Δ₂`-degree `1`).
* Small cases: `n ≤ 3`; degenerate `Δ > 1.94Δ₂` (`degenerate`: `μ(Δ₂) ≤ n + 1`);
  `Δ₂ < 2·10¹⁵` (packing, `card_le_of_small2116`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Weight 7 -/

/-- Classification in Region I / `τ > 1` as an admissible charge vector.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `frameP_of_good`, `classI_shape`, `shapeI_facts`. -/
theorem sendRuleI_of_good (hX : Normal X) (hL : bigD2 ≤ dist2 X)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) {y : Pt} (hy : y ∈ Rset X) (h8 : 8 ≤ vR X y)
    (hg : IsGoodP X y) : ∃ a, SendRule (ShapeI X) X y a := by
  obtain ⟨n, hF⟩ := frameP_of_good hX hy h8 hg
  obtain ⟨a, ha⟩ := classI_shape hX hL hF hτ hy h8
  obtain ⟨h0, hs, hsum⟩ := shapeI_facts ha
  exact ⟨a, hy, hg, h8, h0, hs, hsum, n, hF, ha⟩

/-- Classification in Region II (`τ ≤ 1`) as an admissible charge vector.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `frameP_of_good`, `IIclass_shape`, `shapeI_facts`, `shapeII_to_I`. -/
theorem sendRuleII_of_good (hX : Normal X) (hL : bigD2 ≤ dist2 X)
    (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1) {y : Pt} (hy : y ∈ Rset X)
    (h8 : 8 ≤ vR X y) (hg : IsGoodP X y) : ∃ a, SendRule (ShapeII X) X y a := by
  obtain ⟨n, hF⟩ := frameP_of_good hX hy h8 hg
  obtain ⟨a, ha⟩ := IIclass_shape hX hL hF hτ₁ hτ₂ hy h8
  obtain ⟨h0, hs, hsum⟩ := shapeI_facts (shapeII_to_I ha)
  exact ⟨a, hy, hg, h8, h0, hs, hsum, n, hF, ha⟩

/-- **Theorem P4**: in Region I and for `τ > 1`, with `Δ₂ ≥ 2·10¹⁵`,
`Σ_{y∈R} v(y) ≤ 7r + 5cEP`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `weight7_of_rules`, `sendRuleI_of_good`, `recvI_dest`, `loadI`, `card_EP_le`. -/
theorem W7_I (hX : Normal X) (hL : bigD2 ≤ dist2 X)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) :
    ∑ y ∈ Rset X, (vR X y : ℝ) ≤ 7 * (Rset X).card + 5 * cEP := by
  have h := weight7_of_rules (ShapeI X)
    (fun y hy h8 hg => sendRuleI_of_good hX hL hτ hy h8 hg)
    (fun y a hr x hx => recvI_dest hX hL hτ hr hx) (loadI hX hL hτ)
  have := card_EP_le hX hL
  linarith

/-- **Theorem IIw**: in Region II with `τ ≤ 1` and `Δ₂ ≥ 2·10¹⁵`, `Σ_{y∈R} v(y) ≤ 7r + 5cEP`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `weight7_of_rules`, `sendRuleII_of_good`, `recvII_dest`, `loadII`, `card_EP_le`. -/
theorem W7_II (hX : Normal X) (hL : bigD2 ≤ dist2 X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    ∑ y ∈ Rset X, (vR X y : ℝ) ≤ 7 * (Rset X).card + 5 * cEP := by
  have h := weight7_of_rules (ShapeII X)
    (fun y hy h8 hg => sendRuleII_of_good hX hL hτ₁ hτ₂ hy h8 hg)
    (fun y a hr x hx => recvII_dest hX hL hτ₁ hτ₂ hr hx) (loadII hX hL hτ₁ hτ₂)
  have := card_EP_le hX hL
  linarith

/-! ## Assembly -/

/-- `μ(δ) ≤ e(S) + (7/2)r + (5/2)cEP` from the exact identity and average weight `7`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `mu_delta_identity`. -/
theorem E_bound2116 (hW : ∑ y ∈ Rset X, (vR X y : ℝ) ≤ 7 * (Rset X).card + 5 * cEP) :
    (mult X (minDist X) : ℝ) ≤ eS X + 7 / 2 * (Rset X).card + 5 / 2 * cEP := by
  have hid := mu_delta_identity X
  have hcast : ((∑ y ∈ Rset X, (degδ X y + mS X y) : ℕ) : ℝ) =
      ∑ y ∈ Rset X, (vR X y : ℝ) := by
    rw [Nat.cast_sum]; rfl
  have h2 : (2 * mult X (minDist X) : ℝ) = 2 * eS X + ∑ y ∈ Rset X, (vR X y : ℝ) := by
    rw [← hcast]; exact_mod_cast hid
  linarith

/-- LP step of Theorem 1(b) in the nondegenerate regime (lem:lpavg(b) / lem:IIlp).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `VS_weighted`, `E_bound2116`, `lp2116`, `card_S_add_R`. -/
theorem assemble2116 {Y : Finset Pt} {Q : Finset Pt} (hQS : Q ⊆ Sset Y)
    (hQ : ∀ v ∈ Q, deg2 Y v = 1) {C₂ : ℝ}
    (he : (eS Y : ℝ) ≤ (Sset Y).card + 1 / 2 * Q.card + C₂)
    (hW : ∑ y ∈ Rset Y, (vR Y y : ℝ) ≤ 7 * (Rset Y).card + 5 * cEP) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤
      21 / 16 * Y.card + 3 / 8 * (5 / 2 * cEP + C₂) := by
  have hsr : ((Sset Y).card : ℝ) + (Rset Y).card = Y.card := by
    exact_mod_cast card_S_add_R Y
  have hsp : ((Sset Y \ Q).card : ℝ) + Q.card = (Sset Y).card := by
    exact_mod_cast card_sdiff_add_card_eq_card hQS
  have h₂ := VS_weighted hQS hQ
  have h₂' : (mult Y (dist2 Y) : ℝ) ≤ Q.card + 3 / 2 * ((Sset Y).card - Q.card) := by linarith
  have h := lp2116 (Nat.cast_nonneg _) h₂' (E_bound2116 hW) he
  rw [hsr] at h
  exact h

/-- Theorem 1(b) for a normalised set (`δ = 1`).

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits). -/
theorem main2116_normalized (Y : Finset Pt) (h1 : minDist Y = 1)
    (hτ : tauInv Y ≤ √3 / 2 - 1 / 50 ∨ √3 / 2 + 3 / 100 ≤ tauInv Y) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 21 / 16 * Y.card + C2116 := by
  have hn0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  obtain ⟨hcA, hcB, hcS, hc9, hc1⟩ := consts2116
  have hm₂ := min_le_left (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hmδ := min_le_right (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hδ3 := mult_minDist_le Y
  -- `n ≤ 3`
  by_cases h4 : Y.card < 4
  · have : (Y.card : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 h4
    linarith
  rw [not_lt] at h4
  -- degenerate regime
  by_cases hd : 1.94 * dist2 Y < diam Y
  · have := degenerate h4 hd
    linarith
  rw [not_lt] at hd
  -- nondegenerate, `Δ₂ < 2·10¹⁵`
  by_cases hs : dist2 Y < bigD2
  · have := card_le_of_small2116 h1 h4 hd hs
    linarith
  rw [not_lt] at hs
  -- nondegenerate, large
  have hN : Normal Y := ⟨h4, h1, hd, by unfold bigD2 at hs; linarith⟩
  have hτeq : tauInv Y = tau Y := tauInv_eq_tau h1 hN.dist2_pos.ne'
  rw [hτeq] at hτ
  obtain ⟨F⟩ := dirField_nonempty Y
  have hQ2S : Q2 Y ⊆ Sset Y := filter_subset _ _
  have hQ2d : ∀ v ∈ Q2 Y, deg2 Y v = 1 := fun v hv => (mem_filter.1 hv).2
  rcases hτ with hI | hII
  · -- Region I
    have hI' : tau Y ≤ √3 / 2 - 2 * beta := by unfold beta; linarith
    have he := regionI hN F hI'
    have := assemble2116 (Q := ∅) (empty_subset _) (by simp) (C₂ := cBad + 100)
      (by simp only [card_empty, Nat.cast_zero, mul_zero, add_zero]; linarith)
      (W7_I hN hs (Or.inl hI'))
    linarith
  · have hII' : √3 / 2 + 3 * beta ≤ tau Y := by unfold beta; linarith
    by_cases hhigh : 1 < tau Y
    · -- `τ > 1`
      have he := regionII_high hN F hhigh
      have := assemble2116 (Q := ∅) (empty_subset _) (by simp) (C₂ := cBad + 100)
        (by simp only [card_empty, Nat.cast_zero, mul_zero, add_zero]; linarith)
        (W7_I hN hs (Or.inr hhigh))
      linarith
    · -- Region II, `τ ≤ 1`
      rw [not_lt] at hhigh
      have := assemble2116 hQ2S hQ2d (regionIIe hN F hII' hhigh) (W7_II hN hs hII' hhigh)
      linarith

/-- **Theorem 1(b)** (paper, thm:IIone): there is an absolute `C₁` such that every planar set
`X` with `n ≥ 2` points and `τ(X) ≤ √3/2 − 1/50` or `τ(X) ≥ √3/2 + 3/100` has
`min{μ(Δ₂), μ(δ)} ≤ (21/16)n + C₁`.

TODO: none — proved from the lemma statements.
Acceptance: no `sorry` (inherits the lemma sorries until Phase 2 is complete). -/
theorem erdos132_main2116 : ∃ C₁ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
    (tauInv X ≤ √3 / 2 - 1 / 50 ∨ √3 / 2 + 3 / 100 ≤ tauInv X) →
    (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 21 / 16 * X.card + C₁ := by
  refine ⟨C2116, fun X hX hτ => ?_⟩
  obtain ⟨Y, hc, h1, hm₂, hmδ, hτY⟩ := exists_normalize2116 hX
  rw [← hm₂, ← hmδ, ← hc]
  rw [← hτY] at hτ
  exact main2116_normalized Y h1 hτ

end

end Erdos132Main

#print axioms Erdos132Main.erdos132_main2116

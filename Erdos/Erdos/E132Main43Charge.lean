import Erdos.E132Main43Frame

/-!
# Erdős Problem 132, `4/3` theorem — receivers and owner uniqueness (§1.4)

Paper: `angle_R6.md` §1.4.  Every heavy good point `y` passes its excess `v(y) − 8` to its
receivers `Low X y` (neighbours at least `2/3` deeper than `y`).

* **Receivers** (`low_receiver`): a receiver `a` is interior to `K` (so `a ∈ R`), has height
  `≤ −2/3` (`Low_Z`), and every `S`-neighbour `q` of `a` has height `≥ h − 2/49`; so `q − a`
  and `y − a` are unit vectors within `60°` of `n`, and at most two such are `≥ 60°` apart
  (`card_cone_le_two`): `m_a ≤ 1`, `v(a) ≤ 7`.
* **Owner uniqueness** (`low_disjoint`): fans and caps never coexist (Lemma Pin, `t` global);
  two caps sharing `b` would both sit within `1/20` above `b` (`frame_normal_close`); two fans
  `y ≠ y′` sharing `a` sit at `≈ ±30°` above `a`, so `y′` is `y`'s neighbour in a `±90°` slot
  (`fan_common_low_slot`), which is not in `S`, so `y` is HF2 — and symmetrically `y′`; then
  `y`'s D at `σ·30°` and `y′`'s D at `−σ·30°` coincide in a point `z ∈ D` with four
  `δ`-neighbours, contradicting `degδ_le_three_of_D`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Receivers -/

/-- A receiver has at most one `S`-neighbour.

TODO: prove.
What's missing (paper §1.4, "fan receiver"): `Z a ≤ −2/3` (`Low_Z`).  An `S`-neighbour `q` of
`a` has `dist q y ≤ 2`, `q ∉ int K` (`Sset_not_interior`), so `Z q ≥ h − 2/49`
(`frame_outside`, `|Xq| ≤ 2`) and `⟨q − a, n⟩ ≥ 2/3 − 2/49 > 1/2`; also
`⟨y − a, n⟩ = −Z a ≥ 2/3 > 1/2` and `y ∉ S` (`y ∈ R`), `y ∈ X`.  Apply `card_cone_le_two` to
`insert y (S-neighbours of a)` (unit distances `dist_of_mem_nbδ`, separation `one_le_dist`):
`1 + m_a ≤ 2`.
Acceptance: no `sorry`.
Depends on: `Low_Z`, `frame_outside`, `Sset_not_interior`, `card_cone_le_two`,
`dist_of_mem_nbδ`, `one_le_dist`, `Low_subset`. Difficulty M. -/
theorem mS_le_one_of_Low (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    {a : Pt} (ha : a ∈ Low X y) : mS X a ≤ 1 := by
  sorry

/-- **Receivers are in `R` and have weight `≤ 7`.**

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `Low_interior`, `Sset_not_interior`, `degδ_le_six`, `mS_le_one_of_Low`. -/
theorem low_receiver (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    {a : Pt} (ha : a ∈ Low X y) : a ∈ Rset X ∧ vR X a ≤ 7 := by
  have haX : a ∈ X := (mem_nbδ.1 (Low_subset X y ha)).1
  have hint := Low_interior ha
  have haS : a ∉ Sset X := fun h => Sset_not_interior hX h hint
  refine ⟨mem_sdiff.2 ⟨haX, haS⟩, ?_⟩
  unfold vR
  have := degδ_le_six X a
  have := mS_le_one_of_Low hX hF hy ha
  omega

/-! ## Owner uniqueness -/

/-- **Two fans sharing a receiver are horizontal neighbours**: `y′ − y` is within `7/20` of
`±perp n`.

TODO: prove.
What's missing (paper §1.4, "fan"): `e = y − a`, `e′ = y′ − a` are unit (`Low_subset`,
`dist_of_mem_nbδ`), `‖e − e′‖ = dist y y′ ≥ 1` (`one_le_dist`), `⟨e, n⟩ ≥ 4/5` (`IsFan43`),
`⟨e′, n′⟩ ≥ 4/5` and `‖n′ − n‖ ≤ 1/50` (`frame_normal_close`, `dist y y′ ≤ 2`), so
`⟨e′, n⟩ ≥ 0.78`.  In angles from `n`: `|α| ≤ 36.9°`, `|α′| ≤ 38.8°`, `|α − α′| ≥ 60°`, so
`y′ − y = e′ − e` has length `∈ [1, 1.226]` and direction within `8.8°` of `±perp n`; hence
`‖y′ − y − dirF n (±π/2)‖ ≤ 0.282 < 7/20`.  (A coordinate proof: with `x = ⟨·, perp n⟩`,
`c = ⟨·, n⟩`, bound `|c′ − c|` and `|x′ − x| − 1`.)
Acceptance: no `sorry`.
Depends on: `frame_normal_close`, `one_le_dist`, `dist_of_mem_nbδ`, `n1_inner_frame`,
`norm_perp`. Difficulty M–L. -/
theorem fan_common_low_slot (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X) (hf : IsFan43 X y n)
    (hf' : IsFan43 X y' n') {a : Pt} (ha : a ∈ Low X y) (ha' : a ∈ Low X y')
    (hne : y ≠ y') :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖y' - y - dirF n (σ * (π / 2))‖ ≤ 7 / 20 := by
  sorry

/-- **Fans have private receivers.**

TODO: prove.
What's missing (paper §1.4, "fan", with the HF2–HF2 argument): suppose `a ∈ Low y ∩ Low y′`.
`fan_common_low_slot` gives `σ′`; the slot neighbour of `y` at `σ′·90°` (from `FanSlots`: `p` at
`−σ·90°` or `q` at `σ·90°`, within `1/20`) is within `7/20 + 1/20 < 1` of `y′`, hence equals
`y′` (`one_le_dist`).  It is not `p` (`p ∈ S`, `y′ ∈ R`), so `σ′ = σ`, `y′ = q ∉ S`, and the
HF2 branch gives `z₁` (slot `σ·30°`), `z₂` (slot `−σ·30°`), `dist z₁ z₂ = 1`.  Symmetrically
(roles swapped, `frame_normal_close`) `y = q′` is `y′`'s slot-`σ₁·90°` neighbour with HF2 data
`z₁′, z₂′`, and `σ₁ = −σ` (`y − y′ ≈ −σ perp n`, `‖n − n′‖ ≤ 1/50`).  Then
`‖z₁ − z₁′‖ ≤ 3/20 + 1/50 < 1` (`dirF n (σπ/2) + dirF n (−σπ/6) = dirF n (σπ/6)`, and
`‖dirF n ψ − dirF n′ ψ‖ = ‖n − n′‖`), so `z := z₁ = z₁′ ∈ D`.  Its `δ`-neighbours include `y`,
`y′`, `z₂`, `z₂′` (distances `= minDist`), pairwise `≥ 0.8` apart by their positions
`0, dirF(σπ/2), dirF(−σπ/6), dirF(σπ/2) + dirF(σπ/6)` relative to `y` (errors `≤ 0.2`), so
`degδ X z ≥ 4`, contradicting `degδ_le_three_of_D`.
Acceptance: no `sorry`.
Depends on: `fan_common_low_slot`, `frame_normal_close`, `degδ_le_three_of_D`, `one_le_dist`,
`mem_nbδ`, `dist_of_mem_nbδ`. Difficulty L. -/
theorem fan_disjoint (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X) (hf : IsFan43 X y n)
    (hf' : IsFan43 X y' n') (hne : y ≠ y') : Disjoint (Low X y) (Low X y') := by
  sorry

/-- **Caps have private receivers**: two caps sharing a receiver `b` satisfy
`‖y − y′‖ ≤ 1/20 + 1/20 + 1/50 < 1`.

TODO: prove.
What's missing: `‖b − y + n‖ ≤ 1/20`, `‖b − y′ + n′‖ ≤ 1/20` (`IsCap43`), `dist y y′ ≤ 2`
(both at distance `1` from `b`), `‖n′ − n‖ ≤ 1/50` (`frame_normal_close`); then
`dist y y′ < 1` contradicts `one_le_dist`.
Acceptance: no `sorry`.
Depends on: `frame_normal_close`, `one_le_dist`, `dist_of_mem_nbδ`, `Low_subset`.
Difficulty S–M. -/
theorem cap_disjoint (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X) (hc : IsCap43 X y n)
    (hc' : IsCap43 X y' n') (hne : y ≠ y') : Disjoint (Low X y) (Low X y') := by
  sorry

/-- **Owner uniqueness** (§1.4): distinct heavy good points have disjoint receiver sets.
Fans and caps never coexist (`t ≥ 0.7` vs `t ≤ 0.6`).

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `fan_disjoint`, `cap_disjoint`. -/
theorem low_disjoint (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X)
    (ht : IsFan43 X y n ∨ IsCap43 X y n) (ht' : IsFan43 X y' n' ∨ IsCap43 X y' n')
    (hne : y ≠ y') : Disjoint (Low X y) (Low X y') := by
  rcases ht with hf | hc <;> rcases ht' with hf' | hc'
  · exact fan_disjoint hX hF hF' hy hy' hf hf' hne
  · exfalso; linarith [hf.1, hc'.1]
  · exfalso; linarith [hc.1, hf'.1]
  · exact cap_disjoint hX hF hF' hy hy' hc hc' hne

end

end Erdos132Main

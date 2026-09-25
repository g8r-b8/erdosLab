import Erdos.E132Main2116Frame

/-!
# Erdős Problem 132, `21/16` — classification in Region I and for `τ > 1` (§10.2)

Paper §10 "Neighbours in `S` and classification": **lem:S3** and **lem:classP4**.  Standing
hypotheses: `Normal X`, `Δ₂ ≥ 2·10¹⁵`, and `τ ≤ √3/2 − 2β` (Region I) or `τ > 1`; so
`t ≤ t_I < 0.84604` or `t > 1`.  `y ∈ R` has a frame `FrameP X y n` (it is good′ of weight
`≥ 8`; the frame is produced by `frameP_of_good`).

Output (`classI_shape`, proved from the sorried lemmas): every such `y` of weight `≥ 8` has
one of the shapes of `ShapeI` in the frame `n` — `TwoShape` (types A, B, C_φ), `APShape`
(A′), `CapShapeP` (cap), `DtShape` (Dt) — together with its charge vector.  The shapes record
the exact slots (hexagon of neighbours) and the pinned values of `t` that the discharging
(`E132Main2116DischI`) needs.

Tolerances: angles `ηA = 10⁻³` (paper: `0.012° = 2.1·10⁻⁴`), pinned `t` values `ηT = 10⁻³`
(paper: `δ₀ = 10⁻⁴`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- **lem:S3(a)**: for `t > 1 + 2δ₀`, `y` has no D-neighbour (a D-neighbour would have height
`≥ h + H ≥ t − δ₀/2 > 1`).

TODO: prove.
What's missing: `flat_D` gives `Z q ≥ h + H ≥ t − δ₀/2 > 1` for a diametral neighbour `q`
(within `1 ≤ 6` of `y`), but `Z q ≤ ‖q − y‖ = 1` (Cauchy–Schwarz) and `h > 0`.
Acceptance: no `sorry`.
Depends on: `flat_D`, `FrameP.depth_pos`, `dist_of_mem_nbδ`. Difficulty S. -/
theorem S3_noD (hX : Normal X) {y n : Pt} (hF : FrameP X y n) (ht : 1 + 2 * δ₀P < tgap X) :
    ∀ q ∈ nbδ X y, q ∉ Dset X := by
  sorry

/-- **lem:S3(b)**: `m_y ≤ 3` in Region I and for `τ > 1`.

TODO: prove.
What's missing: paper proof of lem:S3(b).  First `m_y ≤ 4` (the `S`-neighbours lie outside
`int K`, hence at height `≥ h − δ₀/5 > −δ₀`, i.e. in an open arc `< 240°`; as
`mS_le_four_of_flat`/`card_sep_arc_le_four`).  If `m_y = 4`, the `S`-neighbours are K-row
points near `±90°` and D-neighbours near `±30°` (mirror pairs `pair_K2116`, `pair_D2116`,
at most two of each kind, `60°` separation); pinning (`flat_pin`) gives
`t ≥ cos(30° + ε) − δ₀ > 0.8659`, contradicting `t ≤ t_I < 0.8461` (Region I:
`t ≤ τ + 1/(2Δ₂)`) and, for `τ > 1` (`t > 1`), `Z ≤ 0.87 < t − δ₀/2 ≤ H` for the
D-neighbours (`flat_D`).
Acceptance: no `sorry`.
Depends on: `flat_K`, `flat_D`, `flat_pin`, `pair_K2116`, `pair_D2116`, `nb_kind`,
`card_sep_arc_le_four`, `tau_sub_tgap`/`one_lt_tau_iff_alg`. Difficulty M–L. -/
theorem S3_mS_le (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) (hy : y ∈ Rset X) : mS X y ≤ 3 := by
  sorry

/-- **lem:S3(c)**: if `m_y = 3`, the `S`-neighbours are a K-row mirror pair at `±ψ` with
`60° ≤ ψ ≤ 90°` and one D-neighbour between them, and `sin(ψ − 30°) ≤ t ≤ 1 − cos ψ`
(up to the tolerances of `KKDShape`).

TODO: prove.
What's missing: paper proof of lem:S3(c).  By the pair property the kinds are `{K, K, D}` or
`{K, D, D}`; the latter forces a D-pair at `±30°`, a K-row point near `±90°` and `t > 0.8659`
(excluded as in `S3_mS_le`).  In the former the K-pair is at `ψ₁`, `−ψ₂` (`pair_K2116`:
`|ψ₁ − ψ₂| ≤ 10⁻⁴/…`), and the D-neighbour, at height `> h` hence in the upper arc, is `≥ 60°`
from both: `ψD ∈ [−ψ₂ + 60°, ψ₁ − 60°]` (exact).  Pinning (`flat_pin`) gives
`t = cos ψD − cos ψ₁ ± δ₀/5`, and `cos(ψ₁ − 60°) − ηA ≤ cos ψD ≤ 1`.
Acceptance: no `sorry`.
Depends on: `S3_mS_le` (statement), `flat_K`, `flat_D`, `flat_pin`, `pair_K2116`,
`pair_D2116`, `nb_kind`, `nb_above_D`, `exists_angle`. Difficulty M–L. -/
theorem S3_three (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) (hy : y ∈ Rset X) (hm : mS X y = 3) :
    ∃ ψ₁ ψ₂, KKDShape X y n ψ₁ ψ₂ := by
  sorry

/-- **lem:classP4, weight `(6, 2)`**: types A, B, C_φ (a `TwoShape`) or A′ (an `APShape`).

TODO: prove.
What's missing: paper proof of lem:classP4, cases "(6,2), two K-neighbours / two
D-neighbours / a K- and a D-neighbour".  The neighbours form an exact hexagon
(`hex_of_deg6`); choose its slot `φ ∈ [−30°, 30°]` with the largest height and the reflection
`σ`.  Two K-row: mirror pair (`pair_K2116`) at `±30°` (A: `TwoShape` with `φ ≈ 30°`), `±60°`
(the `0°` slot has height `1 > h = 1/2`, so it is a D-neighbour in `R` (`nb_above_D`, `m = 2`)
and `t = 1/2` by `flat_pin`: A′, `APShape`), or `±90°` (then the `±30°` slots are
D-neighbours and `t > 0.8659`: excluded).  Two D: only `±30°` survives (B).  K and D: C_φ
(or A with one D-neighbour if `t ≤ 2δ₀`); the pinned relation `t = sin(30° − φ)` is
`cos φ − cos(φ − 60°)` exactly (`flat_pin`).  For `t > 1 + 2δ₀` only type A (`S3_noD`).
Acceptance: no `sorry`.
Depends on: `hex_of_deg6`, `flat_K`, `flat_D`, `flat_pin`, `flat_int`, `pair_K2116`,
`pair_D2116`, `nb_kind`, `nb_above_D`, `S3_noD`. Difficulty L. -/
theorem class62 (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) (hy : y ∈ Rset X)
    (hdeg : degδ X y = 6) (hm : mS X y = 2) :
    (∃ σ φ, TwoShape X y n σ φ) ∨ ∃ φ, APShape X y n φ := by
  sorry

/-- **lem:classP4, weight `(6, 3)`**: the cap (K-row at `±60°`, a D-neighbour in `S` at `0°`,
`t = 1/2`).  (For `τ > 1` this case does not occur.)

TODO: prove.
What's missing: paper proof, case "(5,3) and (6,3)" with `deg = 6`: by `S3_three` the K-pair
occupies mirror slots of the hexagon, `ψ ∈ {30°, 60°, 90°}`; `30°` leaves no room for the
D-neighbour, `90°` forces `t > 0.8659` (excluded), `60°` puts the D-neighbour at `0°` and
`t = 1 − 1/2` (`flat_pin`).  The base angle of the hexagon is `ψD`, `|ψD| ≤ 10⁻⁴` by the
mirror pair.
Acceptance: no `sorry`.
Depends on: `S3_three`, `hex_of_deg6`, `flat_pin`, `pair_K2116`. Difficulty M. -/
theorem class63 (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) (hy : y ∈ Rset X)
    (hdeg : degδ X y = 6) (hm : mS X y = 3) :
    ∃ φ, CapShapeP X y n φ := by
  sorry

/-- **lem:classP4, weight `(5, 3)`**: type Dt (the `S`-neighbours of `S3_three` and two
interior neighbours in the lower arc `I_y`).

TODO: prove.
What's missing: paper proof, case "(5,3)", `deg = 5`: the two other neighbours are not in `S`
(`m = 3`); each is `≥ 60°` from the two K-row neighbours and the D-neighbour; one in the upper
arc would need `ψ₁ − ψD ≥ 120°`, impossible (`ψ₁ ≤ 90° + ηA`, `ψD ≥ −ψ₂ + 60°`); so both lie
in `[ψ₁ + 60°, 300° − ψ₂]` (angles via `exists_angle`, `60°` separation from unit distances).
Acceptance: no `sorry`.
Depends on: `S3_three`, `nb_kind`, `dist_of_mem_nbδ`, `one_le_dist`, `exists_angle`.
Difficulty M. -/
theorem class53 (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) (hy : y ∈ Rset X)
    (hdeg : degδ X y = 5) (hm : mS X y = 3) :
    ∃ ψ₁ ψ₂ x₁ x₂, DtShape X y n ψ₁ ψ₂ x₁ x₂ := by
  sorry

/-- **lem:classP4** (all weights `≥ 8`): a good′ `y ∈ R` of weight `≥ 8` (with a frame) has one
of the shapes of `ShapeI`, with its charge vector.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `S3_mS_le`, `degδ_le_six`, `class62`, `class63`, `class53`. -/
theorem classI_shape (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) (hy : y ∈ Rset X) (h8 : 8 ≤ vR X y) :
    ∃ a, ShapeI X y n a := by
  have hm3 := S3_mS_le hX hL hF hτ hy
  have hd6 := degδ_le_six X y
  have hcases : (degδ X y = 6 ∧ mS X y = 2) ∨ (degδ X y = 6 ∧ mS X y = 3) ∨
      (degδ X y = 5 ∧ mS X y = 3) := by
    unfold vR at h8
    omega
  rcases hcases with ⟨hd, hm⟩ | ⟨hd, hm⟩ | ⟨hd, hm⟩
  · rcases class62 hX hL hF hτ hy hd hm with ⟨σ, φ, hs⟩ | ⟨φ, hs⟩
    · exact ⟨_, Or.inl ⟨σ, φ, hs, rfl⟩⟩
    · exact ⟨_, Or.inr (Or.inl ⟨φ, hs, rfl⟩)⟩
  · obtain ⟨φ, hs⟩ := class63 hX hL hF hτ hy hd hm
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨φ, hs, rfl⟩))⟩
  · obtain ⟨ψ₁, ψ₂, x₁, x₂, hs⟩ := class53 hX hL hF hτ hy hd hm
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨ψ₁, ψ₂, x₁, x₂, hs, rfl⟩))⟩

end

end Erdos132Main

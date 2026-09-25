import Erdos.E132Main2116Frame

/-!
# Erdős Problem 132, `21/16` — average weight `7` in Region II (§11.2, Theorem IIw)

Paper §11.2: **lem:IIS**, **lem:IIclass**, the discharging (type A: `1/2` to the neighbours
near `±150°`; type Dt_II: `1/2` to each interior neighbour; forwarders of weight `7` pass on to
`2x − k`), **lem:IIrecv**, **lem:IIloads**.  Standing hypotheses: `Normal X`, `Δ₂ ≥ 2·10¹⁵`,
`√3/2 + 3β ≤ τ ≤ 1` (so `t ≥ τ ≥ t_II > 0.89602` and `t ≤ 1`).  Pinning is not needed here.

The rules are the charge vectors of `ShapeII` (`E132Main2116Defs`): type A is a `TwoShape`
with `φ ≈ 30°` and both `S`-neighbours K-row; Dt_II is a `DtShape` (with `ψ₁, ψ₂ ≥ 84°`).
Consumed by `W7_II` (`E132Main2116`) through `weight7_of_rules`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- **lem:IIS**: a good′ point has at most one D-neighbour; every D-neighbour is at height
`> 0.89` (`|ψ| < 26.38°`); `m_y ≤ 3`.

TODO: prove.
What's missing: paper proof of lem:IIS: a D-neighbour has height `≥ h + H ≥ t − δ₀/2 > 0.8958`
(`flat_D`, `h > 0`; `t ≥ τ` since `t ≤ 1`, `tau_sub_tgap`); two neighbours are `≥ 60°` apart,
so two of them cannot both be in the open cone `|ψ| < 26.38°`; at most two K-row neighbours
(`pair_K2116`); every neighbour in `S` is K-row or D (`nb_kind`).
Acceptance: no `sorry`.
Depends on: `flat_D`, `pair_K2116`, `nb_kind`, `dist_of_mem_nbδ`, `one_le_dist`,
`tau_sub_tgap`. Difficulty S–M. -/
theorem IIS (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1) :
    (∀ q ∈ nbδ X y, q ∈ Dset X → 89 / 100 < inner ℝ (q - y) n) ∧
      ((nbδ X y).filter (· ∈ Dset X)).card ≤ 1 ∧ mS X y ≤ 3 := by
  sorry

/-- **lem:IIclass**: a good′ `y ∈ R` of weight `≥ 8` has weight exactly `8` and is of type A
(hexagon within `ηA` of `±30°, ±90°, ±150°`, K-row neighbours near `±30°`) or Dt_II; i.e. it
has one of the shapes of `ShapeII`, with its charge vector.

TODO: prove.
What's missing: paper proof of lem:IIclass.  `deg = 6`: exact hexagon (`hex_of_deg6`); if
`h < 1/2` two slots have height `> h` hence are D-neighbours, contradicting `IIS`; so `h ≥ 1/2`,
no D-neighbour (it would need height `> 1.39`), `h ≥ √3/2`, K-row neighbours only at
`|ψ| ≤ 30.012°` (`flat_K`): `m = 2`, slots `±30°` (`pair_K2116`): a `TwoShape` with
`φ ∈ [30° − ηA, 30° + ηA]`, both `S`-slots K-row.  `(5, 3)`: two K-row neighbours at
`ψ₁, −ψ₂` (`|ψᵢ| ∈ [84.02°, 90.006°]`), one D-neighbour in `S` at `|ψD| < 26.38°`, two
interior neighbours in `[ψ₁ + 60°, 300° − ψ₂]`; the `t`-bounds of `KKDShape` from `flat_pin`
(`t = cos ψD − cos ψ₁ ± δ₀/5`, `cos ψD ≤ 1`, and `sin(ψ₁ − 30°) ≤ sin 60.006° < t_II − ηT`).
Acceptance: no `sorry`.
Depends on: `IIS`, `hex_of_deg6`, `flat_K`, `flat_D`, `flat_pin`, `pair_K2116`, `nb_kind`,
`nb_above_D`, `exists_angle`. Difficulty M–L. -/
theorem IIclass_shape (hX : Normal X) (hL : bigD2 ≤ dist2 X) {y n : Pt} (hF : FrameP X y n)
    (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1) (hy : y ∈ Rset X) (h8 : 8 ≤ vR X y) :
    ∃ a, ShapeII X y n a := by
  sorry

/-- **lem:IIrecv**: a receiver `x` of a sender `y` lies in `R`, has `m_x ≤ 1`, and if
`v(x) = 7` (then `y` is of type Dt_II) its target `2x − k` is a neighbour of `x` in `R` of
weight `≤ 6` (depth `> 1.73`).

TODO: prove.
What's missing: paper proof of lem:IIrecv (a)–(c): type A receivers have depth `> 1.73`, so
`m = 0`; Dt_II receivers have depth `d ∈ [0.86597, 1.10413]`, no D-neighbour, K-row
neighbours at `|β| ≤ 30.02°`, `y` at `|θ_y| ≤ 35.98°`, and two K-row neighbours are
impossible (`y` would have to lie between them, `β₂ − β₁ ≥ 120°`); if `v(x) = 7` then
`deg x = 6`, `g = 2x − k ∈ nbδ x` (`hex_of_deg6`), depth `≥ 2d − δ₀ > 1.73`, so `g ∈ R`,
`m_g = 0`.
Acceptance: no `sorry`.
Depends on: `IIclass_shape` (statement), `flat_K`, `flat_D`, `flat_int`, `hex_of_deg6`,
`nb_kind`, `Sset_not_interior`, definitions. Difficulty M. -/
theorem recvII (hX : Normal X) (hL : bigD2 ≤ dist2 X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {y : Pt} {a : Pt → ℝ} (hr : SendRule (ShapeII X) X y a) {x : Pt}
    (hx : a x ≠ 0) :
    x ∈ Rset X ∧ mS X x ≤ 1 ∧
      (vR X x = 7 → fwdTarget X x ∈ nbδ X x ∧ fwdTarget X x ∈ Rset X ∧
        vR X (fwdTarget X x) ≤ 6) := by
  sorry

/-- Charge lands in `R` at points of weight `≤ 6` (Region II).

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits `recvII`).
Depends on: `recvII`, `dest_ok`. -/
theorem recvII_dest (hX : Normal X) (hL : bigD2 ≤ dist2 X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {y : Pt} {a : Pt → ℝ} (hr : SendRule (ShapeII X) X y a) {x : Pt}
    (hx : a x ≠ 0) : dest X x ∈ Rset X ∧ vR X (dest X x) ≤ 6 := by
  obtain ⟨hxR, hm, hf⟩ := recvII hX hL hτ₁ hτ₂ hr hx
  exact dest_ok hxR hm fun h7 => (hf h7).2

/-- **lem:IIloads**: a forwarder has exactly one sender (so passes `1/2`), and every point of
`R` receives at most one unit in total.

TODO: prove.
What's missing: paper proof of lem:IIloads.  Frames of all good′ points involved lie within
`4` of each other and agree up to `ε₀` (`frameP_close`).  A forwarder has only Dt_II senders
(`recvII`), in directions `[−35.98°, 35.98°]`, and its `S`-neighbour at `|β| ≤ 30.02°`; two
senders `≥ 60°` apart would force `|β| ≥ 84°` or a gap `≥ 120°`: impossible.  Immediate
senders of `d`: type A at `±30° ± ηA`, Dt_II in `[−35.98°, 35.98°]`, forwarders at
`|β| ≤ 30.02°`; pairwise `≥ 60°` apart in a window narrower than `120°`: at most two, each
passing `1/2`.
Acceptance: no `sorry`.
Depends on: `recvII`, `frameP_close`, `flat_K`, `sendAmt_spec`, `shapeI_facts`,
`shapeII_to_I`, definitions. Difficulty L. -/
theorem loadII (hX : Normal X) (hL : bigD2 ≤ dist2 X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    ∀ d ∈ Rset X, ∑ y ∈ Rset X, Tr (ShapeII X) X y d ≤ 1 := by
  sorry

end

end Erdos132Main

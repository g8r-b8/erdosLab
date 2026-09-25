import Erdos.E132Main2116Frame

/-!
# Erdős Problem 132, `21/16` — discharging in Region I and for `τ > 1` (§10.3)

Paper §10 "Discharging": the rules (types A, B: `1/2` to `±150°`; C_φ: `1/2` to `φ + 120°`,
`φ + 180°`; A′: `1` to `180°`; cap: `1` to `180°`, `1/2` to `±120°`; Dt: `1/2` to each interior
neighbour), forwarding by receivers of weight `7`, **lem:recv2**, **lem:cone**, **lem:Th**
(band Th) and **lem:loads** (bands L, Th, H, T).

In Lean the rules are the charge vectors of the shapes of `ShapeI` (`E132Main2116Defs`), the
sender's chosen vector is `sendAmt (ShapeI X) X y`, and forwarding is *merged*: the charge
sent to `x` lands at `dest X x` (`fwdTarget X x = 2x − k` if `v(x) = 7`), and `Tr (ShapeI X) X y d`
is the charge from `y` landing at `d`.  An *immediate sender* of `d` (`ImmSender`) is a sender
giving to `d` directly or a forwarder whose target is `d`; the load of `d` is
`Σ_y Tr (ShapeI X) X y d`.

Consumed by `W7_I` (`E132Main2116`) through `weight7_of_rules`: `recvI_dest` (charge lands in
`R` at weight `≤ 6`) and `loadI` (every load `≤ 1`).

Standing hypotheses: `Normal X`, `Δ₂ ≥ 2·10¹⁵`, `τ ≤ √3/2 − 2β ∨ τ > 1`.  Depths are the
intrinsic `depth X d` (distance to `∂K`); it agrees with the frame depth `h − Z d` of the
paper up to `10⁻⁵` near a good′ point (`frameP_outside`, `FrameP.top`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- **lem:recv2(b,c)**: a receiver `x` of a sender `y` (any shape of `ShapeI`) lies in `R`,
has `m_x ≤ 1`, and if `v(x) = 7` then its target `2x − k` is a neighbour of `x` in `R` of
weight `≤ 6` (depth `> 1.7`, so `m = 0`).

TODO: prove.
What's missing: paper proof of lem:recv2 per shape, in the frame of `y`
(`FrameP` from the rule).  (a) depths: the neighbour at angle `ψ` has depth `h − cos ψ`
(`flat_K`/`FrameP.top` for `h`, exact hexagon slots).  (b) depth `> 1 + δ₀` ⇒ no neighbour in
`S` (a K-row neighbour of `x` in direction `θ` has `cos θ ∈ [d − δ₀, d]`, a D-neighbour
`cos θ ≥ d + H − δ₀`, `flat_K`, `flat_D`): types A, A′/cap at `180°`, C_φ at `φ + 180°`;
type B: the `S`-neighbour would need `|θ| ≤ 30.01°` and be `60°` from `y` and from `w`
(`±30°`); C_φ at `φ + 120°`: it would be within `0.02` of the slot `φ + 60°`, which is not in
`S`; cap at `±120°`: K-row neighbours need `|θ| ≤ 1.5°`; Dt: no D-neighbour (depth
`≥ sin(ψ₁ + 30°) > 0.8845` in Region I, `> 0.8659` for `τ > 1`), K-row neighbours in
`|θ| ≤ 30.02°`, and two of them are impossible (paper's argument).  (c) `v(x) = 7` ⇒
`deg x = 6`, `m_x = 1`; the unique `S`-neighbour `k` is at `|β| ≤ 30.02°`; the hexagon at `x`
gives `2x − k ∈ nbδ x` (`hex_of_deg6`), of depth `≥ 2d − δ₀ > 1.7`, hence interior and not in
`S` (`Sset_not_interior`), with `m = 0`; `fwdTarget X x = 2x − k` since `k` is the only
element of the filter.
Acceptance: no `sorry`.
Depends on: `flat_K`, `flat_D`, `flat_int`, `flat_pin`, `frameP_close`, `nb_kind`,
`hex_of_deg6`, `Sset_not_interior`, `shapeI_facts`, definitions. Difficulty L. -/
theorem recvI (hX : Normal X) (hL : bigD2 ≤ dist2 X) (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X)
    {y : Pt} {a : Pt → ℝ} (hr : SendRule (ShapeI X) X y a) {x : Pt} (hx : a x ≠ 0) :
    x ∈ Rset X ∧ mS X x ≤ 1 ∧
      (vR X x = 7 → fwdTarget X x ∈ nbδ X x ∧ fwdTarget X x ∈ Rset X ∧
        vR X (fwdTarget X x) ≤ 6) := by
  sorry

/-- Charge lands in `R` at points of weight `≤ 6`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits `recvI`).
Depends on: `recvI`, `dest_ok`. -/
theorem recvI_dest (hX : Normal X) (hL : bigD2 ≤ dist2 X)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) {y : Pt} {a : Pt → ℝ}
    (hr : SendRule (ShapeI X) X y a) {x : Pt} (hx : a x ≠ 0) :
    dest X x ∈ Rset X ∧ vR X (dest X x) ≤ 6 := by
  obtain ⟨hxR, hm, hf⟩ := recvI hX hL hτ hr hx
  exact dest_ok hxR hm fun h7 => (hf h7).2

/-- **lem:cone**: an immediate sender `s` of `d` is a neighbour of `d` within `≈ 61°` of the
upward vertical of a nearby frame (`⟨s − d, n⟩ ≥ 12/25 = cos 61.3°`; paper: all directions in
`[−60°, 60°]` up to the flat-model errors).

TODO: prove.
What's missing: paper proof of lem:cone.  Direct sender `y`, receiver `d` at slot angle `ψ`:
`y − d = −dirF n ψ`, `⟨y − d, n⟩ = −cos ψ`; per shape `ψ ∈ {σ(φ + 120°), σ(φ + 180°)}` with
`φ ∈ [−ηA, 30° + ηA]`, `180°` (A′, cap), `±120° + O(ηA)` (cap), `[ψ₁ + 60°, 300° − ψ₂]` with
`ψᵢ ≥ 60° − 2ηA` (Dt); all give `−cos ψ ≥ cos(60° + 2ηA) > 12/25`.  Forwarded: `s = x` a
forwarder of a sender `y` (`dist y d ≤ 2`), `d = 2x − k`, `s − d = k − x` at `|β| ≤ 30.02°`
(`recvI`, `flat_K` at `x`): `cos β > 0.86`.
Acceptance: no `sorry`.
Depends on: `recvI`, `flat_K`, `sendAmt_spec`, `shapeI_facts`, definitions. Difficulty M. -/
theorem coneI (hX : Normal X) (hL : bigD2 ≤ dist2 X)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) {s d : Pt} (h : ImmSender (ShapeI X) X s d) :
    s ∈ nbδ X d ∧ ∃ y n, FrameP X y n ∧ dist y d ≤ 2 ∧ 12 / 25 ≤ inner ℝ (s - d) n := by
  sorry

/-- **lem:Th** (band `|t − 1/2| < κ`): in any good′ frame near `d`, an immediate sender of `d`
within `≈ 3°` of `±60°` forces `depth d ≤ 1.06`, and one within `≈ 3°` of the vertical forces
`depth d ≥ 1.48`; so `d` never has both kinds.

TODO: prove.
What's missing: paper proof of lem:Th.  In this band the shapes are A, B, C_φ with
`φ ≤ 0.73°` (`|t − sin(30° − φ)| ≤ ηT`), A′, cap, Dt with `ψ₁ ≤ 60.73°`.  A sender near
`±60°` is C_φ, a cap, or a Dt with `|θ| ≥ 57°`; its depth is `≤ cos 59.27° + 10⁻⁴ < 0.512`, so
`depth d ≤ 0.512 + 0.54`.  A sender near `0°` is C_φ (depth of `d` `≥ √3 cos(30° − φ) ≥ 1.49`),
A′/cap (`3/2`), Dt with `|θ| ≤ 3.1°` (`≥ cos 60.73° + 0.9986 > 1.487`) or a forwarder (depth
`≥ 0.999 + 0.998`).  Frames of different good′ points within `3` agree up to `ε₀`
(`frameP_close`); intrinsic and frame depths agree up to `10⁻⁵`.
Acceptance: no `sorry`.
Depends on: `coneI`, `recvI`, `flat_K`, `flat_pin`, `frameP_close`, `frameP_outside`,
`FrameP.top`, definitions. Difficulty M–L. -/
theorem ThI (hX : Normal X) (hL : bigD2 ≤ dist2 X)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) (hTh : |tgap X - 1 / 2| < κP) {s d : Pt}
    (h : ImmSender (ShapeI X) X s d) {y n : Pt} (hF : FrameP X y n) (hyd : dist y d ≤ 3) :
    (|inner ℝ (s - d) n - 1 / 2| ≤ 1 / 25 → depth X d ≤ 106 / 100) ∧
      (9986 / 10000 ≤ inner ℝ (s - d) n → 148 / 100 ≤ depth X d) := by
  sorry

/-- **lem:loads**: every point of `R` receives at most one unit in total (directly or through
forwarders).

TODO: prove.
What's missing: paper proof of lem:loads, bands L (`t ≤ 1/2 − κ`: shapes A, B, C_φ with
`φ ≥ 0.6°`, no forwarding; sender directions in `[−59.4°, 59.4°]`, at most two senders of
`1/2`), H (`1/2 + κ ≤ t ≤ t_I` or `1 < t ≤ 1 + 2δ₀`: A, B, Dt with `ψ₁ ≥ 60.5°`; a forwarder
has one Dt sender, passes `1/2`), T (`t > 1 + 2δ₀`: only A, senders at `±30°`), Th (`lem:Th`:
never three immediate senders; a sender giving `1` is alone).  Write the load of `d` as the sum
over immediate senders (`ImmSender`) of what they pass; immediate senders are distinct
neighbours of `d` (`coneI`), pairwise `≥ 60°` apart, inside the cone of `coneI`
(`≤ 3`, and `3` only near `−60°, 0°, 60°`).
Acceptance: no `sorry`.
Depends on: `recvI`, `coneI`, `ThI`, `frameP_close`, `sendAmt_spec`, `shapeI_facts`,
`flat_pin`, definitions. Difficulty XL. -/
theorem loadI (hX : Normal X) (hL : bigD2 ≤ dist2 X)
    (hτ : tau X ≤ √3 / 2 - 2 * beta ∨ 1 < tau X) :
    ∀ d ∈ Rset X, ∑ y ∈ Rset X, Tr (ShapeI X) X y d ≤ 1 := by
  sorry

end

end Erdos132Main

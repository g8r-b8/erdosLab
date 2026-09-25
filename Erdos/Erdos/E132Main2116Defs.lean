import Erdos.E132Main43

/-!
# Erdős Problem 132, Theorem 1(b) (`21/16`) — definitions, charging lemma, LP, small cases

Paper `problems/132/paper/paper.tex` §10 (`sec:P4`, Theorem P4: average weight `7` in Region I
and for `τ > 1`) and §11 (`sec:II`: Theorem IIe `e(S) ≤ s + p/2 + C` and Theorem IIw average
weight `7` in Region II with `τ ≤ 1`).  Target:

```
  theorem erdos132_main2116 : ∃ C₁ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      (tauInv X ≤ √3/2 - 1/50 ∨ √3/2 + 3/100 ≤ tauInv X) →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 21/16 * X.card + C₁
```

Everything of the `54/37`, `15/11` and `4/3` developments is reused unchanged (this file imports
`E132Main43`).  This file adds

* `tauInv` (the scale-invariant `τ(X)` of the paper's introduction), `Q2` (all points of `S` of
  `Δ₂`-degree `1`, the paper's `Q`), the constants of §§10–11;
* goodness at scale `Λ = 10⁹`, `ε₀ = 10⁻⁶` (`IsGoodP`), the exceptional set `EP`, the local
  frame `FrameP` (radius-10 normals, far points at abscissa `±(Λ − 1)`);
* the **heavy shapes** of the classifications (`TwoShape` = types A, B, C_φ; `APShape` = A′;
  `CapShapeP`; `DtShape` = Dt and Dt_II) with their **charge vectors** (`twoAmt`, …);
* the **discharging** in *merged* form: a sender `y` sends `sendAmt Shape X y x` to each
  receiver `x`; a receiver of weight `7` (a *forwarder*) passes it on to its target
  `fwdTarget X x = 2x − k` (`k` its unique `S`-neighbour), so the charge lands at
  `dest X x`; `Tr Shape X y d` is the total charge from `y` landing at `d`;
* the combinatorial **charging lemma** `charge7` and its instance `weight7_of_rules` (proved);
* the LP with weights `5/8, 3/8` (`lp2116`), the normalisation keeping `tauInv`, the small-case
  packing bound, and the constants (all proved).

Plan, deviations and DAG: `problems/132/lean/MAIN2116_PLAN.md`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## `τ(X)` and `Q` -/

/-- The scale-invariant `τ(X) = (Δ² − Δ₂² − δ²)/(2Δ₂δ)` (paper, introduction). -/
def tauInv (X : Finset Pt) : ℝ :=
  (diam X ^ 2 - dist2 X ^ 2 - minDist X ^ 2) / (2 * dist2 X * minDist X)

/-- `Q`: **all** points of `S` of `Δ₂`-degree exactly `1` (paper §2, used by lem:VSQ and
lem:IIlp; `p = |Q|`). -/
def Q2 (X : Finset Pt) : Finset Pt := (Sset X).filter (fun v => deg2 X v = 1)

/-! ## Constants (§10) -/

/-- The large-`Δ₂` threshold of §10: `Δ₂ ≥ 2·10¹⁵`. -/
def bigD2 : ℝ := 2 * 10 ^ 15

/-- `ε₀ = 10⁻⁶` (bound on `‖ν − ν′‖` for unit normals). -/
def ε₀P : ℝ := 1 / 10 ^ 6

/-- `Λ = 10⁹`. -/
def LamP : ℝ := 10 ^ 9

/-- Slope bound `ε = 2·10⁻⁶ ≥ tan ε₀`-type bound (generous). -/
def εP : ℝ := 2 / 10 ^ 6

/-- `δ₀ = 10⁻⁴` (level error of the flat model). -/
def δ₀P : ℝ := 1 / 10 ^ 4

/-- `κ = 10⁻²` (width of band Th). -/
def κP : ℝ := 1 / 100

/-- Tolerance for angles in the shapes (radians). -/
def ηA : ℝ := 1 / 1000

/-- Tolerance for pinned values of `t` in the shapes. -/
def ηT : ℝ := 1 / 1000

/-- DN slope at scale `Λ`: `(1011 + 7)/(10⁹ − 7) < 2·10⁻⁶`. -/
def κD : ℝ := 2 / 10 ^ 6

/-- Thin-case bound on `|X ∖ D|` at scale `Λ` (box `≈ 3.2·10¹¹ × 6.6·10⁹`). -/
def cThinP : ℝ := 10 ^ 23

/-- Bound on the number of non-good points of weight `≥ 8`:
`2π·10⁶·(6·10¹¹ + 1)² + cThinP < 10³²` (paper: `N′_g = 2.6·10²⁵`). -/
def cEP : ℝ := 10 ^ 32

/-- Additive constant of `e(S) ≤ s + p/2 + C` in Region II (`cBad + 1200 (mixed) + 2 + 17 + …`). -/
def cIIe : ℝ := cBad + 1300

/-- Additive constant of Theorem 1(b) (paper: `2·10³²`). -/
def C2116 : ℝ := 10 ^ 33

/-! ## Goodness at scale `Λ`, exceptions, frames -/

/-- **Good′** (Euclidean-local form of §10 "good′"): all unit outer normals of `K` at boundary
points within distance `Λ = 10⁹` of `y` lie pairwise within `ε₀ = 10⁻⁶` (in norm). -/
def IsGoodP (X : Finset Pt) (y : Pt) : Prop :=
  ∀ b₁ ∈ frontier (KBall X), ∀ b₂ ∈ frontier (KBall X), dist y b₁ ≤ LamP → dist y b₂ ≤ LamP →
    ∀ ν₁ ∈ normalCone (KBall X) b₁, ∀ ν₂ ∈ normalCone (KBall X) b₂, ‖ν₁‖ = 1 → ‖ν₂‖ = 1 →
      ‖ν₁ - ν₂‖ ≤ ε₀P

/-- Exceptions: points of `R` of weight `≥ 8` that are not good′ (`card_EP_le`: `≤ cEP`). -/
def EP (X : Finset Pt) : Finset Pt :=
  (Rset X).filter (fun y => 8 ≤ vR X y ∧ ¬ IsGoodP X y)

/-- **Local frame at scale `Λ`** (paper lem:frame with `ε₀ = 10⁻⁶`, `Λ = 10⁹`, Euclidean form as
`Frame43`): `n` is the unit outer normal at a nearest boundary point `p₀ = y + h n`
(`h = depth X y ∈ (0, 1]`), all unit normals at boundary points within distance `10` of `y`
are within `ε₀` of `n`, and `K` contains far points at abscissa `±(Λ − 1)` and height
`≥ h − 1011` (input of Lemma DN).  Heights `Z q = ⟨q − y, n⟩`, abscissae `⟨q − y, perp n⟩`;
the *level* of `q` is `Z q − h`. -/
structure FrameP (X : Finset Pt) (y n : Pt) : Prop where
  unit : ‖n‖ = 1
  mem_int : y ∈ interior (KBall X)
  depth_pos : 0 < depth X y
  depth_le : depth X y ≤ 1
  foot_mem : y + depth X y • n ∈ frontier (KBall X)
  foot_normal : n ∈ normalCone (KBall X) (y + depth X y • n)
  normals : ∀ b ∈ frontier (KBall X), dist y b ≤ 10 → ∀ ν ∈ normalCone (KBall X) b, ‖ν‖ = 1 →
    ‖ν - n‖ ≤ ε₀P
  far : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ g ∈ KBall X,
    inner ℝ (g - y) (perp n) = σ * (LamP - 1) ∧ depth X y - 1011 ≤ inner ℝ (g - y) n

/-! ## Heavy shapes (outputs of the classifications lem:classP4, lem:IIclass) -/

/-- The `k`-th slot of a hexagon of neighbours with base angle `θ₀` and orientation `σ`. -/
def hexPt (y n : Pt) (θ₀ σ : ℝ) (k : ℕ) : Pt := y + dirF n (θ₀ + σ * (k * (π / 3)))

/-- `deg y = 6` and the neighbours are the exact regular hexagon `hexPt y n θ₀ σ k`, `k < 6`. -/
def IsHexNb (X : Finset Pt) (y n : Pt) (θ₀ σ : ℝ) : Prop :=
  degδ X y = 6 ∧ ∀ k : ℕ, k < 6 → hexPt y n θ₀ σ k ∈ nbδ X y

/-- **Types A, B, C_φ** (lem:classP4; type A of lem:IIclass): weight `(6, 2)`, the two
neighbours in `S` are adjacent slots `0` (at `σφ`, `φ ∈ [0, 30°]` up to `ηA`) and `5`
(at `σ(φ − 60°)`).  A: both K-row; B: both D; C_φ: slot 0 in `D`, slot 5 K-row, and then
`t = sin(30° − φ)` (pinning).  Receivers: slots 2, 3 (`σ(φ + 120°)`, `σ(φ + 180°)`). -/
def TwoShape (X : Finset Pt) (y n : Pt) (σ φ : ℝ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ -ηA ≤ φ ∧ φ ≤ π / 6 + ηA ∧ IsHexNb X y n (σ * φ) σ ∧ mS X y = 2 ∧
    hexPt y n (σ * φ) σ 0 ∈ Sset X ∧ hexPt y n (σ * φ) σ 5 ∈ Sset X ∧
    (hexPt y n (σ * φ) σ 0 ∈ Dset X → hexPt y n (σ * φ) σ 5 ∉ Dset X →
      |tgap X - Real.sin (π / 6 - φ)| ≤ ηT)

/-- **Type A′** (lem:classP4): weight `(6, 2)`, hexagon with base `φ ≈ 0`; slot 0 (`0°`) is a
D-neighbour in `R`, slots 1, 5 (`±60°`) are in `S`; `t = 1/2`.  Receiver: slot 3 (`180°`). -/
def APShape (X : Finset Pt) (y n : Pt) (φ : ℝ) : Prop :=
  |φ| ≤ ηA ∧ IsHexNb X y n φ 1 ∧ mS X y = 2 ∧
    hexPt y n φ 1 0 ∈ Dset X ∧ hexPt y n φ 1 0 ∉ Sset X ∧
    hexPt y n φ 1 1 ∈ Sset X ∧ hexPt y n φ 1 5 ∈ Sset X ∧ |tgap X - 1 / 2| ≤ ηT

/-- **Cap** (lem:classP4): weight `(6, 3)`, hexagon with base `φ ≈ 0`; slot 0 is a D-neighbour
in `S`, slots 1, 5 are K-row; `t = 1/2`.  Receivers: slot 3 (one unit), slots 2, 4 (half). -/
def CapShapeP (X : Finset Pt) (y n : Pt) (φ : ℝ) : Prop :=
  |φ| ≤ ηA ∧ IsHexNb X y n φ 1 ∧ mS X y = 3 ∧
    hexPt y n φ 1 0 ∈ Dset X ∧ hexPt y n φ 1 0 ∈ Sset X ∧
    hexPt y n φ 1 1 ∈ Sset X ∧ hexPt y n φ 1 1 ∉ Dset X ∧
    hexPt y n φ 1 5 ∈ Sset X ∧ hexPt y n φ 1 5 ∉ Dset X ∧ |tgap X - 1 / 2| ≤ ηT

/-- The `S`-neighbours of lem:S3(c): K-row neighbours at `ψ₁ > 0` and `−ψ₂ < 0` (a mirror pair,
`60° ≤ ψ₁ ≤ 90°` up to `ηA`), a D-neighbour in `S` between them at least `60°` from both, and
`sin(ψ₁ − 30°) ≤ t ≤ 1 − cos ψ₁` up to `ηT` (pinning). -/
def KKDShape (X : Finset Pt) (y n : Pt) (ψ₁ ψ₂ : ℝ) : Prop :=
  mS X y = 3 ∧ π / 3 - ηA ≤ ψ₁ ∧ ψ₁ ≤ π / 2 + ηA ∧ |ψ₁ - ψ₂| ≤ ηA ∧
    y + dirF n ψ₁ ∈ nbδ X y ∧ y + dirF n ψ₁ ∈ Sset X ∧ y + dirF n ψ₁ ∉ Dset X ∧
    y + dirF n (-ψ₂) ∈ nbδ X y ∧ y + dirF n (-ψ₂) ∈ Sset X ∧ y + dirF n (-ψ₂) ∉ Dset X ∧
    (∃ ψD : ℝ, -ψ₂ + π / 3 ≤ ψD ∧ ψD ≤ ψ₁ - π / 3 ∧ y + dirF n ψD ∈ nbδ X y ∧
      y + dirF n ψD ∈ Sset X ∧ y + dirF n ψD ∈ Dset X) ∧
    Real.sin (ψ₁ - π / 6) - ηT ≤ tgap X ∧ tgap X ≤ 1 - Real.cos ψ₁ + ηT

/-- **Types Dt** (lem:classP4) and **Dt_II** (lem:IIclass): weight `(5, 3)`, the `S`-neighbours
as in `KKDShape`, and the two other neighbours `x₁ ≠ x₂` not in `S`, at angles in the lower arc
`I_y = [ψ₁ + 60°, 300° − ψ₂]`.  Receivers: `x₁`, `x₂` (half each). -/
def DtShape (X : Finset Pt) (y n : Pt) (ψ₁ ψ₂ : ℝ) (x₁ x₂ : Pt) : Prop :=
  degδ X y = 5 ∧ KKDShape X y n ψ₁ ψ₂ ∧ x₁ ≠ x₂ ∧
    x₁ ∈ nbδ X y ∧ x₂ ∈ nbδ X y ∧ x₁ ∉ Sset X ∧ x₂ ∉ Sset X ∧
    (∃ θ, ψ₁ + π / 3 ≤ θ ∧ θ ≤ 2 * π - ψ₂ - π / 3 ∧ x₁ = y + dirF n θ) ∧
    (∃ θ, ψ₁ + π / 3 ≤ θ ∧ θ ≤ 2 * π - ψ₂ - π / 3 ∧ x₂ = y + dirF n θ)

/-! ## Charge vectors -/

/-- A, B, C_φ: half a unit to slots 2 and 3. -/
def twoAmt (y n : Pt) (σ φ : ℝ) (x : Pt) : ℝ :=
  (if x = hexPt y n (σ * φ) σ 2 then 1 / 2 else 0) + (if x = hexPt y n (σ * φ) σ 3 then 1 / 2 else 0)

/-- A′: one unit to slot 3 (`180°`). -/
def apAmt (y n : Pt) (φ : ℝ) (x : Pt) : ℝ := if x = hexPt y n φ 1 3 then 1 else 0

/-- Cap: one unit to slot 3, half a unit to slots 2, 4 (`±120°`). -/
def capAmt (y n : Pt) (φ : ℝ) (x : Pt) : ℝ :=
  (if x = hexPt y n φ 1 3 then 1 else 0) + (if x = hexPt y n φ 1 2 then 1 / 2 else 0) +
    (if x = hexPt y n φ 1 4 then 1 / 2 else 0)

/-- Dt: half a unit to each of the two interior neighbours. -/
def dtAmt (x₁ x₂ : Pt) (x : Pt) : ℝ := (if x = x₁ then 1 / 2 else 0) + (if x = x₂ then 1 / 2 else 0)

/-- The discharging rules of §10 (Region I and `τ > 1`) in the frame `(y, n)`. -/
def ShapeI (X : Finset Pt) (y n : Pt) (a : Pt → ℝ) : Prop :=
  (∃ σ φ, TwoShape X y n σ φ ∧ a = twoAmt y n σ φ) ∨
    (∃ φ, APShape X y n φ ∧ a = apAmt y n φ) ∨
    (∃ φ, CapShapeP X y n φ ∧ a = capAmt y n φ) ∨
    (∃ ψ₁ ψ₂ x₁ x₂, DtShape X y n ψ₁ ψ₂ x₁ x₂ ∧ a = dtAmt x₁ x₂)

/-- The discharging rules of §11.2 (Region II, `τ ≤ 1`): type A (both `S`-neighbours K-row near
`±30°`) and type Dt_II. -/
def ShapeII (X : Finset Pt) (y n : Pt) (a : Pt → ℝ) : Prop :=
  (∃ σ φ, TwoShape X y n σ φ ∧ π / 6 - ηA ≤ φ ∧ hexPt y n (σ * φ) σ 0 ∉ Dset X ∧
      hexPt y n (σ * φ) σ 5 ∉ Dset X ∧ a = twoAmt y n σ φ) ∨
    (∃ ψ₁ ψ₂ x₁ x₂, DtShape X y n ψ₁ ψ₂ x₁ x₂ ∧ a = dtAmt x₁ x₂)

/-- `a` is an admissible charge vector of the sender `y` under the rules `Shape`: `y` is a
good′ point of `R` of weight `≥ 8`, `a ≥ 0` is supported on `δ`-neighbours of `y`, sends at
least the excess `v(y) − 7`, and has one of the shapes in some frame of `y`. -/
def SendRule (Shape : Pt → Pt → (Pt → ℝ) → Prop) (X : Finset Pt) (y : Pt) (a : Pt → ℝ) : Prop :=
  y ∈ Rset X ∧ IsGoodP X y ∧ 8 ≤ vR X y ∧ (∀ x, 0 ≤ a x) ∧ (∀ x, a x ≠ 0 → x ∈ nbδ X y) ∧
    ((vR X y : ℝ) - 7 ≤ ∑ x ∈ nbδ X y, a x) ∧ ∃ n, FrameP X y n ∧ Shape y n a

/-- The charge vector actually used for `y` (a chosen admissible one; `0` if there is none). -/
def sendAmt (Shape : Pt → Pt → (Pt → ℝ) → Prop) (X : Finset Pt) (y : Pt) : Pt → ℝ :=
  if h : ∃ a, SendRule Shape X y a then h.choose else fun _ => 0

/-- Target of a forwarder `x`: `2x − k` for the (chosen) `S`-neighbour `k` of `x`. -/
def fwdTarget (X : Finset Pt) (x : Pt) : Pt :=
  if h : ((nbδ X x).filter (· ∈ Sset X)).Nonempty then (2 : ℝ) • x - h.choose else x

/-- Where charge sent to `x` finally lands: forwarders (weight `7`) pass it to their target. -/
def dest (X : Finset Pt) (x : Pt) : Pt := if vR X x = 7 then fwdTarget X x else x

/-- Total charge from `y` landing at `d` (direct, or through a forwarder). -/
def Tr (Shape : Pt → Pt → (Pt → ℝ) → Prop) (X : Finset Pt) (y d : Pt) : ℝ :=
  ∑ x ∈ (nbδ X y).filter (fun x => dest X x = d), sendAmt Shape X y x

/-- `s` is an **immediate sender** of `d` (paper's "senders of `x`"): a sender `y` giving
directly to `d` (`d` not a forwarder), or a forwarder `s` whose target is `d`. -/
def ImmSender (Shape : Pt → Pt → (Pt → ℝ) → Prop) (X : Finset Pt) (s d : Pt) : Prop :=
  ∃ y ∈ Rset X, (sendAmt Shape X y d ≠ 0 ∧ vR X d ≠ 7 ∧ s = y) ∨
    (∃ x, sendAmt Shape X y x ≠ 0 ∧ vR X x = 7 ∧ fwdTarget X x = d ∧ s = x)

/-! ## Facts about the charge vectors (proved) -/

/-- Sum of a two-point charge vector.

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem sum_two_pts {N : Finset Pt} {p q : Pt} (hp : p ∈ N) (hq : q ∈ N) (c c' : ℝ) :
    ∑ x ∈ N, ((if x = p then c else 0) + (if x = q then c' else 0)) = c + c' := by
  rw [sum_add_distrib, sum_ite_eq', sum_ite_eq', if_pos hp, if_pos hq]

/-- Sum of a three-point charge vector.

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem sum_three_pts {N : Finset Pt} {p q r : Pt} (hp : p ∈ N) (hq : q ∈ N) (hr : r ∈ N)
    (c c' c'' : ℝ) :
    ∑ x ∈ N, ((if x = p then c else 0) + (if x = q then c' else 0) + (if x = r then c'' else 0)) =
      c + c' + c'' := by
  rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', sum_ite_eq', if_pos hp,
    if_pos hq, if_pos hr]

/-- The shapes' charge vectors are admissible: nonnegative, supported on neighbours, and they
send at least the excess `v(y) − 7` (`v = 8` sends `1`; the cap, `v = 9`, sends `2`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions, `sum_two_pts`, `sum_three_pts`. Difficulty S. -/
theorem shapeI_facts {y n : Pt} {a : Pt → ℝ} (h : ShapeI X y n a) :
    (∀ x, 0 ≤ a x) ∧ (∀ x, a x ≠ 0 → x ∈ nbδ X y) ∧ ((vR X y : ℝ) - 7 ≤ ∑ x ∈ nbδ X y, a x) := by
  rcases h with ⟨σ, φ, hs, rfl⟩ | ⟨φ, hs, rfl⟩ | ⟨φ, hs, rfl⟩ | ⟨ψ₁, ψ₂, x₁, x₂, hs, rfl⟩
  · obtain ⟨-, -, -, ⟨hdeg, hhex⟩, hm, -⟩ := hs
    have h2 := hhex 2 (by norm_num)
    have h3 := hhex 3 (by norm_num)
    have hv : (vR X y : ℝ) = 8 := by
      unfold vR; rw [hdeg, hm]; norm_num
    refine ⟨fun x => ?_, fun x hx => ?_, ?_⟩
    · unfold twoAmt; split_ifs <;> norm_num
    · unfold twoAmt at hx
      by_cases e1 : x = hexPt y n (σ * φ) σ 2
      · rw [e1]; exact h2
      by_cases e2 : x = hexPt y n (σ * φ) σ 3
      · rw [e2]; exact h3
      rw [if_neg e1, if_neg e2] at hx; norm_num at hx
    · unfold twoAmt; rw [sum_two_pts h2 h3, hv]; norm_num
  · obtain ⟨-, ⟨hdeg, hhex⟩, hm, -⟩ := hs
    have h3 := hhex 3 (by norm_num)
    have hv : (vR X y : ℝ) = 8 := by
      unfold vR; rw [hdeg, hm]; norm_num
    refine ⟨fun x => ?_, fun x hx => ?_, ?_⟩
    · unfold apAmt; split_ifs <;> norm_num
    · unfold apAmt at hx
      split_ifs at hx with e1
      · rw [e1]; exact h3
      · norm_num at hx
    · unfold apAmt; rw [sum_ite_eq', if_pos h3, hv]; norm_num
  · obtain ⟨-, ⟨hdeg, hhex⟩, hm, -⟩ := hs
    have h2 := hhex 2 (by norm_num)
    have h3 := hhex 3 (by norm_num)
    have h4 := hhex 4 (by norm_num)
    have hv : (vR X y : ℝ) = 9 := by
      unfold vR; rw [hdeg, hm]; norm_num
    refine ⟨fun x => ?_, fun x hx => ?_, ?_⟩
    · unfold capAmt; split_ifs <;> norm_num
    · unfold capAmt at hx
      by_cases e1 : x = hexPt y n φ 1 3
      · rw [e1]; exact h3
      by_cases e2 : x = hexPt y n φ 1 2
      · rw [e2]; exact h2
      by_cases e3 : x = hexPt y n φ 1 4
      · rw [e3]; exact h4
      rw [if_neg e1, if_neg e2, if_neg e3] at hx; norm_num at hx
    · unfold capAmt; rw [sum_three_pts h3 h2 h4, hv]; norm_num
  · obtain ⟨hdeg, ⟨hm, -⟩, -, h1, h2, -⟩ := hs
    have hv : (vR X y : ℝ) = 8 := by
      unfold vR; rw [hdeg, hm]; norm_num
    refine ⟨fun x => ?_, fun x hx => ?_, ?_⟩
    · unfold dtAmt; split_ifs <;> norm_num
    · unfold dtAmt at hx
      by_cases e1 : x = x₁
      · rw [e1]; exact h1
      by_cases e2 : x = x₂
      · rw [e2]; exact h2
      rw [if_neg e1, if_neg e2] at hx; norm_num at hx
    · unfold dtAmt; rw [sum_two_pts h1 h2, hv]; norm_num

/-- `ShapeII ⊆ ShapeI` as rules (type A is a `TwoShape`, Dt_II is a `DtShape`).

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem shapeII_to_I {y n : Pt} {a : Pt → ℝ} (h : ShapeII X y n a) : ShapeI X y n a := by
  rcases h with ⟨σ, φ, hs, -, -, -, rfl⟩ | ⟨ψ₁, ψ₂, x₁, x₂, hs, rfl⟩
  · exact Or.inl ⟨σ, φ, hs, rfl⟩
  · exact Or.inr (Or.inr (Or.inr ⟨ψ₁, ψ₂, x₁, x₂, hs, rfl⟩))

/-- The chosen charge vector is admissible whenever it is nonzero somewhere.

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem sendAmt_spec {Shape : Pt → Pt → (Pt → ℝ) → Prop} {y x : Pt}
    (hx : sendAmt Shape X y x ≠ 0) : SendRule Shape X y (sendAmt Shape X y) := by
  unfold sendAmt at hx ⊢
  split_ifs with h
  · exact h.choose_spec
  · rw [dif_neg h] at hx; exact absurd rfl hx

/-- If an admissible charge vector exists, the chosen one is admissible.

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem sendAmt_spec' {Shape : Pt → Pt → (Pt → ℝ) → Prop} {y : Pt}
    (h : ∃ a, SendRule Shape X y a) : SendRule Shape X y (sendAmt Shape X y) := by
  unfold sendAmt
  rw [dif_pos h]
  exact h.choose_spec

/-- Chosen charges are nonnegative.

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem sendAmt_nonneg (Shape : Pt → Pt → (Pt → ℝ) → Prop) (y x : Pt) :
    0 ≤ sendAmt Shape X y x := by
  by_cases hx : sendAmt Shape X y x = 0
  · rw [hx]
  · exact (sendAmt_spec hx).2.2.2.1 x

/-- Where a receiver's charge lands, from the receiver facts (lem:recv2(b,c), lem:IIrecv):
`x ∈ R` has `m_x ≤ 1`, and if `v(x) = 7` its target is in `R` with weight `≤ 6`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `vR`, `degδ_le_six`. Difficulty S. -/
theorem dest_ok {x : Pt} (hxR : x ∈ Rset X) (hm : mS X x ≤ 1)
    (hfwd : vR X x = 7 → fwdTarget X x ∈ Rset X ∧ vR X (fwdTarget X x) ≤ 6) :
    dest X x ∈ Rset X ∧ vR X (dest X x) ≤ 6 := by
  unfold dest
  split_ifs with h7
  · exact hfwd h7
  · refine ⟨hxR, ?_⟩
    have := degδ_le_six X x
    unfold vR at h7 ⊢
    omega

/-! ## The charging lemma (combinatorial core of Theorems P4 and IIw) -/

/-- **Charging lemma, weight 7.**  Let `v ≤ 12` on `R`, `E ⊆ R`, and `T ≥ 0` a transfer of
charge inside `R` such that every `y ∈ R ∖ E` with `v y ≥ 8` sends at least `v y − 7`, only such
points send, charge lands only at points of weight `≤ 6`, and every point receives at most `1`.
Then `Σ_R v ≤ 7|R| + 5|E|`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S–M. -/
theorem charge7 {R E : Finset Pt} (v : Pt → ℕ) (T : Pt → Pt → ℝ)
    (hv : ∀ y ∈ R, v y ≤ 12) (hER : E ⊆ R) (hT0 : ∀ y x, 0 ≤ T y x)
    (hsend : ∀ y ∈ R \ E, 8 ≤ v y → (v y : ℝ) - 7 ≤ ∑ x ∈ R, T y x)
    (hsrc : ∀ y ∈ R, ∀ x ∈ R, 0 < T y x → y ∈ R \ E ∧ 8 ≤ v y)
    (hdest : ∀ y ∈ R, ∀ x ∈ R, 0 < T y x → v x ≤ 6)
    (hload : ∀ x ∈ R, ∑ y ∈ R, T y x ≤ 1) :
    ∑ y ∈ R, (v y : ℝ) ≤ 7 * R.card + 5 * E.card := by
  have hswap : ∑ x ∈ R, ∑ y ∈ R, T y x = ∑ y ∈ R, ∑ x ∈ R, T y x := Finset.sum_comm
  have key : ∀ x ∈ R, (v x : ℝ) + ∑ y ∈ R, T y x - ∑ x' ∈ R, T x x' ≤
      7 + (if x ∈ E then 5 else 0) := by
    intro x hx
    have hin0 : 0 ≤ ∑ y ∈ R, T y x := sum_nonneg fun y _ => hT0 y x
    have hout0 : 0 ≤ ∑ x' ∈ R, T x x' := sum_nonneg fun x' _ => hT0 x x'
    have hinl := hload x hx
    have hrecv : 0 < ∑ y ∈ R, T y x → v x ≤ 6 := by
      intro hpos
      by_contra hc
      have : ∑ y ∈ R, T y x ≤ 0 := sum_nonpos fun y hy => by
        by_contra hlt
        push Not at hlt
        exact hc (hdest y hy x hx hlt)
      linarith
    by_cases hs : x ∉ E ∧ 8 ≤ v x
    · have hsnd := hsend x (mem_sdiff.2 ⟨hx, hs.1⟩) hs.2
      have hnp : ¬ 0 < ∑ y ∈ R, T y x := fun h => by have := hrecv h; omega
      have hin : ∑ y ∈ R, T y x = 0 := le_antisymm (not_lt.1 hnp) hin0
      rw [hin]
      split_ifs <;> linarith
    · have hout : ∑ x' ∈ R, T x x' ≤ 0 := sum_nonpos fun x' hx' => by
        by_contra hlt
        push Not at hlt
        obtain ⟨h1, h2⟩ := hsrc x hx x' hx' hlt
        exact hs ⟨(mem_sdiff.1 h1).2, h2⟩
      rcases hin0.lt_or_eq with hpos | hzero
      · have h6 := hrecv hpos
        have : (v x : ℝ) ≤ 6 := by exact_mod_cast h6
        split_ifs <;> linarith
      · rw [← hzero]
        have h12 : (v x : ℝ) ≤ 12 := by exact_mod_cast hv x hx
        by_cases hE : x ∈ E
        · rw [if_pos hE]; linarith
        · rw [if_neg hE]
          have h7 : v x < 8 := by
            by_contra h8
            push Not at h8
            exact hs ⟨hE, h8⟩
          have : (v x : ℝ) ≤ 7 := by exact_mod_cast Nat.lt_succ_iff.1 h7
          linarith
  have hsum := sum_le_sum key
  have hE5 : ∑ x ∈ R, (if x ∈ E then (5 : ℝ) else 0) = 5 * E.card := by
    rw [sum_ite_mem, inter_eq_right.2 hER, sum_const, nsmul_eq_mul]; ring
  have e1 : ∑ x ∈ R, ((v x : ℝ) + ∑ y ∈ R, T y x - ∑ x' ∈ R, T x x') =
      ∑ x ∈ R, (v x : ℝ) + (∑ x ∈ R, ∑ y ∈ R, T y x) - ∑ x ∈ R, ∑ x' ∈ R, T x x' := by
    rw [sum_sub_distrib, sum_add_distrib]
  have e2 : ∑ x ∈ R, ((7 : ℝ) + if x ∈ E then 5 else 0) = 7 * R.card + 5 * E.card := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, hE5]; ring
  rw [e1, e2, hswap] at hsum
  linarith

/-- **Weight 7 from the rules** (the wiring of the proofs of Theorems P4 and IIw): if every
good′ point of weight `≥ 8` has an admissible charge vector (classification), the charge of
every admissible vector lands in `R` at points of weight `≤ 6` (receivers), and every point
receives at most `1` (loads), then `Σ_R v ≤ 7r + 5|EP|`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `charge7`, `sendAmt_spec`, `sendAmt_spec'`, `sendAmt_nonneg`, `vR_le_twelve`.
Difficulty M. -/
theorem weight7_of_rules (Shape : Pt → Pt → (Pt → ℝ) → Prop)
    (hclass : ∀ y ∈ Rset X, 8 ≤ vR X y → IsGoodP X y → ∃ a, SendRule Shape X y a)
    (hrecv : ∀ y a, SendRule Shape X y a → ∀ x, a x ≠ 0 →
      dest X x ∈ Rset X ∧ vR X (dest X x) ≤ 6)
    (hload : ∀ d ∈ Rset X, ∑ y ∈ Rset X, Tr Shape X y d ≤ 1) :
    ∑ y ∈ Rset X, (vR X y : ℝ) ≤ 7 * (Rset X).card + 5 * (EP X).card := by
  have hT0 : ∀ y d, 0 ≤ Tr Shape X y d := fun y d =>
    sum_nonneg fun x _ => sendAmt_nonneg Shape y x
  -- a positive transfer comes from a nonzero chosen charge
  have hpos : ∀ y d, 0 < Tr Shape X y d →
      ∃ x ∈ nbδ X y, dest X x = d ∧ sendAmt Shape X y x ≠ 0 := by
    intro y d h
    by_contra hc
    push Not at hc
    have : Tr Shape X y d ≤ 0 := sum_nonpos fun x hx => by
      obtain ⟨hxN, hxd⟩ := mem_filter.1 hx
      rw [hc x hxN hxd]
    linarith
  apply charge7 (vR X) (Tr Shape X) (fun y _ => vR_le_twelve X y) (filter_subset _ _) hT0
  · intro y hy h8
    obtain ⟨hyR, hyE⟩ := mem_sdiff.1 hy
    have hg : IsGoodP X y := by
      by_contra hng
      exact hyE (mem_filter.2 ⟨hyR, h8, hng⟩)
    have hrule := sendAmt_spec' (hclass y hyR h8 hg)
    set a := sendAmt Shape X y with ha
    obtain ⟨-, -, -, ha0, hsupp, hsum, -⟩ := id hrule
    set N' := (nbδ X y).filter (fun x => a x ≠ 0) with hN'
    have hmaps : ∀ x ∈ N', dest X x ∈ Rset X := fun x hx =>
      (hrecv y a hrule x (mem_filter.1 hx).2).1
    have hfib := Finset.sum_fiberwise_of_maps_to hmaps (f := a)
    have hN'sum : ∑ x ∈ N', a x = ∑ x ∈ nbδ X y, a x := by
      rw [hN', sum_filter_ne_zero]
    have hle : ∑ d ∈ Rset X, ∑ x ∈ N'.filter (fun x => dest X x = d), a x ≤
        ∑ d ∈ Rset X, Tr Shape X y d := by
      refine sum_le_sum fun d _ => ?_
      unfold Tr
      refine sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => ha0 x
      intro x hx
      obtain ⟨hx1, hx2⟩ := mem_filter.1 hx
      exact mem_filter.2 ⟨(mem_filter.1 hx1).1, hx2⟩
    rw [hfib, hN'sum] at hle
    linarith
  · intro y hy d hd h
    obtain ⟨x, -, -, hx⟩ := hpos y d h
    obtain ⟨hyR, hg, h8, -⟩ := sendAmt_spec hx
    refine ⟨mem_sdiff.2 ⟨hyR, fun hE => (mem_filter.1 hE).2.2 hg⟩, h8⟩
  · intro y hy d hd h
    obtain ⟨x, -, hxd, hx⟩ := hpos y d h
    have := (hrecv y _ (sendAmt_spec hx) x hx).2
    rw [hxd] at this
    exact this
  · exact hload

/-! ## The linear programme (weights `5/8, 3/8`, lem:lpavg(b), lem:IIlp) -/

/-- **LP with weights `5/8, 3/8`**: from `μ₂ ≤ p + (3/2)(s − p)`, `μ_δ ≤ e + (7/2)r + C₁`,
`e ≤ s + p/2 + C₂`, `p ≥ 0`: `min{μ₂, μ_δ} ≤ (21/16)(s + r) + (3/8)(C₁ + C₂)`.
(`(5/8)(3s/2 − p/2) + (3/8)(s + p/2 + 7r/2) = (21/16)(s + r) − p/8`.)

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp2116 {μ₂ μδ s r e p C₁ C₂ : ℝ} (hp : 0 ≤ p) (h₂ : μ₂ ≤ p + 3 / 2 * (s - p))
    (hδ : μδ ≤ e + 7 / 2 * r + C₁) (he : e ≤ s + 1 / 2 * p + C₂) :
    min μ₂ μδ ≤ 21 / 16 * (s + r) + 3 / 8 * (C₁ + C₂) := by
  have h1 := min_le_left μ₂ μδ
  have h2 := min_le_right μ₂ μδ
  nlinarith

/-- The constants fit (all cases of `main2116_normalized`).

TODO: none — proved.
Acceptance: no `sorry`. Difficulty S. -/
theorem consts2116 :
    3 / 8 * (5 / 2 * cEP + cIIe) ≤ C2116 ∧ 3 / 8 * (5 / 2 * cEP + (cBad + 100)) ≤ C2116 ∧
      3 * ((16 * 10 ^ 15 + 1 : ℝ) ^ 2) ≤ C2116 ∧ (9 : ℝ) ≤ C2116 ∧ (1 : ℝ) ≤ C2116 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [cEP, cIIe, cBad, C2116]

/-! ## `τ(X)`: normalisation -/

/-- `tauInv` agrees with `tau` (of `E132MainDefs`) after normalising `δ = 1`:
`t − (1 − t²)/(2Δ₂) = (Δ² − Δ₂² − 1)/(2Δ₂)` for `t = Δ − Δ₂`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem tauInv_eq_tau (h1 : minDist X = 1) (h2 : dist2 X ≠ 0) : tauInv X = tau X := by
  unfold tauInv tau tgap
  rw [h1]
  field_simp
  ring

/-- `tauInv` is invariant under dilation.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `diam_smul`, `dist2_smul`, `minDist_smul`. Difficulty S. -/
theorem tauInv_smul {c : ℝ} (hc : 0 < c) (X : Finset Pt) :
    tauInv (X.image (c • ·)) = tauInv X := by
  unfold tauInv
  rw [Defs.diam_smul hc, Defs.dist2_smul hc, Defs.minDist_smul hc,
    show (c * diam X) ^ 2 - (c * dist2 X) ^ 2 - (c * minDist X) ^ 2 =
      c ^ 2 * (diam X ^ 2 - dist2 X ^ 2 - minDist X ^ 2) by ring,
    show 2 * (c * dist2 X) * (c * minDist X) = c ^ 2 * (2 * dist2 X * minDist X) by ring,
    mul_div_mul_left _ _ (by positivity)]

/-- **Scaling** keeping `τ(X)`: every `X` with `≥ 2` points has a dilate `Y` with `δ(Y) = 1`,
the same `n`, `μ(Δ₂)`, `μ(δ)` and `τ`.

TODO: none — proved (as `exists_normalize`).
Acceptance: no `sorry`.
Depends on: `minDist_smul`, `dist2_smul`, `mult_smul`, `tauInv_smul`. Difficulty S. -/
theorem exists_normalize2116 (hX : 2 ≤ X.card) :
    ∃ Y : Finset Pt, Y.card = X.card ∧ minDist Y = 1 ∧
      mult Y (dist2 Y) = mult X (dist2 X) ∧ mult Y (minDist Y) = mult X (minDist X) ∧
      tauInv Y = tauInv X := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < X.card)
  have hne : (distSetS X).Nonempty := ⟨_, Erdos132Layer.dist_mem_distSetS ha hb hab⟩
  have hδ : 0 < minDist X := by
    rw [minDist, dite_eq_left hne]; exact Erdos132Layer.pos_of_mem_distSetS (min'_mem _ _)
  set c := (minDist X)⁻¹
  have hc : 0 < c := inv_pos.2 hδ
  refine ⟨X.image (c • ·), card_image_of_injective _ (smul_right_injective Pt hc.ne'), ?_, ?_,
    ?_, tauInv_smul hc X⟩
  · rw [Defs.minDist_smul hc, inv_mul_cancel₀ hδ.ne']
  · rw [Defs.dist2_smul hc, Defs.mult_smul hc]
  · rw [Defs.minDist_smul hc, Defs.mult_smul hc]

/-- **Small cases** (proof of Theorem 1(b) in §10): nondegenerate, `δ = 1`, `Δ₂ < 2·10¹⁵` ⇒
`Δ < 3.88·10¹⁵ ≤ 4·10¹⁵` and packing gives `n ≤ (16·10¹⁵ + 1)²`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `card_sep_ball_le`, `dist_le_diam`, `one_le_dist`. Difficulty S. -/
theorem card_le_of_small2116 (h1 : minDist X = 1) (h4 : 4 ≤ X.card)
    (hnd : diam X ≤ 1.94 * dist2 X) (hs : dist2 X < bigD2) :
    (X.card : ℝ) ≤ (16 * 10 ^ 15 + 1) ^ 2 := by
  obtain ⟨w, hw⟩ : X.Nonempty := card_pos.1 (by omega)
  have hD : diam X ≤ 4 * 10 ^ 15 := by unfold bigD2 at hs; linarith
  have h := card_sep_ball_le (P := X) (fun a ha b hb hab => one_le_dist h1 ha hb hab) w
    (4 * 10 ^ 15) (fun a ha => by
      have := dist_le_diam ha hw
      push_cast
      linarith)
  have h' : (X.card : ℝ) ≤ ((4 * (4 * 10 ^ 15 : ℕ) + 1) ^ 2 : ℕ) := by exact_mod_cast h
  push_cast at h'
  linarith

end

end Erdos132Main

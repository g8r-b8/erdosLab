import Erdos.E132MainRegions

/-!
# Erdős Problem 132, `15/11` theorem — definitions, the exact identity, the LP

Improves `erdos132_main` (`54/37`) to `min{μ(Δ₂), μ(δ)} ≤ (15/11)n + C₀`
(`problems/132/angle_R4.md`, §§2–5 and Appendix A).  Everything of the `54/37` development
(`E132MainDefs / Local / Regions / Degen`) is reused unchanged; this file adds

* `degδ`, `mS` (the `δ`-degree and the number `m_y` of `δ`-neighbours in `S`);
* the exact identity `2μ(δ) = 2e(S) + Σ_{y∈R} (deg y + m_y)` (Appendix A, (0.1));
* the new LP with weights `8/11, 3/11` (Appendix A, (0.2), `2c = 10`);
* the constants `cN1` (exceptions of Theorem N1) and `cReg` (additive constant of the new
  region bounds `e(S) ≤ |S| + |Q| + cReg`).

Plan and DAG: `problems/132/lean/MAIN15_PLAN.md`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Definitions -/

/-- `δ`-degree of `y` in `X`. -/
def degδ (X : Finset Pt) (y : Pt) : ℕ := (partners X (minDist X) y).card

/-- `m_y`: number of `δ`-neighbours of `y` that lie in `S`. -/
def mS (X : Finset Pt) (y : Pt) : ℕ := ((partners X (minDist X) y).filter (· ∈ Sset X)).card

/-- Exceptional count of Theorem N1 (at most `10⁷` points `y ∈ R` with `m_y > 4`).
(Paper: `< 7·10⁷`; the Euclidean-local formulation of `E132Main15N1` gives
`10⁴ + 8π·601² < 10⁷`.) -/
def cN1 : ℝ := 10 ^ 7

/-- Additive constant of the new region bounds `e(S) ≤ |S| + |Q| + cReg`. -/
def cReg : ℝ := 2 * cBad + 10 ^ 4

/-- K-vertices carrying **two** good rungs (`q₂` of §3 counts these). -/
def twoRungVerts (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (rungVerts X F).filter (fun v => ∃ z z', z ≠ z' ∧ IsRung F v z ∧ IsRung F v z' ∧
    s(v, z) ∈ rungs X F ∧ s(v, z') ∈ rungs X F)

/-- **Breaks** (§3.3): points of `S` without a *pure* right T-neighbour (`RowR`). -/
def breaks (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (Sset X).filter (fun p => ¬ ∃ q, RowR F p q)

/-- The **slot** `(p, σ)` (`σ = 1`: left, `σ = -1`: right) is not used by any T-edge. -/
def SlotFree (F : DirField X) (p : Pt) (σ : ℝ) : Prop :=
  ∀ q, s(p, q) ∈ tEdges X F → ¬ 0 < σ * det2 (F.u p) (q - p)

/-- Rotation by the angle `θ` (counterclockwise). -/
def rot (θ : ℝ) (x : Pt) : Pt :=
  !₂[Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1]

/-- `α₁ = 2 arcsin(1/(2Δ))`: angle subtended at the centre by a unit chord of `C(w, Δ)`. -/
def alpha1 (X : Finset Pt) : ℝ := 2 * Real.arcsin (1 / (2 * diam X))

/-- `α₂ = 2 arcsin(1/(2Δ₂))`: angle subtended at the centre by a unit chord of `C(w, Δ₂)`. -/
def alpha2 (X : Finset Pt) : ℝ := 2 * Real.arcsin (1 / (2 * dist2 X))

/-! ## Exact identity and elementary bounds -/

/-- `m_y ≤ deg_δ y`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem mS_le_degδ (X : Finset Pt) (y : Pt) : mS X y ≤ degδ X y :=
  card_filter_le _ _

/-- `deg_δ y ≤ 6` (kissing number).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `card_partners_minDist_le`. Difficulty S. -/
theorem degδ_le_six (X : Finset Pt) (y : Pt) : degδ X y ≤ 6 :=
  card_partners_minDist_le X y

/-- **Exact identity (0.1)**: `2μ(δ) = 2e(S) + Σ_{y ∈ R} (deg y + m_y)`.
(S–S pairs: `e(S)`; S–R pairs: `Σ m_y`; R–R pairs: `Σ (deg y − m_y)/2`.)

TODO: prove.
What's missing: double counting.  Write `2μ(δ) = Σ_{x∈X} deg x` (handshake, as in
`mult_le_add_sum`/`two_mul_card_le_of_deg_le`), split `X = S ⊔ R`, and
`Σ_{x∈S} deg x = 2e(S) + Σ_{y∈R} m_y` (a `δ`-neighbour of `x ∈ S` is in `S` or in `R`; the
S–R incidences counted from both sides).  Works for every `X` (for `minDist X = 0` all terms
vanish since `partners X 0 y = ∅`).
Acceptance: no `sorry`.
Depends on: definitions, `Defs.mult_eq_card`, `Defs.mem_pairsAt`. Difficulty M. -/
theorem mu_delta_identity (X : Finset Pt) :
    2 * mult X (minDist X) = 2 * eS X + ∑ y ∈ Rset X, (degδ X y + mS X y) := by
  sorry

/-! ## The linear programme (Appendix A (0.2), `2c = 10`) -/

/-- **LP with weights `8/11, 3/11`**: from `μ₂ ≤ p + (3/2)(s − p)`, `μ_δ ≤ e + 5r + C₁`,
`e ≤ s + p + C₂` and `p ≥ 0`:  `min{μ₂, μ_δ} ≤ (15/11)(s + r) + (3/11)(C₁ + C₂)`.
(`(8/11)(3s/2 − p/2) + (3/11)(s + p + 5r) = (15/11)(s + r) − p/11`.)

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp15 {μ₂ μδ s r e p C₁ C₂ : ℝ} (hp : 0 ≤ p) (h₂ : μ₂ ≤ p + 3 / 2 * (s - p))
    (hδ : μδ ≤ e + 5 * r + C₁) (he : e ≤ s + p + C₂) :
    min μ₂ μδ ≤ 15 / 11 * (s + r) + 3 / 11 * (C₁ + C₂) := by
  have h1 := min_le_left μ₂ μδ
  have h2 := min_le_right μ₂ μδ
  linarith

/-- The constants fit: `3N₀ + (3/11)(cN1 + cReg) + cReg ≤ C₀` (so the small cases and the region
constants are absorbed by the `C₀` of the `54/37` theorem).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem consts15 : 3 * N₀ + 3 / 11 * (cN1 + cReg) + cReg ≤ C₀ := by
  norm_num [N₀, cN1, cReg, cBad, C₀]

end

end Erdos132Main

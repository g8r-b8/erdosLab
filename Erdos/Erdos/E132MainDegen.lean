import Erdos.E132MainDefs

/-!
# Erdős Problem 132, `54/37` theorem — degenerate regime (§8)

`Δ > 1.94 Δ₂` and `n ≥ 4` ⇒ `μ(Δ₂) ≤ n + 1`.  Scale-invariant: no normalisation needed.

Steps: (1) no two disjoint diametral pairs; (2) the diameter graph is a star `{y} ∪ A`;
(3) `Δ₂`-pairs: none inside `B := X ∖ D`, at most one inside `A`, none between `y` and `A`, so
`μ(Δ₂) ≤ 1 + I` with `I` the `B–W` incidences, `W := {y} ∪ A`; (4) `I ≤ |B| + |W|`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- **[C10]** with `q = 1/1.94²`: `1 + 3q < 2`, `q < 2 − √3 = (2 sin 15°)²`, `q < 1/3`.

TODO: fill (Phase 2 leaf).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c10 :
    (1 : ℝ) + 3 * (1 / 1.94 ^ 2) < 2 ∧ (1 : ℝ) / 1.94 ^ 2 < 2 - √3 ∧ (1 : ℝ) / 1.94 ^ 2 < 1 / 3 := by
  sorry

/-- Cross-distance identity (Step 1): `Σ|a − b|² = |xx′|² + |zz′|² + 4|m − m′|²`
(written with `(x + x′) − (z + z′) = 2(m − m′)`).

TODO: fill (Phase 2 leaf: coordinates, `EuclideanSpace.dist_eq`).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem cross_dist_identity (x x' z z' : Pt) :
    dist x z ^ 2 + dist x z' ^ 2 + dist x' z ^ 2 + dist x' z' ^ 2 =
      dist x x' ^ 2 + dist z z' ^ 2 + dist (x + x') (z + z') ^ 2 := by
  sorry

/-- **Step 1**: no two disjoint diametral pairs when `Δ > 1.94Δ₂`.

TODO: prove.
What's missing: at least two cross distances equal `Δ` ([C10] + `cross_dist_identity`);
disjoint cross pairs ⇒ rhombus of side `Δ` with a diagonal `≥ √2Δ`; sharing a point ⇒
equilateral triangle and a distance in `[2Δ sin 15°, Δ)`, hence in `(Δ₂, Δ)`.
Acceptance: no `sorry`.
Depends on: `c10`, `cross_dist_identity`. Difficulty L. -/
theorem degen_step1 (hdeg : 1.94 * dist2 X < diam X) {x x' z z' : Pt} (hx : x ∈ X)
    (hx' : x' ∈ X) (hz : z ∈ X) (hz' : z' ∈ X) (h₁ : dist x x' = diam X)
    (h₂ : dist z z' = diam X) (hxz : x ≠ z) (hxz' : x ≠ z') (hx'z : x' ≠ z) (hx'z' : x' ≠ z') :
    False := by
  sorry

/-- **Step 2**: the diameter graph is a star with centre `y`.

TODO: prove.
What's missing: by Step 1 it is a star or a triangle; a triangle with a 4th point is impossible
(`Δ₂² < Δ²/3` = circumradius², [C10]).
Acceptance: no `sorry`.
Depends on: `degen_step1`, `c10`. Difficulty M. -/
theorem degen_star (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) :
    ∃ y ∈ X, ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y := by
  sorry

/-- `W := {y} ∪ Diam(y)` (the diametral points for a star centre `y`). -/
def Wset (X : Finset Pt) (y : Pt) : Finset Pt := insert y (partners X (diam X) y)

/-- `B := X ∖ W`. -/
def Bset (X : Finset Pt) (y : Pt) : Finset Pt := X \ Wset X y

/-- `I`: incidences `(b, w) ∈ B × W` with `|bw| = Δ₂`. -/
def incid (X : Finset Pt) (y : Pt) : ℕ :=
  ((Bset X y ×ˢ Wset X y).filter (fun bw => dist bw.1 bw.2 = dist2 X)).card

/-- **Step 3a**: no `Δ₂`-pair inside `B` (`diam K < Δ₂`: lens bounding box, [C10]).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `ball_polygon_a`-type facts, `c10`. Difficulty M. -/
theorem degen_B_no_pair (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt}
    (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    mult (Bset X y) (dist2 X) = 0 := by
  sorry

/-- **Step 3b**: at most one `Δ₂`-pair inside `A = Diam(y)` (the two extreme points of the arc).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `c10`, `degen_star`. Difficulty M. -/
theorem degen_A_le_one (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt}
    (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    mult (partners X (diam X) y) (dist2 X) ≤ 1 := by
  sorry

/-- **Step 3**: `μ(Δ₂) ≤ 1 + I`.

TODO: prove (split the `Δ₂`-pairs by where the endpoints lie; `y–A` pairs are at distance `Δ`).
Acceptance: no `sorry`.
Depends on: `degen_B_no_pair`, `degen_A_le_one`. Difficulty M. -/
theorem degen_step3 (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt} (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    mult X (dist2 X) ≤ 1 + incid X y := by
  sorry

/-- **Step 4 (incidence bound)** `I ≤ |B| + |W|`.

TODO: prove.
What's missing: each `J_w = C(w, Δ₂) ∩ K` is a single arc; no point is interior to two arcs
(internally tangent equal circles coincide); nondegenerate arcs are edges of `∂K`; injective
map `b ↦` following edge.
Acceptance: no `sorry`.
Depends on: circle geometry; `degen_B_no_pair`. Difficulty L–XL. -/
theorem degen_step4 (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt} (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    incid X y ≤ (Bset X y).card + (Wset X y).card := by
  sorry

/-- **§8 Degenerate regime**: `Δ > 1.94Δ₂`, `n ≥ 4` ⇒ `μ(Δ₂) ≤ n + 1`.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `degen_star`, `degen_step3`, `degen_step4`. -/
theorem degenerate (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) :
    (mult X (dist2 X) : ℝ) ≤ X.card + 1 := by
  obtain ⟨y, hy, hstar⟩ := degen_star h4 hdeg
  have h3 := degen_step3 h4 hdeg hy hstar
  have h4' := degen_step4 h4 hdeg hy hstar
  have hW : Wset X y ⊆ X := insert_subset hy (filter_subset _ _)
  have hc : (Bset X y).card + (Wset X y).card = X.card := card_sdiff_add_card_eq_card hW
  have : mult X (dist2 X) ≤ X.card + 1 := by omega
  exact_mod_cast this

end

end Erdos132Main

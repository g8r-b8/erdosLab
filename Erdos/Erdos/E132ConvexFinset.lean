import Erdos.E132Convex
import Mathlib.Analysis.Convex.Independent
import Mathlib.Data.Finset.Sym

/-!
# Erdős Problem 132, convex case: statements for finite point sets

`E132Convex.lean` proves the `n = 7, 11` results for an *ordered* strictly convex polygon
`p : Fin n → ℝ²` (every index-increasing triple positively oriented).  This file removes the
ordering: for a finite set `S ⊆ ℝ²` in convex position,

* convex position is Mathlib's `ConvexIndependent ℝ ((↑) : S → ℝ²)` (no point of `S` lies in the
  convex hull of the others);
* distances are counted over **unordered** pairs `{x, y} ⊆ S`, `x ≠ y` (as non-diagonal elements
  of `S.sym2`), and a distance `d` is *rare* if `1 ≤ #{pairs at distance d} ≤ #S`.

**Bridge** (`exists_strictConvexPolygon`).  Fix any `p₀ ∈ S`.  On `S \ {p₀}` the relation
`a ≺ b :⇔ 0 < orient p₀ a b` is a strict total order:
* total, because three distinct points of `S` are never collinear (the middle one would lie in
  the segment of the other two);
* transitive, because `a ≺ b ≺ c ⪯ a` would put `p₀` in the triangle `abc`.
Listing `p₀` followed by `S \ {p₀}` in `≺`-increasing order gives a strictly convex polygon: for
`a ≺ b ≺ c`, `orient a b c ≤ 0` would put `b` in the triangle `p₀ a c`.
-/

open Finset

namespace Erdos132Convex

/-! ## Convex-hull membership from coordinates -/

/-- A convex combination (given coordinatewise) of `A, B, C` lies in their convex hull. -/
theorem mem_hull3 {P A B C : Pt} {w0 w1 w2 : ℝ} (h0 : 0 ≤ w0) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2)
    (hs : w0 + w1 + w2 = 1) (hx : P 0 = w0 * A 0 + w1 * B 0 + w2 * C 0)
    (hy : P 1 = w0 * A 1 + w1 * B 1 + w2 * C 1) :
    P ∈ convexHull ℝ ({A, B, C} : Set Pt) := by
  sorry

/-- Barycentric coordinates: if `P` is on the inner side of all three sides of the positively
oriented triangle `ABC`, then `P ∈ conv{A, B, C}`. -/
theorem hull_of_orient {P A B C : Pt} (h1 : 0 ≤ orient P B C) (h2 : 0 ≤ orient A P C)
    (h3 : 0 ≤ orient A B P) (hD : 0 < orient A B C) :
    P ∈ convexHull ℝ ({A, B, C} : Set Pt) := by
  sorry

/-! ## Consequences of convex position -/

/-- Convex position, in the "not in the hull of the others" form. -/
def NotInHull (S : Finset Pt) : Prop := ∀ x ∈ S, x ∉ convexHull ℝ ((S : Set Pt) \ {x})

theorem notInHull_of_convexIndependent {S : Finset Pt}
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : NotInHull S := by
  sorry

/-- A point of `S` is not in the hull of three other points of `S`. -/
theorem not_mem_hull3 {S : Finset Pt} (hS : NotInHull S) {P A B C : Pt} (hP : P ∈ S)
    (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hPA : P ≠ A) (hPB : P ≠ B) (hPC : P ≠ C) :
    P ∉ convexHull ℝ ({A, B, C} : Set Pt) := by
  sorry

/-- No three distinct points of a convex-position set are collinear. -/
theorem orient_ne_zero {S : Finset Pt} (hS : NotInHull S) {x y z : Pt} (hx : x ∈ S)
    (hy : y ∈ S) (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    orient x y z ≠ 0 := by
  sorry

/-! ## The angular order around a vertex -/

/-- Transitivity of `a ≺ b :⇔ 0 < orient p₀ a b` on a convex-position set. -/
theorem orient_trans {S : Finset Pt} (hS : NotInHull S) {p₀ a b c : Pt} (h₀ : p₀ ∈ S)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (ha₀ : a ≠ p₀) (hb₀ : b ≠ p₀) (hc₀ : c ≠ p₀)
    (hab : 0 < orient p₀ a b) (hbc : 0 < orient p₀ b c) : 0 < orient p₀ a c := by
  sorry

/-- `≺`-increasing triples are positively oriented. -/
theorem orient_pos_of_lt {S : Finset Pt} (hS : NotInHull S) {p₀ a b c : Pt} (h₀ : p₀ ∈ S)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hb₀ : b ≠ p₀)
    (hab : 0 < orient p₀ a b) (hbc : 0 < orient p₀ b c) (hac : 0 < orient p₀ a c) :
    0 < orient a b c := by
  sorry

/-- **Bridge.** A finite set in convex position can be listed as a strictly convex polygon. -/
theorem exists_strictConvexPolygon {S : Finset Pt} (hS : NotInHull S) :
    ∃ (m : ℕ) (p : Fin m → Pt), Function.Injective p ∧ Set.range p = ↑S ∧
      StrictConvexPolygon p := by
  sorry

/-! ## Distances of a finite set -/

/-- The distance between the two points of an unordered pair. -/
noncomputable def pairDist (z : Sym2 Pt) : ℝ :=
  Sym2.lift ⟨fun x y => dist x y, fun x y => dist_comm x y⟩ z

/-- The unordered pairs `{x, y} ⊆ S` with `x ≠ y`. -/
noncomputable def pairsS (S : Finset Pt) : Finset (Sym2 Pt) := by
  classical exact S.sym2.filter (fun z => ¬ z.IsDiag)

/-- Number of unordered pairs of `S` at distance `d`. -/
noncomputable def multS (S : Finset Pt) (d : ℝ) : ℕ := by
  classical exact ((pairsS S).filter (fun z => pairDist z = d)).card

/-- The distances determined by `S`. -/
noncomputable def distSetS (S : Finset Pt) : Finset ℝ := by
  classical exact (pairsS S).image pairDist

/-- The rare distances of `S`: determined by `S` (so `≥ 1` pair) and by at most `#S` pairs. -/
noncomputable def rareDistsS (S : Finset Pt) : Finset ℝ := by
  classical exact (distSetS S).filter (fun d => multS S d ≤ S.card)

/-- For a listing `p` of `S`, the rare distances of `S` are those of `p`. -/
theorem rareDistsS_eq {S : Finset Pt} {n : ℕ} {p : Fin n → Pt} (hinj : Function.Injective p)
    (hrange : Set.range p = ↑S) : rareDistsS S = rareDists p := by
  sorry

/-- Main theorems for point sets: from the ordered version and the bridge. -/
theorem finset_of_polygon {n : ℕ} (h : ∀ p : Fin n → Pt, StrictConvexPolygon p →
    3 ≤ (rareDists p).card) {S : Finset Pt} (hn : S.card = n)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card := by
  sorry

/-- **Theorem 7 (point sets).** Seven points in convex position determine at least three
distances that each occur for at least one and at most 7 of the 21 pairs. -/
theorem erdos132_convex7_finset (S : Finset Pt) (hn : S.card = 7)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card :=
  finset_of_polygon erdos132_convex7 hn hS

/-- **Theorem 11 (point sets).** Eleven points in convex position determine at least three
distances that each occur for at least one and at most 11 of the 55 pairs. -/
theorem erdos132_convex11_finset (S : Finset Pt) (hn : S.card = 11)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card :=
  finset_of_polygon erdos132_convex11 hn hS

end Erdos132Convex

#print axioms Erdos132Convex.erdos132_convex7_finset
#print axioms Erdos132Convex.erdos132_convex11_finset

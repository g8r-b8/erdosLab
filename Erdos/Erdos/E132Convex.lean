import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import Std.Tactic.BVDecide

/-!
# Erdős Problem 132, convex case: `n = 7` and `n = 11`

A strictly convex `n`-gon `p : Fin n → ℝ²` (vertices listed in counter-clockwise order, every
triple `i < j < k` positively oriented) has at least three distances that each occur at most
`n` times among the `C(n,2)` vertex pairs.  This file proves it for `n = 7` and `n = 11`
(Theorems 7 and 11 of `problems/132/angle_B3.md`).

Proof architecture (see `problems/132/lean/README.md`):

1. **Geometry (Lemma Q).**  For `i < j < k < l` the diagonals of the convex quadrilateral meet
   at an interior point `O`, so `|ik| + |jl| > |ij| + |kl|` and `> |jk| + |il|`.
2. **Ordinal reduction.**  Colour each pair by the rank of its distance.  Lemma Q becomes the
   ordinal condition `QOrd`.  Lemma R (counting) bounds the number of distinct distances by `Dm`
   when at most two distances are rare.  `OrdNoCE n Dm` says: every `QOrd` colouring with
   colours `< Dm` has at least three rare colour classes.
3. **Certificate.**  `OrdNoCE n Dm` is reduced (with a Lean-proved encoding lemma) to a pure
   `BitVec` statement `BVNoCE`, discharged by `bv_decide`: CaDiCaL produces an LRAT proof and
   Lean's *verified* LRAT checker (`Std.Tactic.BVDecide`) checks it.  The only trusted step is
   the compiled evaluation of that checker, which `bv_decide` records as an auxiliary axiom
   `…._native.bv_decide.ax_…` stating `verifyBVExpr expr cert = true` (disclosed; this is the
   same trust base as `native_decide`).
-/

open Finset

namespace Erdos132Convex

/-! ## Geometry -/

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area of the triangle `abc` (positive iff counter-clockwise). -/
noncomputable def orient (a b c : Pt) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- `p` lists the vertices of a strictly convex polygon in counter-clockwise order:
every index-increasing triple is positively oriented. -/
def StrictConvexPolygon {n : ℕ} (p : Fin n → Pt) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → 0 < orient (p i) (p j) (p k)

/-- Coordinates of a point of the line through `a, b`. -/
theorem lineMap_apply' (a b : Pt) (u : ℝ) (i : Fin 2) :
    (AffineMap.lineMap a b u : Pt) i = a i + u * (b i - a i) := by
  rw [AffineMap.lineMap_apply]
  simp [vsub_eq_sub, vadd_eq_add]
  ring

/-- `orient` vanishes on a point of the line through `a, b`. -/
theorem orient_lineMap (a b : Pt) (u : ℝ) : orient a b (AffineMap.lineMap a b u) = 0 := by
  simp only [orient, lineMap_apply']; ring

/-- `orient x y ·` is affine along a segment. -/
theorem orient_lineMap_right (x y a c : Pt) (t : ℝ) :
    orient x y (AffineMap.lineMap a c t) = (1 - t) * orient x y a + t * orient x y c := by
  simp only [orient, lineMap_apply']; ring

/-- Strict triangle inequality when `o` is not on the line `ab` (detected by orientation). -/
theorem dist_lt_of_orient_ne {a b o : Pt} (h : orient a b o ≠ 0) :
    dist a b < dist a o + dist o b := by
  refine lt_of_le_of_ne (dist_triangle a o b) (fun he => h ?_)
  obtain ⟨u, -, hu⟩ := (dist_add_dist_eq_iff (a := a) (b := o) (c := b)).1 he.symm
  rw [← hu, orient_lineMap]

/-- A point of the segment `ab` splits `dist a b`. -/
theorem dist_lineMap_add (a b : Pt) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    dist a (AffineMap.lineMap a b t) + dist (AffineMap.lineMap a b t) b = dist a b :=
  (dist_add_dist_eq_iff).2 ⟨t, ⟨h0, h1⟩, rfl⟩

/-- **Quadrilateral inequality** for a positively oriented convex quadrilateral `ABCE`.
The diagonals meet at `O = lineMap A C t = lineMap B E s` with `0 < s, t < 1`, and `O` lies on
none of the four side lines. -/
theorem quad_ineq {A B C E : Pt} (h1 : 0 < orient A B C) (h2 : 0 < orient A B E)
    (h3 : 0 < orient A C E) (h4 : 0 < orient B C E) :
    dist A B + dist C E < dist A C + dist B E ∧ dist B C + dist A E < dist A C + dist B E := by
  set t := orient A B E / (orient A B E + orient B C E) with ht
  set s := orient A B C / (orient A B C + orient A C E) with hs
  have ht0 : 0 < t := div_pos h2 (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hs0 : 0 < s := div_pos h1 (by linarith)
  have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set O := AffineMap.lineMap A C t with hO
  have hO' : O = AffineMap.lineMap B E s := by
    have hsum : orient A B E + orient B C E = orient A B C + orient A C E := by
      simp only [orient]; ring
    ext i
    fin_cases i
    all_goals
      simp only [hO, lineMap_apply', ht, hs, Fin.zero_eta, Fin.mk_one]
      rw [hsum]
      field_simp
      simp only [orient]
      ring
  have eAC := dist_lineMap_add A C ht0.le ht1.le
  have eBE := dist_lineMap_add B E hs0.le hs1.le
  rw [← hO'] at eBE
  rw [← hO] at eAC
  have sAB : dist A B < dist A O + dist O B := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient A B A = 0 := by simp only [orient]; ring
    rw [this]; positivity)
  have sCE : dist C E < dist C O + dist O E := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient C E C = 0 := by simp only [orient]; ring
    have h' : orient C E A = orient A C E := by simp only [orient]; ring
    rw [this, h']
    have : 0 < 1 - t := by linarith
    positivity)
  have sBC : dist B C < dist B O + dist O C := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient B C C = 0 := by simp only [orient]; ring
    have h' : orient B C A = orient A B C := by simp only [orient]; ring
    rw [this, h']
    have : 0 < 1 - t := by linarith
    positivity)
  have sAE : dist A E < dist A O + dist O E := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient A E A = 0 := by simp only [orient]; ring
    have h' : orient A E C = - orient A C E := by simp only [orient]; ring
    rw [this, h']
    have : 0 < t * orient A C E := by positivity
    linarith)
  have d1 := dist_comm O B
  have d2 := dist_comm C O
  constructor <;> linarith

/-- **Lemma Q** for a strictly convex polygon. -/
theorem lemmaQ {n : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p) {i j k l : Fin n}
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    dist (p i) (p j) + dist (p k) (p l) < dist (p i) (p k) + dist (p j) (p l) ∧
    dist (p j) (p k) + dist (p i) (p l) < dist (p i) (p k) + dist (p j) (p l) :=
  quad_ineq (hp i j k hij hjk) (hp i j l hij (hjk.trans hkl)) (hp i k l (hij.trans hjk) hkl)
    (hp j k l hjk hkl)

/-! ## Distances, multiplicities, the target statement -/

/-- The vertex pairs `i < j`. -/
def pairsF (n : ℕ) : Finset (Fin n × Fin n) := univ.filter (fun e => e.1 < e.2)

/-- The set of distinct distances. -/
noncomputable def distSet {n : ℕ} (p : Fin n → Pt) : Finset ℝ :=
  (pairsF n).image (fun e => dist (p e.1) (p e.2))

/-- Multiplicity of the distance `d`: the number of pairs `i < j` at distance `d`. -/
noncomputable def mult {n : ℕ} (p : Fin n → Pt) (d : ℝ) : ℕ := by
  classical exact ((pairsF n).filter (fun e => dist (p e.1) (p e.2) = d)).card

/-- The *rare* distances: those occurring at most `n` times (and at least once). -/
noncomputable def rareDists {n : ℕ} (p : Fin n → Pt) : Finset ℝ := by
  classical exact (distSet p).filter (fun d => mult p d ≤ n)

/-! ## The ordinal model -/

/-- Ordinal quadrilateral condition for diagonal colours `a, b` and opposite-side colours
`s, t`: the diagonals are not dominated by the sides under either matching. -/
def Qc (a b s t : ℕ) : Prop := ¬ (a ≤ s ∧ b ≤ t) ∧ ¬ (a ≤ t ∧ b ≤ s)

/-- A colouring of the pairs `i < j` satisfies the ordinal Lemma Q. -/
def QOrd (n : ℕ) (c : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k l : Fin n, i < j → j < k → k < l →
    Qc (c i k) (c j l) (c i j) (c k l) ∧ Qc (c i k) (c j l) (c j k) (c i l)

/-- Size of colour class `t`. -/
def cnt (n : ℕ) (c : Fin n → Fin n → ℕ) (t : ℕ) : ℕ :=
  ((pairsF n).filter (fun e => c e.1 e.2 = t)).card

/-- **No `(n, ≤ Dm)` ordinal counterexample**: every `QOrd` colouring with colours `< Dm`
has at least three colours whose class size lies in `[1, n]`. -/
def OrdNoCE (n Dm : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → ℕ, (∀ i j : Fin n, i < j → c i j < Dm) → QOrd n c →
    3 ≤ ((range Dm).filter (fun t => 1 ≤ cnt n c t ∧ cnt n c t ≤ n)).card

/-- Rank of the distance of the pair `(i, j)` among all distinct distances. -/
noncomputable def rank {n : ℕ} (p : Fin n → Pt) (i j : Fin n) : ℕ :=
  ((distSet p).filter (· < dist (p i) (p j))).card

/-- Rank comparison is distance comparison.
TODO: / What's missing: strict monotonicity of `card (filter (· < x))` on a finset.
/ Acceptance: sorry-free. / Depends on: —. -/
theorem rank_le_iff {n : ℕ} (p : Fin n → Pt) (i j k l : Fin n) :
    rank p i j ≤ rank p k l ↔ dist (p i) (p j) ≤ dist (p k) (p l) := by
  sorry

/-- Ranks of pairs are `< #distSet`.
TODO: / Acceptance: sorry-free. / Depends on: —. -/
theorem rank_lt_card {n : ℕ} (p : Fin n → Pt) {i j : Fin n} (h : i < j) :
    rank p i j < (distSet p).card := by
  sorry

/-- The rank colouring of a strictly convex polygon satisfies the ordinal Lemma Q.
TODO: / Acceptance: sorry-free. / Depends on: `lemmaQ`, `rank_le_iff`. -/
theorem qord_rank {n : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p) : QOrd n (rank p) := by
  sorry

/-- The multiplicities sum to the number of pairs.
TODO: / Acceptance: sorry-free. / Depends on: `Finset.card_eq_sum_card_image`. -/
theorem sum_mult {n : ℕ} (p : Fin n → Pt) : ∑ d ∈ distSet p, mult p d = (pairsF n).card := by
  sorry

/-- **Lemma R**: with at most two rare distances, `(D - 2)(n + 1) ≤ #pairs`.
TODO: / Acceptance: sorry-free. / Depends on: `sum_mult`. -/
theorem lemmaR {n : ℕ} (p : Fin n → Pt) (h : (rareDists p).card ≤ 2) :
    ((distSet p).card - 2) * (n + 1) ≤ (pairsF n).card := by
  sorry

/-- Transfer: if `D ≤ Dm` and there is no ordinal counterexample, there are `≥ 3` rare distances.
TODO: / Acceptance: sorry-free. / Depends on: `qord_rank`, `rank_le_iff`, `rank_lt_card`. -/
theorem rare_of_ord {n Dm : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p)
    (hD : (distSet p).card ≤ Dm) (h : OrdNoCE n Dm) : 3 ≤ (rareDists p).card := by
  sorry

/-- Geometry + Lemma R + the ordinal statement give the theorem.
TODO: / Acceptance: sorry-free. / Depends on: `lemmaR`, `rare_of_ord`. -/
theorem main_of_ord {n Dm : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p)
    (hDm : (pairsF n).card < (Dm - 1) * (n + 1)) (h : OrdNoCE n Dm) :
    3 ≤ (rareDists p).card := by
  sorry

/-! ## The `BitVec` encoding

Colours are `BitVec 3`, class sizes `BitVec 8`, the number of rare classes `BitVec 4`.  The
pair / quadruple lists are explicit literals so that `simp` can unfold everything into a
quantifier-free `BitVec` formula for `bv_decide`. -/

/-- Size of colour class `t`, as an 8-bit sum over the list `L` of pairs. -/
def cntBV {n : ℕ} (L : List (Fin n × Fin n)) (x : Fin n → Fin n → BitVec 3) (t : BitVec 3) :
    BitVec 8 :=
  L.foldr (fun e acc => (if x e.1 e.2 = t then 1 else 0) + acc) 0

/-- Colour `t` is rare: class size in `[1, n]`. -/
def rareBV {n : ℕ} (L : List (Fin n × Fin n)) (x : Fin n → Fin n → BitVec 3) (t : BitVec 3) :
    Bool :=
  (cntBV L x t != 0) && decide (cntBV L x t ≤ BitVec.ofNat 8 n)

/-- Number of rare colours among `0, …, Dm - 1`. -/
def rareSumBV {n : ℕ} (L : List (Fin n × Fin n)) (x : Fin n → Fin n → BitVec 3) (Dm : ℕ) :
    BitVec 4 :=
  (List.range Dm).foldr (fun t acc => (if rareBV L x (BitVec.ofNat 3 t) = true then 1 else 0) + acc) 0

/-- Lemma Q (all four matchings) on one quadruple, `BitVec` version. -/
def QBV {n : ℕ} (x : Fin n → Fin n → BitVec 3) (q : Fin n × Fin n × Fin n × Fin n) : Prop :=
  ¬ (x q.1 q.2.2.1 ≤ x q.1 q.2.1 ∧ x q.2.1 q.2.2.2 ≤ x q.2.2.1 q.2.2.2) ∧
  ¬ (x q.1 q.2.2.1 ≤ x q.2.2.1 q.2.2.2 ∧ x q.2.1 q.2.2.2 ≤ x q.1 q.2.1) ∧
  ¬ (x q.1 q.2.2.1 ≤ x q.2.1 q.2.2.1 ∧ x q.2.1 q.2.2.2 ≤ x q.1 q.2.2.2) ∧
  ¬ (x q.1 q.2.2.1 ≤ x q.1 q.2.2.2 ∧ x q.2.1 q.2.2.2 ≤ x q.2.1 q.2.2.1)

/-- `BitVec` form of "no ordinal counterexample" for explicit pair / quadruple lists. -/
def BVNoCE (n Dm : ℕ) (L : List (Fin n × Fin n)) (Qs : List (Fin n × Fin n × Fin n × Fin n)) :
    Prop :=
  ∀ x : Fin n → Fin n → BitVec 3, (∀ e ∈ L, x e.1 e.2 < BitVec.ofNat 3 Dm) →
    (∀ q ∈ Qs, QBV x q) → rareSumBV L x Dm ≤ 2 → False

/-- **Encoding correctness**: the `BitVec` statement implies the ordinal one.
TODO: / What's missing: `toNat` of the fold sums = list counts = finset cards.
/ Acceptance: sorry-free. / Depends on: —. -/
theorem ordNoCE_of_bv {n Dm : ℕ} {L : List (Fin n × Fin n)}
    {Qs : List (Fin n × Fin n × Fin n × Fin n)}
    (hL : ∀ e, e ∈ L ↔ e.1 < e.2) (hnd : L.Nodup) (hlen : L.length < 256) (hn : n < 256)
    (hQ : ∀ q ∈ Qs, q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2)
    (hDm : Dm ≤ 8) (h : BVNoCE n Dm L Qs) : OrdNoCE n Dm := by
  sorry

/-! ## Explicit pair and quadruple lists (generated) -/

/-- The 21 pairs `i < j` of `Fin 7`, lexicographic. -/
def pairs7 : List (Fin 7 × Fin 7) :=
    [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6),
    (5, 6)]

/-- The 35 quadruples `i < j < k < l` of `Fin 7`, lexicographic. -/
def quads7 : List (Fin 7 × Fin 7 × Fin 7 × Fin 7) :=
    [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 2, 5), (0, 1, 2, 6), (0, 1, 3, 4), (0, 1, 3, 5),
    (0, 1, 3, 6), (0, 1, 4, 5), (0, 1, 4, 6), (0, 1, 5, 6), (0, 2, 3, 4), (0, 2, 3, 5),
    (0, 2, 3, 6), (0, 2, 4, 5), (0, 2, 4, 6), (0, 2, 5, 6), (0, 3, 4, 5), (0, 3, 4, 6),
    (0, 3, 5, 6), (0, 4, 5, 6), (1, 2, 3, 4), (1, 2, 3, 5), (1, 2, 3, 6), (1, 2, 4, 5),
    (1, 2, 4, 6), (1, 2, 5, 6), (1, 3, 4, 5), (1, 3, 4, 6), (1, 3, 5, 6), (1, 4, 5, 6),
    (2, 3, 4, 5), (2, 3, 4, 6), (2, 3, 5, 6), (2, 4, 5, 6), (3, 4, 5, 6)]

/-- The 55 pairs `i < j` of `Fin 11`, lexicographic. -/
def pairs11 : List (Fin 11 × Fin 11) :=
    [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 3),
    (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 4), (3, 5), (3, 6),
    (3, 7), (3, 8), (3, 9), (3, 10), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10),
    (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 7), (6, 8), (6, 9), (6, 10), (7, 8),
    (7, 9), (7, 10), (8, 9), (8, 10), (9, 10)]

/-- The 330 quadruples `i < j < k < l` of `Fin 11`, lexicographic. -/
def quads11 : List (Fin 11 × Fin 11 × Fin 11 × Fin 11) :=
    [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 2, 5), (0, 1, 2, 6), (0, 1, 2, 7), (0, 1, 2, 8),
    (0, 1, 2, 9), (0, 1, 2, 10), (0, 1, 3, 4), (0, 1, 3, 5), (0, 1, 3, 6), (0, 1, 3, 7),
    (0, 1, 3, 8), (0, 1, 3, 9), (0, 1, 3, 10), (0, 1, 4, 5), (0, 1, 4, 6), (0, 1, 4, 7),
    (0, 1, 4, 8), (0, 1, 4, 9), (0, 1, 4, 10), (0, 1, 5, 6), (0, 1, 5, 7), (0, 1, 5, 8),
    (0, 1, 5, 9), (0, 1, 5, 10), (0, 1, 6, 7), (0, 1, 6, 8), (0, 1, 6, 9), (0, 1, 6, 10),
    (0, 1, 7, 8), (0, 1, 7, 9), (0, 1, 7, 10), (0, 1, 8, 9), (0, 1, 8, 10), (0, 1, 9, 10),
    (0, 2, 3, 4), (0, 2, 3, 5), (0, 2, 3, 6), (0, 2, 3, 7), (0, 2, 3, 8), (0, 2, 3, 9),
    (0, 2, 3, 10), (0, 2, 4, 5), (0, 2, 4, 6), (0, 2, 4, 7), (0, 2, 4, 8), (0, 2, 4, 9),
    (0, 2, 4, 10), (0, 2, 5, 6), (0, 2, 5, 7), (0, 2, 5, 8), (0, 2, 5, 9), (0, 2, 5, 10),
    (0, 2, 6, 7), (0, 2, 6, 8), (0, 2, 6, 9), (0, 2, 6, 10), (0, 2, 7, 8), (0, 2, 7, 9),
    (0, 2, 7, 10), (0, 2, 8, 9), (0, 2, 8, 10), (0, 2, 9, 10), (0, 3, 4, 5), (0, 3, 4, 6),
    (0, 3, 4, 7), (0, 3, 4, 8), (0, 3, 4, 9), (0, 3, 4, 10), (0, 3, 5, 6), (0, 3, 5, 7),
    (0, 3, 5, 8), (0, 3, 5, 9), (0, 3, 5, 10), (0, 3, 6, 7), (0, 3, 6, 8), (0, 3, 6, 9),
    (0, 3, 6, 10), (0, 3, 7, 8), (0, 3, 7, 9), (0, 3, 7, 10), (0, 3, 8, 9), (0, 3, 8, 10),
    (0, 3, 9, 10), (0, 4, 5, 6), (0, 4, 5, 7), (0, 4, 5, 8), (0, 4, 5, 9), (0, 4, 5, 10),
    (0, 4, 6, 7), (0, 4, 6, 8), (0, 4, 6, 9), (0, 4, 6, 10), (0, 4, 7, 8), (0, 4, 7, 9),
    (0, 4, 7, 10), (0, 4, 8, 9), (0, 4, 8, 10), (0, 4, 9, 10), (0, 5, 6, 7), (0, 5, 6, 8),
    (0, 5, 6, 9), (0, 5, 6, 10), (0, 5, 7, 8), (0, 5, 7, 9), (0, 5, 7, 10), (0, 5, 8, 9),
    (0, 5, 8, 10), (0, 5, 9, 10), (0, 6, 7, 8), (0, 6, 7, 9), (0, 6, 7, 10), (0, 6, 8, 9),
    (0, 6, 8, 10), (0, 6, 9, 10), (0, 7, 8, 9), (0, 7, 8, 10), (0, 7, 9, 10), (0, 8, 9, 10),
    (1, 2, 3, 4), (1, 2, 3, 5), (1, 2, 3, 6), (1, 2, 3, 7), (1, 2, 3, 8), (1, 2, 3, 9),
    (1, 2, 3, 10), (1, 2, 4, 5), (1, 2, 4, 6), (1, 2, 4, 7), (1, 2, 4, 8), (1, 2, 4, 9),
    (1, 2, 4, 10), (1, 2, 5, 6), (1, 2, 5, 7), (1, 2, 5, 8), (1, 2, 5, 9), (1, 2, 5, 10),
    (1, 2, 6, 7), (1, 2, 6, 8), (1, 2, 6, 9), (1, 2, 6, 10), (1, 2, 7, 8), (1, 2, 7, 9),
    (1, 2, 7, 10), (1, 2, 8, 9), (1, 2, 8, 10), (1, 2, 9, 10), (1, 3, 4, 5), (1, 3, 4, 6),
    (1, 3, 4, 7), (1, 3, 4, 8), (1, 3, 4, 9), (1, 3, 4, 10), (1, 3, 5, 6), (1, 3, 5, 7),
    (1, 3, 5, 8), (1, 3, 5, 9), (1, 3, 5, 10), (1, 3, 6, 7), (1, 3, 6, 8), (1, 3, 6, 9),
    (1, 3, 6, 10), (1, 3, 7, 8), (1, 3, 7, 9), (1, 3, 7, 10), (1, 3, 8, 9), (1, 3, 8, 10),
    (1, 3, 9, 10), (1, 4, 5, 6), (1, 4, 5, 7), (1, 4, 5, 8), (1, 4, 5, 9), (1, 4, 5, 10),
    (1, 4, 6, 7), (1, 4, 6, 8), (1, 4, 6, 9), (1, 4, 6, 10), (1, 4, 7, 8), (1, 4, 7, 9),
    (1, 4, 7, 10), (1, 4, 8, 9), (1, 4, 8, 10), (1, 4, 9, 10), (1, 5, 6, 7), (1, 5, 6, 8),
    (1, 5, 6, 9), (1, 5, 6, 10), (1, 5, 7, 8), (1, 5, 7, 9), (1, 5, 7, 10), (1, 5, 8, 9),
    (1, 5, 8, 10), (1, 5, 9, 10), (1, 6, 7, 8), (1, 6, 7, 9), (1, 6, 7, 10), (1, 6, 8, 9),
    (1, 6, 8, 10), (1, 6, 9, 10), (1, 7, 8, 9), (1, 7, 8, 10), (1, 7, 9, 10), (1, 8, 9, 10),
    (2, 3, 4, 5), (2, 3, 4, 6), (2, 3, 4, 7), (2, 3, 4, 8), (2, 3, 4, 9), (2, 3, 4, 10),
    (2, 3, 5, 6), (2, 3, 5, 7), (2, 3, 5, 8), (2, 3, 5, 9), (2, 3, 5, 10), (2, 3, 6, 7),
    (2, 3, 6, 8), (2, 3, 6, 9), (2, 3, 6, 10), (2, 3, 7, 8), (2, 3, 7, 9), (2, 3, 7, 10),
    (2, 3, 8, 9), (2, 3, 8, 10), (2, 3, 9, 10), (2, 4, 5, 6), (2, 4, 5, 7), (2, 4, 5, 8),
    (2, 4, 5, 9), (2, 4, 5, 10), (2, 4, 6, 7), (2, 4, 6, 8), (2, 4, 6, 9), (2, 4, 6, 10),
    (2, 4, 7, 8), (2, 4, 7, 9), (2, 4, 7, 10), (2, 4, 8, 9), (2, 4, 8, 10), (2, 4, 9, 10),
    (2, 5, 6, 7), (2, 5, 6, 8), (2, 5, 6, 9), (2, 5, 6, 10), (2, 5, 7, 8), (2, 5, 7, 9),
    (2, 5, 7, 10), (2, 5, 8, 9), (2, 5, 8, 10), (2, 5, 9, 10), (2, 6, 7, 8), (2, 6, 7, 9),
    (2, 6, 7, 10), (2, 6, 8, 9), (2, 6, 8, 10), (2, 6, 9, 10), (2, 7, 8, 9), (2, 7, 8, 10),
    (2, 7, 9, 10), (2, 8, 9, 10), (3, 4, 5, 6), (3, 4, 5, 7), (3, 4, 5, 8), (3, 4, 5, 9),
    (3, 4, 5, 10), (3, 4, 6, 7), (3, 4, 6, 8), (3, 4, 6, 9), (3, 4, 6, 10), (3, 4, 7, 8),
    (3, 4, 7, 9), (3, 4, 7, 10), (3, 4, 8, 9), (3, 4, 8, 10), (3, 4, 9, 10), (3, 5, 6, 7),
    (3, 5, 6, 8), (3, 5, 6, 9), (3, 5, 6, 10), (3, 5, 7, 8), (3, 5, 7, 9), (3, 5, 7, 10),
    (3, 5, 8, 9), (3, 5, 8, 10), (3, 5, 9, 10), (3, 6, 7, 8), (3, 6, 7, 9), (3, 6, 7, 10),
    (3, 6, 8, 9), (3, 6, 8, 10), (3, 6, 9, 10), (3, 7, 8, 9), (3, 7, 8, 10), (3, 7, 9, 10),
    (3, 8, 9, 10), (4, 5, 6, 7), (4, 5, 6, 8), (4, 5, 6, 9), (4, 5, 6, 10), (4, 5, 7, 8),
    (4, 5, 7, 9), (4, 5, 7, 10), (4, 5, 8, 9), (4, 5, 8, 10), (4, 5, 9, 10), (4, 6, 7, 8),
    (4, 6, 7, 9), (4, 6, 7, 10), (4, 6, 8, 9), (4, 6, 8, 10), (4, 6, 9, 10), (4, 7, 8, 9),
    (4, 7, 8, 10), (4, 7, 9, 10), (4, 8, 9, 10), (5, 6, 7, 8), (5, 6, 7, 9), (5, 6, 7, 10),
    (5, 6, 8, 9), (5, 6, 8, 10), (5, 6, 9, 10), (5, 7, 8, 9), (5, 7, 8, 10), (5, 7, 9, 10),
    (5, 8, 9, 10), (6, 7, 8, 9), (6, 7, 8, 10), (6, 7, 9, 10), (6, 8, 9, 10), (7, 8, 9, 10)]


/-! ## The certificates (`bv_decide`) -/

/-- `n = 7`: no ordinal counterexample with `≤ 4` colours.
TODO: / What's missing: unfold with `simp`, then `bv_decide`. / Acceptance: sorry-free
(auxiliary `bv_decide` axiom allowed and disclosed). / Depends on: —. -/
theorem bvNoCE7 : BVNoCE 7 4 pairs7 quads7 := by
  sorry

/-- `n = 11`: no ordinal counterexample with `≤ 6` colours.
TODO: / What's missing: as for `bvNoCE7`. / Acceptance: as for `bvNoCE7`. / Depends on: —. -/
theorem bvNoCE11 : BVNoCE 11 6 pairs11 quads11 := by
  sorry

/-- TODO: / Depends on: `ordNoCE_of_bv`, `bvNoCE7`. -/
theorem ordNoCE7 : OrdNoCE 7 4 := by
  sorry

/-- TODO: / Depends on: `ordNoCE_of_bv`, `bvNoCE11`. -/
theorem ordNoCE11 : OrdNoCE 11 6 := by
  sorry

/-! ## Main theorems -/

/-- **Theorem 7.** A strictly convex 7-gon has at least three distances occurring at most 7
times.  TODO: / Depends on: `main_of_ord`, `ordNoCE7`. -/
theorem erdos132_convex7 (p : Fin 7 → Pt) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card := by
  sorry

/-- **Theorem 11.** A strictly convex 11-gon has at least three distances occurring at most 11
times.  TODO: / Depends on: `main_of_ord`, `ordNoCE11`. -/
theorem erdos132_convex11 (p : Fin 11 → Pt) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card := by
  sorry

end Erdos132Convex

#print axioms Erdos132Convex.erdos132_convex7
#print axioms Erdos132Convex.erdos132_convex11

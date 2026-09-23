import Erdos.E132ConvexFinset
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Erdős Problem 132: the layer bound (Theorem A, Corollary A1)

This file formalises `problems/132/paper/paper.tex`, section "A layer bound and a new class of
sets" (= `angle_C.md` Theorem A / Corollary A1, `VERIFY_A1b.md`, `VERIFY_A1c.md`).

For a finite set `X ⊆ ℝ²` let `Δ > Δ₂` be its two largest distances (`TwoLargest X Δ Δ₂`),
`L₁ = L1 X` the extreme points of `X`, `L₂ = L2 X` the extreme points of `X \ L₁`, `G` the
`Δ₂`-graph on `L₁ ∪ L₂` and `G′` its 2-core (`core`).  We prove

* (location) every `Δ₂`-pair has an endpoint in `L₁` and both in `L₁ ∪ L₂`; the endpoints of a
  `Δ`-pair are extreme; a non-extreme point has no `Δ`-partner;
* (Prop 3) every `q ∈ L₂ ∩ V(G′)` has `deg_{G′} q = 2`;
* (degree ≤ 4) every `p ∈ L₁ ∩ V(G′)` has `deg_{G′} p ≤ 4`;
* (Theorem A) `2 μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁′} (deg′ p − 2)`;
* (Corollary A1) if no point of `L₁` has 4 or more points at distance `Δ₂`, then
  `2 μ(Δ₂) ≤ 3|L₁| + 2|L₂|`; unconditionally
  `2 μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁} (min(h p, 4) − 2)`, hence `μ(Δ₂) ≤ 2|L₁| + |L₂|`.

## Design choices

* **Distances.**  `μ(d) = multS X d` (unordered pairs, from `E132ConvexFinset`).  Internally we
  work with squared distances `sqd` (polynomials in the coordinates).
* **The two largest distances** are given by the predicate `TwoLargest X Δ Δ₂` (`Δ` is the
  largest element of `distSetS X`, `Δ₂` the largest one below it); `exists_twoLargest` shows it
  is satisfiable as soon as `X` determines two distances.
* **Extreme points** (`IsExt`) are *exposed* points: some open half-plane bounded by a line
  through `p` contains `S \ {p}`.  For finite sets this is the same as `p ∉ conv(S \ {p})`
  (`isExt_iff_notMem_convexHull`, via Hahn–Banach), i.e. `L₁` is the vertex set of `conv X`.
* **The 2-core** `core V d` is the union of all `S ⊆ V` in which every vertex has at least two
  `d`-neighbours inside `S` (`MinDeg2`).  This is the largest such set, i.e. what repeated
  deletion of vertices of degree `< 2` leaves.  Instead of simulating the deletion process we
  prove its only consequence used here, `esum_le_core`: the (doubled) edge count drops by at most
  `2` per vertex outside the core.
* **Edges** are counted twice, as `esum V d = Σ_{v ∈ V} deg_V v` (handshake `two_mul_multS`).
* **Frames.**  The planar case analyses are done in the orthonormal frame `(fx q v ·, fy q v ·)`
  centred at `q` with first axis `v − q`, scaled so that `v ↦ (1,0)`; squared distances are
  divided by `sqd q v` (`frame_sqd`).  The core computations are lemmas about real numbers
  (suffix `_real`), closed by `nlinarith` / `linear_combination`.
-/

open Finset

namespace Erdos132Layer

open Erdos132Convex

/-! ## Squared distances, dot products and frames -/

/-- Squared Euclidean distance, in coordinates. -/
noncomputable def sqd (x y : Pt) : ℝ := (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2

/-- Dot product of `a − q` and `b − q`. -/
noncomputable def dotp (q a b : Pt) : ℝ := (a 0 - q 0) * (b 0 - q 0) + (a 1 - q 1) * (b 1 - q 1)

/-- TODO: prove.
What's missing: unfold `EuclideanSpace.dist_eq`, `Fin.sum_univ_two`, `Real.sq_sqrt`.
Acceptance: `dist x y ^ 2 = sqd x y`, no sorry.
Depends on: nothing. -/
theorem dist_sq_eq_sqd (x y : Pt) : dist x y ^ 2 = sqd x y := by
  sorry

/-- TODO: prove.
What's missing: both sides nonnegative, square both sides using `dist_sq_eq_sqd`.
Acceptance: `dist x y = r ↔ sqd x y = r ^ 2` for `0 ≤ r`.
Depends on: `dist_sq_eq_sqd`. -/
theorem dist_eq_iff_sqd {x y : Pt} {r : ℝ} (hr : 0 ≤ r) : dist x y = r ↔ sqd x y = r ^ 2 := by
  sorry

/-- TODO: prove.
What's missing: monotonicity of squaring on `[0, ∞)` (`pow_le_pow_left`, `abs_le_abs`).
Acceptance: `dist x y ≤ r ↔ sqd x y ≤ r ^ 2` for `0 ≤ r`.
Depends on: `dist_sq_eq_sqd`. -/
theorem dist_le_iff_sqd {x y : Pt} {r : ℝ} (hr : 0 ≤ r) : dist x y ≤ r ↔ sqd x y ≤ r ^ 2 := by
  sorry

/-- TODO: prove.
What's missing: `ring` after unfolding.
Acceptance: symmetry of `sqd`.
Depends on: nothing. -/
theorem sqd_comm (x y : Pt) : sqd x y = sqd y x := by
  sorry

/-- TODO: prove.
What's missing: if the sum of squares vanishes, both coordinates agree (`EuclideanSpace` ext).
Acceptance: `x ≠ y → 0 < sqd x y`.
Depends on: nothing. -/
theorem sqd_pos_of_ne {x y : Pt} (h : x ≠ y) : 0 < sqd x y := by
  sorry

/-- First frame coordinate of `P` in the frame at `q` with axis `v` (so `fx q v v = 1`). -/
noncomputable def fx (q v P : Pt) : ℝ := dotp q v P / sqd q v

/-- Second frame coordinate of `P` in the frame at `q` with axis `v` (counter-clockwise). -/
noncomputable def fy (q v P : Pt) : ℝ := orient q v P / sqd q v

/-- TODO: prove.
What's missing: Lagrange identity `(u·a)² + (u×a)² = |u|²|a|²` applied to `a = P − Q`;
`field_simp` then `ring`.
Acceptance: the frame is a similarity with squared ratio `1 / sqd q v`.
Depends on: `sqd_pos_of_ne`. -/
theorem frame_sqd {q v : Pt} (h : q ≠ v) (P Q : Pt) :
    (fx q v P - fx q v Q) ^ 2 + (fy q v P - fy q v Q) ^ 2 = sqd P Q / sqd q v := by
  sorry

/-- TODO: prove.
What's missing: unfold; `simp`.
Acceptance: `q` has frame coordinates `(0, 0)`.
Depends on: nothing. -/
theorem frame_base (q v : Pt) : fx q v q = 0 ∧ fy q v q = 0 := by
  sorry

/-- TODO: prove.
What's missing: `dotp q v v = sqd q v`, `orient q v v = 0`, `div_self`.
Acceptance: `v` has frame coordinates `(1, 0)`.
Depends on: `sqd_pos_of_ne`. -/
theorem frame_axis {q v : Pt} (h : q ≠ v) : fx q v v = 1 ∧ fy q v v = 0 := by
  sorry

/-- TODO: prove.
What's missing: 2D identity `(u·a)(u·b) + (u×a)(u×b) = |u|² (a·b)`.
Acceptance: frame coordinates preserve dot products (up to the factor `sqd q v`).
Depends on: `sqd_pos_of_ne`. -/
theorem frame_dot {q v : Pt} (h : q ≠ v) (P Q : Pt) :
    fx q v P * fx q v Q + fy q v P * fy q v Q = dotp q P Q / sqd q v := by
  sorry

/-- TODO: prove.
What's missing: 2D identity `(u·a)(u×b) − (u×a)(u·b) = |u|² (a×b)`.
Acceptance: frame coordinates preserve orientation (up to the factor `sqd q v`).
Depends on: `sqd_pos_of_ne`. -/
theorem frame_cross {q v : Pt} (h : q ≠ v) (P Q : Pt) :
    fx q v P * fy q v Q - fy q v P * fx q v Q = orient q P Q / sqd q v := by
  sorry

/-! ## The two largest distances -/

/-- `Δ` is the largest and `Δ₂` the second largest distance determined by `X`. -/
structure TwoLargest (X : Finset Pt) (Δ Δ₂ : ℝ) : Prop where
  mem_max : Δ ∈ distSetS X
  mem_snd : Δ₂ ∈ distSetS X
  snd_lt : Δ₂ < Δ
  le_max : ∀ d ∈ distSetS X, d ≤ Δ
  le_snd : ∀ d ∈ distSetS X, d < Δ → d ≤ Δ₂

/-- TODO: prove.
What's missing: `s(x, y) ∈ X.sym2`, not diagonal, `pairDist s(x,y) = dist x y`.
Acceptance: distances of distinct points of `X` lie in `distSetS X`.
Depends on: nothing. -/
theorem dist_mem_distSetS {X : Finset Pt} {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    dist x y ∈ distSetS X := by
  sorry

/-- TODO: prove.
What's missing: elements of `distSetS X` are distances of non-diagonal pairs, hence positive.
Acceptance: `0 < d` for `d ∈ distSetS X`.
Depends on: nothing. -/
theorem pos_of_mem_distSetS {X : Finset Pt} {d : ℝ} (hd : d ∈ distSetS X) : 0 < d := by
  sorry

/-- TODO: prove.
What's missing: `Δ := max' (distSetS X)`, `Δ₂ := max' ((distSetS X).erase Δ)`.
Acceptance: `TwoLargest` is satisfiable whenever `X` determines at least two distances.
Depends on: nothing. -/
theorem exists_twoLargest (X : Finset Pt) (h : 2 ≤ (distSetS X).card) :
    ∃ Δ Δ₂, TwoLargest X Δ Δ₂ := by
  sorry

namespace TwoLargest

variable {X : Finset Pt} {Δ Δ₂ : ℝ}

/-- TODO: prove.
What's missing: `pos_of_mem_distSetS mem_snd`.
Acceptance: `0 < Δ₂`.
Depends on: `pos_of_mem_distSetS`. -/
theorem pos (hT : TwoLargest X Δ Δ₂) : 0 < Δ₂ := by
  sorry

/-- TODO: prove.
What's missing: split `x = y` (distance `0`) / `x ≠ y` (`dist_mem_distSetS`, `le_max`).
Acceptance: all distances are at most `Δ`.
Depends on: `dist_mem_distSetS`, `pos`. -/
theorem dist_le (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    dist x y ≤ Δ := by
  sorry

/-- TODO: prove.
What's missing: split `x = y` / `x ≠ y`; `le_snd`.
Acceptance: no distance lies strictly between `Δ₂` and `Δ`.
Depends on: `dist_mem_distSetS`, `pos`. -/
theorem dist_gap (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    dist x y ≤ Δ₂ ∨ dist x y = Δ := by
  sorry

/-- TODO: prove.
What's missing: `dist_le` + `dist_le_iff_sqd`.
Acceptance: squared version of `dist_le`.
Depends on: `dist_le`, `dist_le_iff_sqd`. -/
theorem sqd_le (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    sqd x y ≤ Δ ^ 2 := by
  sorry

/-- TODO: prove.
What's missing: `dist_gap` + `dist_le_iff_sqd`, `dist_eq_iff_sqd`.
Acceptance: squared version of `dist_gap`.
Depends on: `dist_gap`. -/
theorem sqd_gap (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    sqd x y ≤ Δ₂ ^ 2 ∨ sqd x y = Δ ^ 2 := by
  sorry

end TwoLargest

/-! ## Extreme points and convex layers -/

/-- `p` is an extreme point of `S`: `p ∈ S` and some open half-plane bounded by a line through
`p` contains `S \ {p}`. -/
def IsExt (S : Finset Pt) (p : Pt) : Prop :=
  p ∈ S ∧ ∃ a b : ℝ, ∀ x ∈ S, x ≠ p → a * (x 0 - p 0) + b * (x 1 - p 1) < 0

/-- TODO: prove.
What's missing: (→) the half-plane is convex and misses `p`; (←) Hahn–Banach
(`geometric_hahn_banach_point_closed`) against the compact set `conv(S \ {p})`, then read off
the coefficients of the functional on the basis vectors.
Acceptance: `IsExt S p ↔ p ∉ convexHull ℝ (S \ {p})`, so `L1 X` is the vertex set of `conv X`.
Depends on: nothing (documentation of the definition; not used below). -/
theorem isExt_iff_notMem_convexHull {S : Finset Pt} {p : Pt} (hp : p ∈ S) :
    IsExt S p ↔ p ∉ convexHull ℝ ((S : Set Pt) \ {p}) := by
  sorry

/-- The first convex layer: the extreme points of `X`. -/
noncomputable def L1 (X : Finset Pt) : Finset Pt := by
  classical exact X.filter (IsExt X)

/-- The second convex layer: the extreme points of `X \ L₁`. -/
noncomputable def L2 (X : Finset Pt) : Finset Pt := by
  classical exact (X \ L1 X).filter (IsExt (X \ L1 X))

/-- TODO: prove.
What's missing: unfold `L1`, `mem_filter`, `IsExt` contains membership.
Acceptance: `p ∈ L1 X ↔ IsExt X p`.
Depends on: nothing. -/
theorem mem_L1 {X : Finset Pt} {p : Pt} : p ∈ L1 X ↔ IsExt X p := by
  sorry

/-- TODO: prove.
What's missing: unfold `L2`.
Acceptance: `p ∈ L2 X ↔ IsExt (X \ L1 X) p`.
Depends on: nothing. -/
theorem mem_L2 {X : Finset Pt} {p : Pt} : p ∈ L2 X ↔ IsExt (X \ L1 X) p := by
  sorry

/-- TODO: prove.
What's missing: from `mem_L1`, `mem_L2`.
Acceptance: `L1 X ⊆ X`, `L2 X ⊆ X`, `Disjoint (L1 X) (L2 X)`.
Depends on: `mem_L1`, `mem_L2`. -/
theorem L1_subset (X : Finset Pt) : L1 X ⊆ X := by
  sorry

/-- TODO: prove. (see `L1_subset`) -/
theorem L2_subset (X : Finset Pt) : L2 X ⊆ X := by
  sorry

/-- TODO: prove. (see `L1_subset`) -/
theorem disjoint_L1_L2 (X : Finset Pt) : Disjoint (L1 X) (L2 X) := by
  sorry

/-- TODO: prove.
What's missing: normal `u = q − c`; `2u·(x − q) = |x−c|² − |x−q|² − |q−c|² ≤ −|x−q|² < 0`.
Acceptance: a point of `S` on the boundary of a disc containing `S` is extreme.
Depends on: `sqd_pos_of_ne`. -/
theorem isExt_of_disk {S : Finset Pt} {c q : Pt} {R : ℝ} (hq : q ∈ S)
    (hS : ∀ x ∈ S, sqd c x ≤ R) (hR : sqd c q = R) : IsExt S q := by
  sorry

/-- TODO: prove.
What's missing: negate the definition of `IsExt` at the coefficients `(a, b)`.
Acceptance: a non-extreme point has another point of `S` in every closed half-plane at it.
Depends on: nothing. -/
theorem exists_of_not_isExt {S : Finset Pt} {q : Pt} (hq : q ∈ S) (h : ¬ IsExt S q) (a b : ℝ) :
    ∃ x ∈ S, x ≠ q ∧ 0 ≤ a * (x 0 - q 0) + b * (x 1 - q 1) := by
  sorry

/-! ## Location of `Δ`- and `Δ₂`-pairs (Lemma "location", obs. (1)–(2)) -/

/-- TODO: prove.
What's missing: `isExt_of_disk` with centre `q`, radius `Δ²`.
Acceptance: both endpoints of a `Δ`-pair are extreme (obs. (1)/(i)).
Depends on: `isExt_of_disk`, `TwoLargest.sqd_le`, `dist_eq_iff_sqd`. -/
theorem isExt_of_dist_max {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p q : Pt}
    (hp : p ∈ X) (hq : q ∈ X) (h : dist p q = Δ) : IsExt X p := by
  sorry

/-- TODO: prove.
What's missing: contrapositive of `isExt_of_dist_max` plus `dist_gap`.
Acceptance: a non-extreme point has no `Δ`-partner, so all of `X` is within `Δ₂` of it.
Depends on: `isExt_of_dist_max`, `TwoLargest.dist_gap`. -/
theorem dist_le_snd_of_not_isExt {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q x : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (hx : x ∈ X) : dist q x ≤ Δ₂ := by
  sorry

/-- TODO: prove.
What's missing: if `p ∉ L₁` then `X ⊆ D(p, Δ₂)` and `q` is extreme by `isExt_of_disk`.
Acceptance: every `Δ₂`-pair has an endpoint in `L₁` (obs. (2), first half).
Depends on: `dist_le_snd_of_not_isExt`, `isExt_of_disk`. -/
theorem mem_L1_or_of_dist_snd {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p q : Pt}
    (hp : p ∈ X) (hq : q ∈ X) (h : dist p q = Δ₂) : p ∈ L1 X ∨ q ∈ L1 X := by
  sorry

/-- TODO: prove.
What's missing: if `p ∉ L₁` then `q ∈ L₁` and every `x ∈ X \ L₁` is within `Δ₂` of `q`
(a `Δ`-partner would be extreme), so `p` is extreme in `X \ L₁` by `isExt_of_disk`.
Acceptance: every endpoint of a `Δ₂`-pair lies in `L₁ ∪ L₂` (obs. (2), second half).
Depends on: `mem_L1_or_of_dist_snd`, `isExt_of_dist_max`, `isExt_of_disk`. -/
theorem mem_L12_of_dist_snd {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p q : Pt}
    (hp : p ∈ X) (hq : q ∈ X) (h : dist p q = Δ₂) : p ∈ L1 X ∪ L2 X := by
  sorry

/-! ## Graphs, degrees and the 2-core -/

/-- The `d`-neighbours of `v` inside `V`. -/
noncomputable def nbr (V : Finset Pt) (d : ℝ) (v : Pt) : Finset Pt := by
  classical exact V.filter (fun x => dist v x = d)

/-- Twice the number of `d`-edges inside `V`: the degree sum. -/
noncomputable def esum (V : Finset Pt) (d : ℝ) : ℕ := ∑ v ∈ V, (nbr V d v).card

/-- Every vertex of `V` has at least two `d`-neighbours inside `V`. -/
def MinDeg2 (V : Finset Pt) (d : ℝ) : Prop := ∀ v ∈ V, 2 ≤ (nbr V d v).card

/-- The 2-core of the `d`-graph on `V`: the union of all subsets of minimum degree `≥ 2`. -/
noncomputable def core (V : Finset Pt) (d : ℝ) : Finset Pt := by
  classical exact (V.powerset.filter (fun S => MinDeg2 S d)).sup id

/-- TODO: prove.
What's missing: unfold `nbr`, `mem_filter`.
Acceptance: membership characterisation of `nbr`.
Depends on: nothing. -/
theorem mem_nbr {V : Finset Pt} {d : ℝ} {v x : Pt} : x ∈ nbr V d v ↔ x ∈ V ∧ dist v x = d := by
  sorry

/-- TODO: prove.
What's missing: `filter_subset_filter`.
Acceptance: `nbr` is monotone in the vertex set.
Depends on: `mem_nbr`. -/
theorem nbr_mono {V V' : Finset Pt} (h : V ⊆ V') (d : ℝ) (v : Pt) : nbr V d v ⊆ nbr V' d v := by
  sorry

/-- TODO: prove.
What's missing: `sup_le` over the powerset filter.
Acceptance: `core V d ⊆ V`.
Depends on: nothing. -/
theorem core_subset (V : Finset Pt) (d : ℝ) : core V d ⊆ V := by
  sorry

/-- TODO: prove.
What's missing: `le_sup` with `S ∈ V.powerset.filter _`.
Acceptance: every min-degree-2 subset of `V` lies in the core.
Depends on: nothing. -/
theorem subset_core {V S : Finset Pt} {d : ℝ} (hS : S ⊆ V) (h : MinDeg2 S d) :
    S ⊆ core V d := by
  sorry

/-- TODO: prove.
What's missing: `v ∈ core` lies in some min-degree-2 `S ⊆ core`; `nbr_mono`.
Acceptance: the core itself has minimum degree `≥ 2`.
Depends on: `nbr_mono`, `subset_core`. -/
theorem minDeg2_core (V : Finset Pt) (d : ℝ) : MinDeg2 (core V d) d := by
  sorry

/-- TODO: prove.
What's missing: expand both degree sums over `insert v V` with `sum_insert`; `v ∉ nbr · v`
because `d ≠ 0`; symmetry of `dist` turns the column `Σ_u [u ~ v]` into `deg v`.
Acceptance: adding a vertex adds twice its degree to `esum`.
Depends on: `mem_nbr`. -/
theorem esum_insert {V : Finset Pt} {d : ℝ} (hd : d ≠ 0) {v : Pt} (hv : v ∉ V) :
    esum (insert v V) d = esum V d + 2 * (nbr (insert v V) d v).card := by
  sorry

/-- TODO: prove.
What's missing: strong induction on `#V`: if `V ≠ core V`, some `v ∈ V \ core V` has
`deg_V v ≤ 1` (else `V` is min-degree-2, so `V ⊆ core V`); `core (V.erase v) = core V`;
apply `esum_insert`.
Acceptance: pruning to the 2-core loses at most one edge (two degree units) per deleted vertex.
Depends on: `esum_insert`, `core_subset`, `subset_core`, `minDeg2_core`. -/
theorem esum_le_core {d : ℝ} (hd : d ≠ 0) (V : Finset Pt) :
    esum V d ≤ esum (core V d) d + 2 * (V \ core V d).card := by
  sorry

/-- TODO: prove.
What's missing: double counting: the ordered pairs at distance `d` map 2-to-1 onto the
non-diagonal unordered pairs at distance `d` (`card_eq_sum_card_fiberwise`).
Acceptance: handshake lemma `2 μ(d) = esum X d`.
Depends on: `mem_nbr`. -/
theorem two_mul_multS {d : ℝ} (hd : 0 < d) (X : Finset Pt) : 2 * multS X d = esum X d := by
  sorry

/-- TODO: prove.
What's missing: vertices outside `L₁ ∪ L₂` have no `Δ₂`-neighbours and neighbours of vertices in
`L₁ ∪ L₂` lie in `L₁ ∪ L₂` (`mem_L12_of_dist_snd`).
Acceptance: the `Δ₂`-graph on `L₁ ∪ L₂` contains every `Δ₂`-pair.
Depends on: `mem_L12_of_dist_snd`, `mem_nbr`. -/
theorem esum_eq_esum_L12 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    esum X Δ₂ = esum (L1 X ∪ L2 X) Δ₂ := by
  sorry

/-! ## Planar lemmas in normalised coordinates -/

/-- TODO: prove.
What's missing: all three points satisfy `2 P·t = 1 + |t|² − D` and `(t × P)² = |t|² − (P·t)²`;
two of the three values `t × Pᵢ` coincide; a point is determined by `P·t` and `t × P`.
Acceptance: two distinct circles (centres `0` and `t ≠ 0`) meet in at most two points.
Depends on: nothing. -/
theorem circle3_real {x₁ y₁ x₂ y₂ x₃ y₃ tx ty D : ℝ} (ht : 0 < tx ^ 2 + ty ^ 2)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 = 1) (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (h₃ : x₃ ^ 2 + y₃ ^ 2 = 1)
    (d₁ : (x₁ - tx) ^ 2 + (y₁ - ty) ^ 2 = D) (d₂ : (x₂ - tx) ^ 2 + (y₂ - ty) ^ 2 = D)
    (d₃ : (x₃ - tx) ^ 2 + (y₃ - ty) ^ 2 = D) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = x₃ ∧ y₁ = y₃) ∨ (x₂ = x₃ ∧ y₂ = y₃) := by
  sorry

/-- TODO: prove.
What's missing: `|r − a|² − 1 = 2 x_r (1 − x_a) − 2 y_r y_a`, both terms `≥ 0`, not both zero.
Acceptance: Lemma M (opposite-side lemma) with `p = 0`, `b = (1, 0)`, `|pa| = |br| = 1`.
Depends on: nothing. -/
theorem lemmaM_real {xa ya xr yr : ℝ} (ha : xa ^ 2 + ya ^ 2 = 1) (hya : ya < 0)
    (hr : (xr - 1) ^ 2 + yr ^ 2 = 1) (hyr : 0 ≤ yr) (hr0 : 0 < xr ^ 2 + yr ^ 2) :
    1 < (xr - xa) ^ 2 + (yr - ya) ^ 2 := by
  sorry

/-- TODO: prove.
What's missing: identity `(A·W − A·B)(1 + W·B) = (W×B)(A×W + A×B)` for unit vectors, and
`1 + W·B > 0` because `W × B ≠ 0`.
Acceptance: chord monotonicity: if `W` and then `B` follow `A` counter-clockwise within a half-turn,
`|AB| > |AW|`.
Depends on: nothing. -/
theorem chord_real {a0 a1 w0 w1 b0 b1 : ℝ} (ha : a0 ^ 2 + a1 ^ 2 = 1) (hw : w0 ^ 2 + w1 ^ 2 = 1)
    (hb : b0 ^ 2 + b1 ^ 2 = 1) (haw : 0 < a0 * w1 - a1 * w0) (hab : 0 < a0 * b1 - a1 * b0)
    (hwb : 0 < w0 * b1 - w1 * b0) : a0 * b0 + a1 * b1 < a0 * w0 + a1 * w1 := by
  sorry

/-- TODO: prove.
What's missing: (VERIFY_A1b Case 3, `b = (1,0)` the middle neighbour, `t` in the closed half-plane
`x ≤ 0`, WLOG `y_t ≥ 0`): `t·c < 0` and `t·b ≤ 0` force `|tb|² = |tc|² = D`; then
`t ∥ −(b + c)` gives `t·a ≤ 0` (because `a·b + a·c ≥ 0`), so `|ta|² = D` too, and
`circle3_real` gives a contradiction.
Acceptance: Case 3 core computation.
Depends on: `circle3_real`. -/
theorem case3_real {xa ya xc yc xt yt D : ℝ} (hD : 1 < D)
    (ha : xa ^ 2 + ya ^ 2 = 1) (hc : xc ^ 2 + yc ^ 2 = 1)
    (hab : (xa - 1) ^ 2 + ya ^ 2 ≤ 1) (hcb : (xc - 1) ^ 2 + yc ^ 2 ≤ 1)
    (hya : 0 < ya) (hyc : yc < 0) (hxt : xt ≤ 0) (ht0 : 0 < xt ^ 2 + yt ^ 2) (hyt : 0 ≤ yt)
    (ga : (xt - xa) ^ 2 + (yt - ya) ^ 2 ≤ 1 ∨ (xt - xa) ^ 2 + (yt - ya) ^ 2 = D)
    (gb : (xt - 1) ^ 2 + yt ^ 2 ≤ 1 ∨ (xt - 1) ^ 2 + yt ^ 2 = D)
    (gc : (xt - xc) ^ 2 + (yt - yc) ^ 2 ≤ 1 ∨ (xt - xc) ^ 2 + (yt - yc) ^ 2 = D) : False := by
  sorry

/-- TODO: prove.
What's missing: reduce to `case3_real` by the reflection `y ↦ −y` and/or swapping `a ↔ c`.
Acceptance: Case 3 with `a, c` on opposite sides (`y_a y_c < 0`) and no sign condition on `y_t`.
Depends on: `case3_real`. -/
theorem case3_real' {xa ya xc yc xt yt D : ℝ} (hD : 1 < D)
    (ha : xa ^ 2 + ya ^ 2 = 1) (hc : xc ^ 2 + yc ^ 2 = 1)
    (hab : (xa - 1) ^ 2 + ya ^ 2 ≤ 1) (hcb : (xc - 1) ^ 2 + yc ^ 2 ≤ 1)
    (hopp : ya * yc < 0) (hxt : xt ≤ 0) (ht0 : 0 < xt ^ 2 + yt ^ 2)
    (ga : (xt - xa) ^ 2 + (yt - ya) ^ 2 ≤ 1 ∨ (xt - xa) ^ 2 + (yt - ya) ^ 2 = D)
    (gb : (xt - 1) ^ 2 + yt ^ 2 ≤ 1 ∨ (xt - 1) ^ 2 + yt ^ 2 = D)
    (gc : (xt - xc) ^ 2 + (yt - yc) ^ 2 ≤ 1 ∨ (xt - xc) ^ 2 + (yt - yc) ^ 2 = D) : False := by
  sorry

/-- TODO: prove.
What's missing: with `x_a, x_c ≥ 1/2`, `y_a y_c > 0`: `|ac|² ≤ 1` via `(a×c)² ≤ 3/4`, `a·c > 0`;
the one of `a, c` with smaller `|y|` separates `b = (1,0)` from the other one.
Acceptance: when both non-middle points are on the same side, the configuration can be relabelled
so that the middle point separates the other two.
Depends on: nothing. -/
theorem case3_select_real {xa ya xc yc : ℝ}
    (ha : xa ^ 2 + ya ^ 2 = 1) (hc : xc ^ 2 + yc ^ 2 = 1)
    (hab : (xa - 1) ^ 2 + ya ^ 2 ≤ 1) (hcb : (xc - 1) ^ 2 + yc ^ 2 ≤ 1)
    (hsame : 0 < ya * yc) (hne : ¬ (xa = xc ∧ ya = yc)) :
    (xa - xc) ^ 2 + (ya - yc) ^ 2 ≤ 1 ∧
      ((-ya) * (xa * yc - ya * xc) < 0 ∨ (-yc) * (xc * ya - yc * xa) < 0) := by
  sorry

/-- TODO: prove.
What's missing: (VERIFY_A1b Case 2 with the apex `v₁ = (1, 0)`): `x₂ = x₃ = −c`, `y₃ = −y₂`,
`D = 2 + 2c`, `c² ≥ 3/4`; with `ρ = |r|² = 2 x_r ∈ (0, 1]`:
both far distances `≤ 1` ⇒ `ρ(1 + c) ≤ 0`; `|r v₂|² = D` ⇒
`2(1+c)(1−ρ)(2−ρ) + 4c² − 3 = 0` ⇒ `ρ = 1, c² = 3/4` ⇒ `|r v₃|² = 2 ∈ (1, D)`; symmetric for `v₃`.
Acceptance: Case 2 core computation: the apex has no second `Δ₂`-neighbour.
Depends on: nothing. -/
theorem case2_real {x₂ y₂ x₃ y₃ xr yr D : ℝ} (hD : 1 < D)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (h₃ : x₃ ^ 2 + y₃ ^ 2 = 1)
    (h12 : (1 - x₂) ^ 2 + y₂ ^ 2 = D) (h13 : (1 - x₃) ^ 2 + y₃ ^ 2 = D)
    (h23 : (x₂ - x₃) ^ 2 + (y₂ - y₃) ^ 2 ≤ 1) (hne : ¬ (x₂ = x₃ ∧ y₂ = y₃))
    (hr1 : (xr - 1) ^ 2 + yr ^ 2 = 1) (hrn : xr ^ 2 + yr ^ 2 ≤ 1) (hr0 : 0 < xr ^ 2 + yr ^ 2)
    (g2 : (xr - x₂) ^ 2 + (yr - y₂) ^ 2 ≤ 1 ∨ (xr - x₂) ^ 2 + (yr - y₂) ^ 2 = D)
    (g3 : (xr - x₃) ^ 2 + (yr - y₃) ^ 2 ≤ 1 ∨ (xr - x₃) ^ 2 + (yr - y₃) ^ 2 = D) : False := by
  sorry

/-- TODO: prove.
What's missing: `r·A = ρ/2`, `r·C = ρ/2 − 1`; `r − (αA + βC)` is orthogonal to `A` and `C`,
which span the plane (`(A × C)² = 3/4`), so it vanishes; then `ρ = α² + β² − αβ`.
Acceptance: the two candidates of VERIFY_A1b Case 1: `r = (ρ − 2/3)A + (ρ − 4/3)C` with
`ρ² − 3ρ + 4/3 = 0`, `ρ = |r|²`.
Depends on: nothing. -/
theorem cand_real {a0 a1 c0 c1 r0 r1 : ℝ} (ha : a0 ^ 2 + a1 ^ 2 = 1) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hac : a0 * c0 + a1 * c1 = -1 / 2)
    (hra : (r0 - a0) ^ 2 + (r1 - a1) ^ 2 = 1) (hrc : (r0 - c0) ^ 2 + (r1 - c1) ^ 2 = 3) :
    r0 = (r0 ^ 2 + r1 ^ 2 - 2 / 3) * a0 + (r0 ^ 2 + r1 ^ 2 - 4 / 3) * c0 ∧
    r1 = (r0 ^ 2 + r1 ^ 2 - 2 / 3) * a1 + (r0 ^ 2 + r1 ^ 2 - 4 / 3) * c1 ∧
    (r0 ^ 2 + r1 ^ 2) ^ 2 - 3 * (r0 ^ 2 + r1 ^ 2) + 4 / 3 = 0 := by
  sorry

/-- TODO: prove.
What's missing: (VERIFY_A1b Case 1, `v₁ = (1,0)`): `D = 3`, `v₂ = (−1/2, y₂)`, `v₃ = (−1/2, −y₂)`;
each extra neighbour `rᵢ` is at squared distance `3` from some `vⱼ` (`j ≠ i`), hence a candidate
(`cand_real`); if `r₁` points to `v₂` then `|r₁ r₂|² ∈ {4/3, 3ρ} ⊆ (1, 3)`, else `|r₁ r₃|²` is.
Acceptance: Case 1 core computation: some vertex of the equilateral triangle has no second
`Δ₂`-neighbour.
Depends on: `cand_real`. -/
theorem case1_real {x₂ y₂ x₃ y₃ p₁ q₁ p₂ q₂ p₃ q₃ D : ℝ} (hD : 1 < D)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (h₃ : x₃ ^ 2 + y₃ ^ 2 = 1)
    (h12 : (1 - x₂) ^ 2 + y₂ ^ 2 = D) (h13 : (1 - x₃) ^ 2 + y₃ ^ 2 = D)
    (h23 : (x₂ - x₃) ^ 2 + (y₂ - y₃) ^ 2 = D)
    (hr₁ : (p₁ - 1) ^ 2 + q₁ ^ 2 = 1) (hr₂ : (p₂ - x₂) ^ 2 + (q₂ - y₂) ^ 2 = 1)
    (hr₃ : (p₃ - x₃) ^ 2 + (q₃ - y₃) ^ 2 = 1)
    (n₁ : p₁ ^ 2 + q₁ ^ 2 ≤ 1) (n₂ : p₂ ^ 2 + q₂ ^ 2 ≤ 1) (n₃ : p₃ ^ 2 + q₃ ^ 2 ≤ 1)
    (z₁ : 0 < p₁ ^ 2 + q₁ ^ 2) (z₂ : 0 < p₂ ^ 2 + q₂ ^ 2) (z₃ : 0 < p₃ ^ 2 + q₃ ^ 2)
    (g12 : (p₁ - x₂) ^ 2 + (q₁ - y₂) ^ 2 ≤ 1 ∨ (p₁ - x₂) ^ 2 + (q₁ - y₂) ^ 2 = D)
    (g13 : (p₁ - x₃) ^ 2 + (q₁ - y₃) ^ 2 ≤ 1 ∨ (p₁ - x₃) ^ 2 + (q₁ - y₃) ^ 2 = D)
    (g21 : (p₂ - 1) ^ 2 + q₂ ^ 2 ≤ 1 ∨ (p₂ - 1) ^ 2 + q₂ ^ 2 = D)
    (g23 : (p₂ - x₃) ^ 2 + (q₂ - y₃) ^ 2 ≤ 1 ∨ (p₂ - x₃) ^ 2 + (q₂ - y₃) ^ 2 = D)
    (g31 : (p₃ - 1) ^ 2 + q₃ ^ 2 ≤ 1 ∨ (p₃ - 1) ^ 2 + q₃ ^ 2 = D)
    (g32 : (p₃ - x₂) ^ 2 + (q₃ - y₂) ^ 2 ≤ 1 ∨ (p₃ - x₂) ^ 2 + (q₃ - y₂) ^ 2 = D)
    (gr12 : (p₁ - p₂) ^ 2 + (q₁ - q₂) ^ 2 ≤ 1 ∨ (p₁ - p₂) ^ 2 + (q₁ - q₂) ^ 2 = D)
    (gr13 : (p₁ - p₃) ^ 2 + (q₁ - q₃) ^ 2 ≤ 1 ∨ (p₁ - p₃) ^ 2 + (q₁ - q₃) ^ 2 = D) : False := by
  sorry

/-- TODO: prove.
What's missing: (VERIFY_A1c Lemma F, `p = 0`, `w = (1,0)`, `r` WLOG not below the axis):
Lemma M gives `|r a₁|² = |r a₂|² = D`; so `r ∥ a₁ + a₂`, which forces `x₁ + x₂ < 0`; the
neighbour `a` with `x_a < 0` has `|aw|² > 2`, so `|aw|² = D`; `chord_real` gives `|ab|² > D`.
Acceptance: Lemma F core computation.
Depends on: `lemmaM_real`, `chord_real`. -/
theorem lemmaF_real {x₁ y₁ x₂ y₂ xb yb xr yr D : ℝ} (hD : 1 < D)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 = 1) (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (hb : xb ^ 2 + yb ^ 2 = 1)
    (hy₁ : y₁ < 0) (hy₂ : y₂ < 0) (hyb : 0 < yb) (hne : ¬ (x₁ = x₂ ∧ y₁ = y₂))
    (hc₁ : 0 < x₁ * yb - y₁ * xb) (hc₂ : 0 < x₂ * yb - y₂ * xb)
    (hr : (xr - 1) ^ 2 + yr ^ 2 = 1) (hr0 : 0 < xr ^ 2 + yr ^ 2) (hyr : 0 ≤ yr)
    (g₁ : (xr - x₁) ^ 2 + (yr - y₁) ^ 2 ≤ 1 ∨ (xr - x₁) ^ 2 + (yr - y₁) ^ 2 = D)
    (g₂ : (xr - x₂) ^ 2 + (yr - y₂) ^ 2 ≤ 1 ∨ (xr - x₂) ^ 2 + (yr - y₂) ^ 2 = D)
    (gw₁ : (x₁ - 1) ^ 2 + y₁ ^ 2 ≤ 1 ∨ (x₁ - 1) ^ 2 + y₁ ^ 2 = D)
    (gw₂ : (x₂ - 1) ^ 2 + y₂ ^ 2 ≤ 1 ∨ (x₂ - 1) ^ 2 + y₂ ^ 2 = D)
    (m₁ : (x₁ - xb) ^ 2 + (y₁ - yb) ^ 2 ≤ D) (m₂ : (x₂ - xb) ^ 2 + (y₂ - yb) ^ 2 ≤ D) :
    False := by
  sorry

/-! ## Prop 3: core vertices of `L₂` have core degree `2` -/

/-- TODO: prove.
What's missing: frame at `q` with axis `m`; `t` from `exists_of_not_isExt` with coefficients
`q − m`; transport all squared distances through `frame_sqd`; apply `case3_real'`.
Acceptance: Case 3 when the middle neighbour `m` separates `a` and `c`.
Depends on: `frame_sqd`, `frame_base`, `frame_axis`, `frame_cross`, `exists_of_not_isExt`,
`dist_le_snd_of_not_isExt`, `TwoLargest.sqd_gap`, `case3_real'`. -/
theorem prop3_case3_core {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q m a c : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (hm : m ∈ X) (ha : a ∈ X) (hc : c ∈ X)
    (hqm : dist q m = Δ₂) (hqa : dist q a = Δ₂) (hqc : dist q c = Δ₂)
    (hma : sqd m a ≤ Δ₂ ^ 2) (hmc : sqd m c ≤ Δ₂ ^ 2)
    (hopp : orient q m a * orient q m c < 0) : False := by
  sorry

/-- TODO: prove.
What's missing: frame at `q` with axis `v₂`; if `v₁, v₃` are on opposite sides use
`prop3_case3_core` with middle `v₂`, otherwise `case3_select_real` picks middle `v₁` or `v₃`.
Acceptance: Case 3 (at most one `Δ`-pair; labelled so that `v₂` is close to both others).
Depends on: `prop3_case3_core`, `case3_select_real`, frame lemmas. -/
theorem prop3_case3 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃)
    (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (s12 : sqd v₁ v₂ ≤ Δ₂ ^ 2) (s23 : sqd v₂ v₃ ≤ Δ₂ ^ 2) : False := by
  sorry

/-- TODO: prove.
What's missing: frame at `q` with axis `v₁`; transport; apply `case2_real`.
Acceptance: Case 2 (exactly two `Δ`-pairs, apex `v₁`): `v₁` has no `Δ₂`-neighbour besides `q`.
Depends on: frame lemmas, `dist_le_snd_of_not_isExt`, `case2_real`. -/
theorem prop3_case2 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ r : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (h23 : v₂ ≠ v₃) (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (s12 : sqd v₁ v₂ = Δ ^ 2) (s13 : sqd v₁ v₃ = Δ ^ 2) (s23 : sqd v₂ v₃ ≤ Δ₂ ^ 2)
    (hr : r ∈ X) (hrq : r ≠ q) (hr₁ : dist v₁ r = Δ₂) : False := by
  sorry

/-- TODO: prove.
What's missing: frame at `q` with axis `v₁`; transport; apply `case1_real`.
Acceptance: Case 1 (all three pairs at `Δ`): not all three `vᵢ` have a second neighbour.
Depends on: frame lemmas, `dist_le_snd_of_not_isExt`, `case1_real`. -/
theorem prop3_case1 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ r₁ r₂ r₃ : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (s12 : sqd v₁ v₂ = Δ ^ 2) (s13 : sqd v₁ v₃ = Δ ^ 2) (s23 : sqd v₂ v₃ = Δ ^ 2)
    (hr₁ : r₁ ∈ X) (hr₂ : r₂ ∈ X) (hr₃ : r₃ ∈ X) (hrq₁ : r₁ ≠ q) (hrq₂ : r₂ ≠ q) (hrq₃ : r₃ ≠ q)
    (e₁ : dist v₁ r₁ = Δ₂) (e₂ : dist v₂ r₂ = Δ₂) (e₃ : dist v₃ r₃ = Δ₂) : False := by
  sorry

/-- TODO: prove.
What's missing: split on which of the three pairs are at distance `Δ` (`TwoLargest.sqd_gap`) and
call `prop3_case1/2/3` with the right labelling.
Acceptance: a non-extreme point cannot have three `Δ₂`-neighbours that each have a further
`Δ₂`-neighbour.
Depends on: `prop3_case1`, `prop3_case2`, `prop3_case3`. -/
theorem prop3_three {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ r₁ r₂ r₃ : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃)
    (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (hr₁ : r₁ ∈ X) (hr₂ : r₂ ∈ X) (hr₃ : r₃ ∈ X) (hrq₁ : r₁ ≠ q) (hrq₂ : r₂ ≠ q) (hrq₃ : r₃ ≠ q)
    (e₁ : dist v₁ r₁ = Δ₂) (e₂ : dist v₂ r₂ = Δ₂) (e₃ : dist v₃ r₃ = Δ₂) : False := by
  sorry

/-- TODO: prove.
What's missing: `≥ 2` from `minDeg2_core`; three core neighbours `v₁, v₂, v₃` would each have a
core neighbour `rᵢ ≠ q`, contradicting `prop3_three` (`q ∈ L₂` is not extreme in `X`).
Acceptance: **Prop 3**: every `q ∈ L₂ ∩ V(G′)` has `deg_{G′} q = 2`.
Depends on: `prop3_three`, `minDeg2_core`, `core_subset`, `mem_L2`, `disjoint_L1_L2`. -/
theorem deg_core_L2 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q : Pt}
    (hq : q ∈ L2 X) (hK : q ∈ core (L1 X ∪ L2 X) Δ₂) :
    (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ q).card = 2 := by
  sorry

/-! ## Degree at most 4 on `L₁′` (Lemma M, Lemma F) -/

/-- TODO: prove.
What's missing: frame at `p` with axis `w`; if `r` is not strictly right of `pw` use `a₁, a₂, b₁`,
else reflect (`y ↦ −y`) and use `b₁, b₂, a₁`; apply `lemmaF_real`.
Acceptance: **Lemma F**: a neighbour `w` of an extreme point `p` with two further neighbours of
`p` strictly on each side of the line `pw` has `p` as its only `Δ₂`-neighbour.
Depends on: frame lemmas, `lemmaF_real`, `TwoLargest.sqd_gap`, `TwoLargest.sqd_le`. -/
theorem lemmaF {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p w a₁ a₂ b₁ b₂ : Pt}
    (hp : p ∈ X) (hw : w ∈ X) (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X) (hb₁ : b₁ ∈ X) (hb₂ : b₂ ∈ X)
    (dw : dist p w = Δ₂) (da₁ : dist p a₁ = Δ₂) (da₂ : dist p a₂ = Δ₂)
    (db₁ : dist p b₁ = Δ₂) (db₂ : dist p b₂ = Δ₂) (hna : a₁ ≠ a₂) (hnb : b₁ ≠ b₂)
    (oa₁ : orient p w a₁ < 0) (oa₂ : orient p w a₂ < 0)
    (ob₁ : 0 < orient p w b₁) (ob₂ : 0 < orient p w b₂)
    (o11 : 0 < orient p a₁ b₁) (o21 : 0 < orient p a₂ b₁)
    (o12 : 0 < orient p a₁ b₂) (o22 : 0 < orient p a₂ b₂)
    {r : Pt} (hr : r ∈ X) (hwr : dist w r = Δ₂) : r = p := by
  sorry

/-- TODO: prove.
What's missing: with the half-plane normal `n` of `p`, `g x = (n × (x−p)) / (n·(x−p))` orders the
neighbours by angle (`orient p x y > 0 ↔ g x < g y`) and is injective on points at equal
distance from `p`; sort the 5 values (`orderEmbOfFin`) and take the median.
Acceptance: among five `Δ₂`-neighbours of an extreme point, the angular median has two of them
strictly on each side.
Depends on: nothing beyond the definitions. -/
theorem exists_median {X : Finset Pt} {Δ₂ : ℝ} {p : Pt} (hp : IsExt X p) {S : Finset Pt}
    (hSX : S ⊆ X) (hS : ∀ x ∈ S, dist p x = Δ₂) (hpos : 0 < Δ₂) (h5 : 5 ≤ S.card) :
    ∃ w ∈ S, ∃ a₁ ∈ S, ∃ a₂ ∈ S, ∃ b₁ ∈ S, ∃ b₂ ∈ S, a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      orient p w a₁ < 0 ∧ orient p w a₂ < 0 ∧ 0 < orient p w b₁ ∧ 0 < orient p w b₂ ∧
      0 < orient p a₁ b₁ ∧ 0 < orient p a₂ b₁ ∧ 0 < orient p a₁ b₂ ∧ 0 < orient p a₂ b₂ := by
  sorry

/-- TODO: prove.
What's missing: five core neighbours give a median `w` (`exists_median`); by `lemmaF` all
`Δ₂`-neighbours of `w` equal `p`, but `w ∈ core` has two core neighbours.
Acceptance: **degree ≤ 4**: every `p ∈ L₁ ∩ V(G′)` has `deg_{G′} p ≤ 4`.
Depends on: `exists_median`, `lemmaF`, `minDeg2_core`, `core_subset`. -/
theorem deg_core_L1_le_four {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p : Pt}
    (hp : p ∈ L1 X) (hK : p ∈ core (L1 X ∪ L2 X) Δ₂) :
    (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card ≤ 4 := by
  sorry

/-! ## Theorem A and Corollary A1 -/

/-- TODO: prove.
What's missing: `2μ = esum X = esum (L₁ ∪ L₂) ≤ esum K + 2|(L₁ ∪ L₂) \ K|`; split `esum K` over
`K ∩ L₁` and `K ∩ L₂` and use `deg_core_L2`.
Acceptance: **Theorem A** (doubled): `2μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁′} (deg′ p − 2)`.
Depends on: `two_mul_multS`, `esum_eq_esum_L12`, `esum_le_core`, `deg_core_L2`, `minDeg2_core`. -/
theorem theoremA {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    2 * multS X Δ₂ ≤ 2 * (L1 X).card + 2 * (L2 X).card +
      ∑ p ∈ L1 X ∩ core (L1 X ∪ L2 X) Δ₂, ((nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card - 2) := by
  sorry

/-- TODO: prove.
What's missing: `deg_{G′} p ≤ deg_X p ≤ 3`, so each summand of Theorem A is `≤ 1`.
Acceptance: **Corollary A1**: under (H3), `2μ(Δ₂) ≤ 3|L₁| + 2|L₂|`.
Depends on: `theoremA`, `nbr_mono`, `core_subset`. -/
theorem corA1 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂)
    (hH3 : ∀ p ∈ L1 X, (nbr X Δ₂ p).card ≤ 3) :
    2 * multS X Δ₂ ≤ 3 * (L1 X).card + 2 * (L2 X).card := by
  sorry

/-- TODO: prove.
What's missing: `deg′ p ≤ min(h p, 4)` (`nbr_mono`, `deg_core_L1_le_four`); extend the sum from
`L₁′` to `L₁` (nonnegative summands).
Acceptance: **unconditional form**:
`2μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁} (min(h p, 4) − 2)` (truncated subtraction = `(·)⁺`).
Depends on: `theoremA`, `deg_core_L1_le_four`. -/
theorem corA1_uncond {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    2 * multS X Δ₂ ≤ 2 * (L1 X).card + 2 * (L2 X).card +
      ∑ p ∈ L1 X, (min (nbr X Δ₂ p).card 4 - 2) := by
  sorry

/-- TODO: prove.
What's missing: each summand of `corA1_uncond` is `≤ 2`.
Acceptance: CDL's layer bound `μ(Δ₂) ≤ 2|L₁| + |L₂|`.
Depends on: `corA1_uncond`. -/
theorem cdl_layer_bound {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    multS X Δ₂ ≤ 2 * (L1 X).card + (L2 X).card := by
  sorry

/-- TODO: prove.
What's missing: `|L₁| + |L₂| ≤ |X|` (disjoint subsets) and arithmetic.
Acceptance: under (H3), `|L₁| ≤ 2 m₃` (with `m₃ = |X| − |L₁| − |L₂|`) implies `μ(Δ₂) ≤ |X|`.
Depends on: `corA1`, `disjoint_L1_L2`, `L1_subset`, `L2_subset`. -/
theorem corA1_le_card {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂)
    (hH3 : ∀ p ∈ L1 X, (nbr X Δ₂ p).card ≤ 3)
    (h : (L1 X).card ≤ 2 * (X.card - (L1 X).card - (L2 X).card)) : multS X Δ₂ ≤ X.card := by
  sorry

end Erdos132Layer

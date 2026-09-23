import Erdos.E132ConvexFinset
import Erdos.E132Ve87
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Erdős Problem 132, the `54/37` theorem — definitions and the counting reductions (§§1–4)

Skeleton of the Lean formalisation of `problems/132/WRITEUP_A2.md` (paper §§2–7):

> there is an absolute `C₀` such that every finite `X ⊆ ℝ²` satisfies
> `min {μ(Δ₂), μ(δ)} ≤ (54/37)·|X| + C₀`.

Files:
* `E132MainDefs.lean`    — distances, `S / R / D`, `K`, the direction field, edge classes,
  turning measure; cited results [Ve87], [HP]; reductions (VS), (E); LP Lemmas 4.1, 4.2;
  normalisation `δ = 1`; small cases; numeric constants.
* `E132MainLocal.lean`   — §3 (Lemmas 3.1–3.4, rung identity, T-edge/rung dichotomy, T1, T2)
  and §5 (lens lemma, bad-edge counts KK, DD, c1, c2).
* `E132MainRegions.lean` — §6 Region I, §7 Regions II/III (Lemma 7.1, R1, R2, R2-sym, R3,
  ownership/pairing, corner lemma).
* `E132MainDegen.lean`   — §8 degenerate regime `Δ > 1.94 Δ₂ ⇒ μ(Δ₂) ≤ n + 1`.
* `E132Main.lean`        — §9 assembly: `erdos132_main` (proved from the lemma statements).

Conventions (finite sets, unordered pairs of distinct points, as in `E132ConvexFinset`):
* `diam X` = largest distance, `dist2 X` = largest distance `< diam X`, `minDist X` = smallest
  distance; each is `0` when it does not exist, and `mult X 0 = 0`, so degenerate small sets
  need no side conditions.
* `mult X d` = number of unordered pairs of `X` at distance `d`.

Every lemma carries a docstring `TODO / What's missing / Acceptance / Depends on`.
Plan and difficulty estimates: `problems/132/lean/MAIN_PLAN.md`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical
open Erdos132Layer (sqd dist_eq_iff_sqd dist_sq_eq_sqd dist_mem_distSetS pos_of_mem_distSetS)

namespace Erdos132Main

noncomputable section

/-! ## Distances of a finite set -/

/-- Number of unordered pairs of distinct points of `X` at distance `d` (`μ(d)`). -/
abbrev mult (X : Finset Pt) (d : ℝ) : ℕ := multS X d

/-- Diameter `Δ` (largest distance; `0` if `X` has no pair). -/
def diam (X : Finset Pt) : ℝ :=
  if h : (distSetS X).Nonempty then (distSetS X).max' h else 0

/-- Second-largest distance `Δ₂` (largest distance `< Δ`; `0` if there is none). -/
def dist2 (X : Finset Pt) : ℝ :=
  if h : ((distSetS X).erase (diam X)).Nonempty then ((distSetS X).erase (diam X)).max' h else 0

/-- Minimum distance `δ` (`0` if `X` has no pair). -/
def minDist (X : Finset Pt) : ℝ :=
  if h : (distSetS X).Nonempty then (distSetS X).min' h else 0

/-- The points of `X` other than `p` at distance `d` from `p`. -/
def partners (X : Finset Pt) (d : ℝ) (p : Pt) : Finset Pt :=
  X.filter (fun q => q ≠ p ∧ dist p q = d)

/-- `S`: points of `X` with a `Δ₂`-partner. -/
def Sset (X : Finset Pt) : Finset Pt := X.filter (fun p => (partners X (dist2 X) p).Nonempty)

/-- `R := X ∖ S`. -/
def Rset (X : Finset Pt) : Finset Pt := X \ Sset X

/-- `D`: endpoints of diametral pairs. -/
def Dset (X : Finset Pt) : Finset Pt := X.filter (fun p => (partners X (diam X) p).Nonempty)

/-- `Δ₂`-degree of `p`. -/
def deg2 (X : Finset Pt) (p : Pt) : ℕ := (partners X (dist2 X) p).card

/-- `e(S)`: number of `δ`-pairs inside `S`. -/
def eS (X : Finset Pt) : ℕ := mult (Sset X) (minDist X)

/-- The `δ`-pairs inside `S` (as unordered pairs). `(edges X).card = eS X`. -/
def edges (X : Finset Pt) : Finset (Sym2 Pt) :=
  (pairsS (Sset X)).filter (fun z => pairDist z = minDist X)

/-! ## Parameters and constants (δ normalised to 1) -/

/-- `β = 1/100`. -/
def beta : ℝ := 1 / 100

/-- `t := Δ − Δ₂`. -/
def tgap (X : Finset Pt) : ℝ := diam X - dist2 X

/-- `τ := t − (1 − t²)/(2Δ₂)`. -/
def tau (X : Finset Pt) : ℝ := tgap X - (1 - tgap X ^ 2) / (2 * dist2 X)

/-- Rung offset length `s := √(1 − τ²)`. -/
def sOff (X : Finset Pt) : ℝ := √(1 - tau X ^ 2)

/-- Packing threshold `N₀ = 1.51·10⁹` for the small cases. -/
def N₀ : ℝ := 151 * 10 ^ 7

/-- Uniform bound on the number of bad edges (paper: `< 1.83·10⁷`). -/
def cBad : ℝ := 2 * 10 ^ 7

/-- The additive constant of the main theorem: `C₀ ≥ 3N₀ + cBad + 100`. -/
def C₀ : ℝ := 5 * 10 ^ 9

/-- The **nondegenerate, normalised, large** regime of §§4–7: `δ = 1`, `Δ ≤ 1.94Δ₂`,
`Δ₂ ≥ 10⁴`, `n ≥ 4`. -/
structure Normal (X : Finset Pt) : Prop where
  four_le : 4 ≤ X.card
  minDist_eq : minDist X = 1
  nondeg : diam X ≤ 1.94 * dist2 X
  large : 10 ^ 4 ≤ dist2 X

/-! ## Geometry: ball polygon, direction field, normal cones, turning -/

/-- The ball polygon `K := ⋂_{w ∈ X} D(w, Δ₂)`. -/
def KBall (X : Finset Pt) : Set Pt := ⋂ w ∈ (X : Set Pt), Metric.closedBall w (dist2 X)

/-- `det(a, b)`: positive iff `b` is to the left of `a`. -/
def det2 (a b : Pt) : ℝ := a 0 * b 1 - a 1 * b 0

/-- Rotation by `+90°`. -/
def perp (a : Pt) : Pt := !₂[-a 1, a 0]

/-- Unoriented angle between two vectors. -/
def ang (a b : Pt) : ℝ := InnerProductGeometry.angle a b

/-- Unit vector of direction `θ`. -/
def dirVec (θ : ℝ) : Pt := !₂[Real.cos θ, Real.sin θ]

/-- Outward normal cone of `K` at `x`. -/
def normalCone (K : Set Pt) (x : Pt) : Set Pt := {ν | ∀ y ∈ K, inner ℝ (y - x) ν ≤ 0}

/-- **Turning** of a set `γ` of boundary points: the measure of the set of directions lying in the
normal cone at some point of `γ` (full cones at the endpoints included, §3). -/
def turning (K γ : Set Pt) : ℝ :=
  (MeasureTheory.volume
    {θ : ℝ | θ ∈ Set.Ico 0 (2 * π) ∧ ∃ x ∈ γ, dirVec θ ∈ normalCone K x}).toReal

/-- A **direction field** (§3): a chosen partner for each `p ∈ S` — a `Δ₂`-partner if `p ∉ D`,
a diametral partner if `p ∈ D`.  The inward normal is `u p := (partner p − p)/|partner p − p|`. -/
structure DirField (X : Finset Pt) where
  partner : Pt → Pt
  partner_mem : ∀ p ∈ Sset X, partner p ∈ X
  partner_K : ∀ p ∈ Sset X, p ∉ Dset X → dist p (partner p) = dist2 X
  partner_D : ∀ p ∈ Sset X, p ∈ Dset X → dist p (partner p) = diam X

/-- The unit inward normal `u_p`. -/
def DirField.u {X : Finset Pt} (F : DirField X) (p : Pt) : Pt :=
  (dist p (F.partner p))⁻¹ • (F.partner p - p)

/-! ## Edge classes -/

variable {X : Finset Pt}

/-- A `δ`-edge is **good** if `∠(u_p, u_q) ≤ β`. -/
def IsGood (F : DirField X) (z : Sym2 Pt) : Prop :=
  ∀ p q, z = s(p, q) → ang (F.u p) (F.u q) ≤ beta

/-- Good `δ`-edges inside `S`. -/
def good (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) := (edges X).filter (IsGood F)

/-- Bad `δ`-edges inside `S`. -/
def bad (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (edges X).filter (fun z => ¬ IsGood F z)

/-- **T-edge**: `a = (q−p)·u_p ∈ (0, β)` and `b = (p−q)·u_q ∈ (0, β)`. -/
def IsTEdge (F : DirField X) (p q : Pt) : Prop :=
  0 < inner ℝ (q - p) (F.u p) ∧ inner ℝ (q - p) (F.u p) < beta ∧
  0 < inner ℝ (p - q) (F.u q) ∧ inner ℝ (p - q) (F.u q) < beta

/-- **Rung** `(v, z)`: `v ∈ S ∖ D`, `z ∈ S ∩ D`, `|vz| = 1`, and `z` is an exception for `v`
(`|z w_v| = Δ`). -/
def IsRung (F : DirField X) (v z : Pt) : Prop :=
  v ∈ Sset X ∧ v ∉ Dset X ∧ z ∈ Sset X ∧ z ∈ Dset X ∧ dist v z = 1 ∧
    dist z (F.partner v) = diam X

/-- `q` is the **right** (`σ = -1`) / **left** (`σ = 1`) T-neighbour of `p`. -/
def IsSideT (F : DirField X) (σ : ℝ) (p q : Pt) : Prop :=
  p ∈ Sset X ∧ q ∈ Sset X ∧ dist p q = 1 ∧ ang (F.u p) (F.u q) ≤ beta ∧ IsTEdge F p q ∧
    0 < σ * det2 (F.u p) (q - p)

/-- Good T-edges. -/
def tEdges (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (good X F).filter (fun z => ∀ p q, z = s(p, q) → IsTEdge F p q)

/-- Good rungs. -/
def rungs (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (good X F).filter (fun z => ∃ v w, z = s(v, w) ∧ IsRung F v w)

/-- Mixed T-edges (one end in `D`, one not). -/
def mixedT (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (tEdges X F).filter (fun z => ∃ v w, z = s(v, w) ∧ v ∉ Dset X ∧ w ∈ Dset X)

/-- Good edges that are not mixed T-edges (pure T-edges and rungs). -/
def goodPure (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) := good X F \ mixedT X F

/-! ## Helper lemmas: pairs at a given distance

Helpers live in the sub-namespace `Erdos132Main.Defs` (opened below) so that they cannot clash
with helpers of the same name in the downstream files. -/

namespace Defs

/-- Membership of an unordered pair in `pairsS`. -/
theorem mk_mem_pairsS {Y : Finset Pt} {a b : Pt} :
    s(a, b) ∈ pairsS Y ↔ a ∈ Y ∧ b ∈ Y ∧ a ≠ b := by
  unfold pairsS
  rw [mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, and_assoc]

/-- `pairDist` of an explicit pair. -/
theorem pairDist_mk (a b : Pt) : pairDist s(a, b) = dist a b := rfl

/-- `mult` as the card of an explicit filter. -/
theorem mult_eq_card (Y : Finset Pt) (d : ℝ) :
    mult Y d = ((pairsS Y).filter (fun z => pairDist z = d)).card := by
  unfold mult multS; convert rfl

/-- Membership in the pairs at distance `d`. -/
theorem mem_pairsAt {Y : Finset Pt} {d : ℝ} {a b : Pt} :
    s(a, b) ∈ (pairsS Y).filter (fun z => pairDist z = d) ↔
      a ∈ Y ∧ b ∈ Y ∧ a ≠ b ∧ dist a b = d := by
  rw [mem_filter, mk_mem_pairsS, pairDist_mk, and_assoc, and_assoc]

/-- `mult` is monotone in the set. -/
theorem mult_mono {Y Z : Finset Pt} (h : Y ⊆ Z) (d : ℝ) : mult Y d ≤ mult Z d := by
  rw [mult_eq_card, mult_eq_card]
  refine card_le_card fun z hz => ?_
  induction z using Sym2.ind with
  | h a b =>
    obtain ⟨ha, hb, hab, hd⟩ := mem_pairsAt.1 hz
    exact mem_pairsAt.2 ⟨h ha, h hb, hab, hd⟩

/-- Membership in `partners`. -/
theorem mem_partners {Y : Finset Pt} {d : ℝ} {p q : Pt} :
    q ∈ partners Y d p ↔ q ∈ Y ∧ q ≠ p ∧ dist p q = d := by
  unfold partners; rw [mem_filter]

/-- Pairs of `Z` at distance `d` are those inside `Y` plus those meeting `Z \ Y`. -/
theorem mult_le_add_sum (Y Z : Finset Pt) (d : ℝ) :
    mult Z d ≤ mult Y d + ∑ x ∈ Z \ Y, (partners Z d x).card := by
  rw [mult_eq_card, mult_eq_card]
  have hsub : (pairsS Z).filter (fun z => pairDist z = d) ⊆
      (pairsS Y).filter (fun z => pairDist z = d) ∪
        (Z \ Y).biUnion (fun x => (partners Z d x).image (fun q => s(x, q))) := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨ha, hb, hab, hd⟩ := mem_pairsAt.1 hz
      rw [mem_union, mem_biUnion]
      by_cases haY : a ∈ Y
      · by_cases hbY : b ∈ Y
        · exact Or.inl (mem_pairsAt.2 ⟨haY, hbY, hab, hd⟩)
        · refine Or.inr ⟨b, mem_sdiff.2 ⟨hb, hbY⟩, mem_image.2 ⟨a, ?_, Sym2.eq_swap⟩⟩
          exact mem_partners.2 ⟨ha, hab, by rw [dist_comm]; exact hd⟩
      · refine Or.inr ⟨a, mem_sdiff.2 ⟨ha, haY⟩, mem_image.2 ⟨b, ?_, rfl⟩⟩
        exact mem_partners.2 ⟨hb, Ne.symm hab, hd⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  exact card_biUnion_le.trans (sum_le_sum fun x _ => card_image_le)

/-- `δ ≤` every distance of distinct points. -/
theorem minDist_le_dist {X : Finset Pt} {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    minDist X ≤ dist x y := by
  have hm := dist_mem_distSetS hx hy hxy
  have hne : (distSetS X).Nonempty := ⟨_, hm⟩
  rw [minDist, dite_eq_left hne]
  exact min'_le _ _ hm

/-- Two points on a circle of radius `δ` whose angles differ by less than `π/3` are at distance
`< δ`. -/
theorem sqd_lt_of_arg {δ a b : ℝ} (hδ : 0 < δ) (hab : |a - b| < π / 3) :
    (δ * cos a - δ * cos b) ^ 2 + (δ * sin a - δ * sin b) ^ 2 < δ ^ 2 := by
  have hc : 1 / 2 < cos (a - b) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hab
  have e : (δ * cos a - δ * cos b) ^ 2 + (δ * sin a - δ * sin b) ^ 2 =
      δ ^ 2 * (2 - 2 * cos (a - b)) := by
    rw [Real.cos_sub]
    linear_combination δ ^ 2 * (Real.sin_sq_add_cos_sq a) + δ ^ 2 * (Real.sin_sq_add_cos_sq b)
  rw [e]
  have : 0 < δ ^ 2 := by positivity
  nlinarith

/-- No pair of distinct points is at distance `0`. -/
theorem mult_zero (Y : Finset Pt) : mult Y 0 = 0 := by
  rw [mult_eq_card, card_eq_zero, filter_eq_empty_iff]
  intro z hz h0
  induction z using Sym2.ind with
  | h a b =>
    obtain ⟨-, -, hab⟩ := mk_mem_pairsS.1 hz
    rw [pairDist_mk] at h0
    exact hab (dist_eq_zero.1 h0)

/-- `δ ≥ 0`. -/
theorem minDist_nonneg (X : Finset Pt) : 0 ≤ minDist X := by
  unfold minDist
  split_ifs with h
  · exact (pos_of_mem_distSetS (min'_mem _ h)).le
  · exact le_rfl

end Defs

open Defs

/-! ## Cited results -/

/-- **[Ve87]** Vesztergombi, *On large distances in planar sets*, Discrete Math. 67 (1987)
191–198: in every `m`-point planar set the second-largest distance occurs at most `3m/2` times.

Formerly a cited black box; now **proved** in `Erdos.E132Ve87` (2-core argument on the
`Δ₂`-graph of `L₁ ∪ L₂`), whose `Erdos132Ve87.vesztergombi87` has this exact statement up to
unfolding its local copies of `diam`/`dist2`.
Acceptance: no `sorry` (done). -/
theorem vesztergombi87 (Y : Finset Pt) : (mult Y (dist2 Y) : ℝ) ≤ 3 / 2 * Y.card :=
  Erdos132Ve87.vesztergombi87 Y

/-- **[HP]** Hopf–Pannwitz (1934): in every `m`-point planar set the diameter occurs at most
`m` times.

TODO: prove (classical: two diametral segments always intersect; a graph with pairwise-crossing
edges in convex-ish position has `≤ m` edges).
What's missing: the crossing lemma and the counting (each vertex of degree ≥ 2 forces a leaf).
Acceptance: no `sorry`.
Depends on: nothing (planar geometry only). Difficulty L. -/
theorem hopf_pannwitz (Y : Finset Pt) : mult Y (diam Y) ≤ Y.card := by
  sorry

/-! ## Elementary counting -/

/-- `|S| + |R| = n`.

TODO: none — proved (Phase 2).
What's missing: nothing mathematical.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_S_add_R (X : Finset Pt) : (Sset X).card + (Rset X).card = X.card := by
  rw [Rset, add_comm]; exact card_sdiff_add_card_eq_card (filter_subset _ _)

/-- `e(S)` is the number of `edges`.

TODO: none — proved (Phase 2).
What's missing: nothing.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_edges (X : Finset Pt) : (edges X).card = eS X := by
  rfl

/-- **Kissing bound**: a point has at most 6 points of `X` at distance `δ`.

TODO: prove.
What's missing: two `δ`-neighbours of `p` subtend `≥ 60°` at `p` (else closer than `δ`),
so at most 6 fit around `p`.
Acceptance: no `sorry`.
Depends on: angle facts in `ℝ²`. Difficulty M. -/
theorem card_partners_minDist_le (X : Finset Pt) (p : Pt) :
    (partners X (minDist X) p).card ≤ 6 := by
  set δ := minDist X with hδdef
  by_contra hcon
  push Not at hcon
  obtain ⟨q₀, hq₀⟩ := card_pos.1 (by omega : 0 < (partners X δ p).card)
  obtain ⟨-, hq₀p, hq₀d⟩ := Defs.mem_partners.1 hq₀
  have hδ : 0 < δ := by rw [← hq₀d]; exact dist_pos.2 (Ne.symm hq₀p)
  let z : Pt → ℂ := fun q => ⟨q 0 - p 0, q 1 - p 1⟩
  have hz : ∀ q ∈ partners X δ p, ‖z q‖ = δ := by
    intro q hq
    obtain ⟨-, -, hd⟩ := Defs.mem_partners.1 hq
    have h1 := (dist_eq_iff_sqd hδ.le).1 hd
    have h2 : ‖z q‖ ^ 2 = δ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk, ← h1, sqd]; ring
    exact (pow_left_inj₀ (norm_nonneg _) hδ.le two_ne_zero).1 h2
  have hre : ∀ q ∈ partners X δ p, q 0 - p 0 = δ * cos (Complex.arg (z q)) := by
    intro q hq
    have hz0 : z q ≠ 0 := by
      intro h; have := hz q hq; rw [h, norm_zero] at this; linarith
    rw [Complex.cos_arg hz0, hz q hq, mul_div_cancel₀ _ hδ.ne']
  have him : ∀ q ∈ partners X δ p, q 1 - p 1 = δ * sin (Complex.arg (z q)) := by
    intro q hq
    rw [Complex.sin_arg, hz q hq, mul_div_cancel₀ _ hδ.ne']
  let f : Pt → ℕ := fun q => ⌈(Complex.arg (z q) + π) / (π / 3)⌉₊
  have hmaps : ∀ q ∈ partners X δ p, f q ∈ Icc 1 6 := by
    intro q _
    have h1 := Complex.neg_pi_lt_arg (z q)
    have h2 := Complex.arg_le_pi (z q)
    have hp3 : 0 < π / 3 := by positivity
    rw [mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (div_pos (by linarith) hp3)))
    · refine Nat.ceil_le.2 ?_
      rw [div_le_iff₀ hp3]; push_cast; linarith
  have hcard : (Icc 1 6 : Finset ℕ).card < (partners X δ p).card := by simpa using hcon
  obtain ⟨q, hq, q', hq', hqq', hf⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hclose : |Complex.arg (z q) - Complex.arg (z q')| < π / 3 := by
    have hp3 : 0 < π / 3 := by positivity
    have h1 := Complex.neg_pi_lt_arg (z q)
    have h1' := Complex.neg_pi_lt_arg (z q')
    set x := (Complex.arg (z q) + π) / (π / 3)
    set y := (Complex.arg (z q') + π) / (π / 3)
    have hx0 : 0 ≤ x := div_nonneg (by linarith) hp3.le
    have hy0 : 0 ≤ y := div_nonneg (by linarith) hp3.le
    have a1 := Nat.le_ceil x
    have a2 := Nat.ceil_lt_add_one hx0
    have b1 := Nat.le_ceil y
    have b2 := Nat.ceil_lt_add_one hy0
    have hf' : (⌈x⌉₊ : ℝ) = ⌈y⌉₊ := by exact_mod_cast hf
    have hxy : |x - y| < 1 := by rw [abs_lt]; constructor <;> linarith
    have e : Complex.arg (z q) - Complex.arg (z q') = (x - y) * (π / 3) := by
      simp only [x, y]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hp3]
    nlinarith [abs_nonneg (x - y)]
  obtain ⟨hqX, -, -⟩ := Defs.mem_partners.1 hq
  obtain ⟨hq'X, -, -⟩ := Defs.mem_partners.1 hq'
  have hge := minDist_le_dist hqX hq'X hqq'
  have hsq : δ ^ 2 ≤ sqd q q' := by
    rw [← dist_sq_eq_sqd]; exact pow_le_pow_left₀ hδ.le hge 2
  have hlt := sqd_lt_of_arg hδ hclose
  have e : sqd q q' = (δ * cos (Complex.arg (z q)) - δ * cos (Complex.arg (z q'))) ^ 2 +
      (δ * sin (Complex.arg (z q)) - δ * sin (Complex.arg (z q'))) ^ 2 := by
    rw [← hre q hq, ← hre q' hq', ← him q hq, ← him q' hq', sqd]; ring
  linarith

/-- **Handshake with degree ≤ k**: `2|E| ≤ k|V|` for a loopless edge set on `V` whose vertices
have degree `≤ k`.

TODO: prove by double counting `Σ_{p ∈ V} deg p = 2|E|`.
What's missing: the double counting over `Sym2`.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty M. -/
theorem two_mul_card_le_of_deg_le {V : Finset Pt} {E : Finset (Sym2 Pt)} {k : ℕ}
    (hE : ∀ z ∈ E, ¬ z.IsDiag ∧ ∀ p ∈ z, p ∈ V)
    (hdeg : ∀ p ∈ V, (E.filter (fun z => p ∈ z)).card ≤ k) :
    2 * E.card ≤ k * V.card := by
  have h2 : ∀ z ∈ E, (V.filter (fun p => p ∈ z)).card = 2 := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨hd, hV⟩ := hE _ hz
      have hab : a ≠ b := by simpa using hd
      have : V.filter (fun p => p ∈ s(a, b)) = {a, b} := by
        ext x
        simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hV _ (Sym2.mem_mk_left _ _), Or.inl rfl⟩
          · exact ⟨hV _ (Sym2.mem_mk_right _ _), Or.inr rfl⟩
      rw [this, card_pair hab]
  have hdc : ∑ z ∈ E, (V.filter (fun p => p ∈ z)).card =
      ∑ p ∈ V, (E.filter (fun z => p ∈ z)).card := by
    simp only [card_filter]; exact sum_comm
  calc 2 * E.card = ∑ z ∈ E, (V.filter (fun p => p ∈ z)).card := by
        rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
    _ = ∑ p ∈ V, (E.filter (fun z => p ∈ z)).card := hdc
    _ ≤ ∑ _p ∈ V, k := sum_le_sum hdeg
    _ = k * V.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- `μ(δ) ≤ 3n` (from the kissing bound).

TODO: prove.
What's missing: handshake applied to the `δ`-graph.
Acceptance: no `sorry`.
Depends on: `card_partners_minDist_le`, `two_mul_card_le_of_deg_le`. Difficulty S–M. -/
theorem mult_minDist_le (X : Finset Pt) : (mult X (minDist X) : ℝ) ≤ 3 * X.card := by
  rcases (minDist_nonneg X).eq_or_lt with h0 | hpos
  · rw [← h0, mult_zero]; simp
  · have h2 := Erdos132Layer.two_mul_multS hpos X
    have hle : Erdos132Layer.esum X (minDist X) ≤ 6 * X.card := by
      unfold Erdos132Layer.esum
      calc ∑ v ∈ X, (Erdos132Layer.nbr X (minDist X) v).card ≤ ∑ _v ∈ X, 6 := by
            refine sum_le_sum fun v _ => le_trans (card_le_card fun x hx => ?_)
              (card_partners_minDist_le X v)
            obtain ⟨hxX, hd⟩ := Erdos132Layer.mem_nbr.1 hx
            refine Defs.mem_partners.2 ⟨hxX, fun h => ?_, hd⟩
            rw [h, dist_self] at hd; linarith
        _ = 6 * X.card := by rw [sum_const, smul_eq_mul, mul_comm]
    have : 2 * mult X (minDist X) ≤ 6 * X.card := by
      have e : mult X (minDist X) = multS X (minDist X) := rfl
      omega
    have : (2 * mult X (minDist X) : ℝ) ≤ 6 * X.card := by exact_mod_cast this
    linarith

/-! ## (VS) and (E) -/

/-- **(VS), general form**: for `Y ⊆ X`, the `Δ₂(X)`-pairs inside `Y` number `≤ (3/2)|Y|`.

TODO: prove.
What's missing: case split: if `diam Y = diam X` then `dist2 Y = dist2 X` (no distances of `X`
in `(Δ₂, Δ)`) and apply [Ve87] to `Y`; otherwise `diam Y ≤ Δ₂` and [HP] applies (or the count
is `0`).
Acceptance: no `sorry`.
Depends on: `vesztergombi87`, `hopf_pannwitz`. Difficulty M. -/
theorem mult_dist2_subset_le {Y : Finset Pt} (hY : Y ⊆ X) :
    (mult Y (dist2 X) : ℝ) ≤ 3 / 2 * Y.card := by
  sorry

/-- Every `Δ₂`-pair lies inside `S`.

TODO: prove.
What's missing: both ends of a `Δ₂`-pair have a `Δ₂`-partner, so are in `S`.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem mult_dist2_eq_S (X : Finset Pt) : mult X (dist2 X) = mult (Sset X) (dist2 X) := by
  refine le_antisymm ?_ (mult_mono (filter_subset _ _) _)
  refine (mult_le_add_sum (Sset X) _ _).trans (le_of_eq ?_)
  rw [sum_eq_zero, add_zero]
  intro x hx
  obtain ⟨hxX, hxS⟩ := mem_sdiff.1 hx
  rw [card_eq_zero, ← not_nonempty_iff_eq_empty]
  intro hne
  exact hxS (mem_filter.2 ⟨hxX, hne⟩)

/-- **(VS)** `μ(Δ₂) ≤ (3/2)|S|`.

TODO: none (proved from the two lemmas above).
Acceptance: no `sorry` (inherits theirs).
Depends on: `mult_dist2_eq_S`, `mult_dist2_subset_le`. -/
theorem VS (X : Finset Pt) : (mult X (dist2 X) : ℝ) ≤ 3 / 2 * (Sset X).card := by
  rw [mult_dist2_eq_S]
  exact mult_dist2_subset_le (filter_subset _ _)

/-- **(E)** `μ(δ) ≤ e(S) + 6r`: every `δ`-pair not inside `S` has an endpoint in `R`.

TODO: prove.
What's missing: split the `δ`-pairs of `X` into those inside `S` and those meeting `R`;
bound the latter by `Σ_{x ∈ R} deg_δ x ≤ 6r`.
Acceptance: no `sorry`.
Depends on: `card_partners_minDist_le`. Difficulty M. -/
theorem E_bound (X : Finset Pt) :
    (mult X (minDist X) : ℝ) ≤ eS X + 6 * (Rset X).card := by
  have h := mult_le_add_sum (Sset X) X (minDist X)
  have hs : ∑ x ∈ X \ Sset X, (partners X (minDist X) x).card ≤ 6 * (Rset X).card := by
    calc ∑ x ∈ X \ Sset X, (partners X (minDist X) x).card ≤ ∑ _x ∈ X \ Sset X, 6 :=
          sum_le_sum fun x _ => card_partners_minDist_le X x
      _ = 6 * (Rset X).card := by rw [sum_const, smul_eq_mul, mul_comm, Rset]
  have : mult X (minDist X) ≤ eS X + 6 * (Rset X).card := by
    rw [eS]; omega
  exact_mod_cast this

/-- **Weighted (VS)** (Lemma 4.2, first bullet): if every point of `P₁ ⊆ S` has `Δ₂`-degree 1
then `μ(Δ₂) ≤ |P₁| + (3/2)|S ∖ P₁|`.

TODO: prove.
What's missing: pairs touching `P₁` number `≤ |P₁|`; the rest lie in `S ∖ P₁`, apply
`mult_dist2_subset_le`.
Acceptance: no `sorry`.
Depends on: `mult_dist2_eq_S`, `mult_dist2_subset_le`. Difficulty M. -/
theorem VS_weighted {P₁ : Finset Pt} (hP : P₁ ⊆ Sset X) (hdeg : ∀ v ∈ P₁, deg2 X v = 1) :
    (mult X (dist2 X) : ℝ) ≤ P₁.card + 3 / 2 * (Sset X \ P₁).card := by
  sorry

/-! ## The linear programmes (Lemmas 4.1, 4.2) — pure algebra -/

/-- **Lemma 4.1** (LP certificate): with `λ = (6 − k)/(7.5 − k)`,
`min{μ₂, μ_δ} ≤ 9(s + r)/(7.5 − k) + C`.

TODO: none — proved (Phase 2).
What's missing: nothing — algebra.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_mix {μ₂ μδ s r e k C : ℝ} (_hk0 : 0 ≤ k) (hk : k ≤ 3 / 2) (_hs : 0 ≤ s) (_hr : 0 ≤ r)
    (hC : 0 ≤ C) (h₂ : μ₂ ≤ 3 / 2 * s) (hδ : μδ ≤ e + 6 * r) (he : e ≤ k * s + C) :
    min μ₂ μδ ≤ 9 * (s + r) / (15 / 2 - k) + C := by
  have hpos : 0 < 15 / 2 - k := by linarith
  have h1 := min_le_left μ₂ μδ
  have h2 := min_le_right μ₂ μδ
  set m := min μ₂ μδ
  have key : (15 / 2 - k) * m ≤ 9 * (s + r) + 3 / 2 * C := by
    have a : (6 - k) * m ≤ (6 - k) * (3 / 2 * s) :=
      mul_le_mul_of_nonneg_left (h1.trans h₂) (by linarith)
    have b : 3 / 2 * m ≤ 3 / 2 * (k * s + C + 6 * r) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    nlinarith
  have hCle : 3 / 2 * C ≤ (15 / 2 - k) * C := mul_le_mul_of_nonneg_right (by linarith) hC
  rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
  nlinarith

/-- **Lemma 4.2** (weighted LP, weights `4/5, 1/5`): `min{μ₂, μ_δ} ≤ (7/5)(s + r) + C`.

TODO: none — proved (Phase 2).
What's missing: nothing — algebra.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_weighted {μ₂ μδ s r e p C : ℝ} (_hp : 0 ≤ p) (_hps : p ≤ s) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (h₂ : μ₂ ≤ p + 3 / 2 * (s - p)) (hδ : μδ ≤ e + 6 * r) (he : e ≤ s + 2 * p + C) :
    min μ₂ μδ ≤ 7 / 5 * (s + r) + C := by
  have h1 := min_le_left μ₂ μδ
  have h2 := min_le_right μ₂ μδ
  linarith

/-- `9n/(7.5 − k) ≤ (54/37) n` for `0 ≤ k ≤ 4/3`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_value_le {k n : ℝ} (_hk0 : 0 ≤ k) (hk : k ≤ 4 / 3) (hn : 0 ≤ n) :
    9 * n / (15 / 2 - k) ≤ 54 / 37 * n := by
  have hpos : 0 < 15 / 2 - k := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **[C1]** values of the certificate: `k = 1, 5/4, 4/3 ↦ 18/13, 36/25, 54/37`, and
`7/5 ≤ 54/37`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_values :
    (9 : ℝ) / (15 / 2 - 1) = 18 / 13 ∧ (9 : ℝ) / (15 / 2 - 5 / 4) = 36 / 25 ∧
      (9 : ℝ) / (15 / 2 - 4 / 3) = 54 / 37 ∧ (7 : ℝ) / 5 ≤ 54 / 37 := by
  norm_num

/-! ## Normalisation and small cases -/

/-- **Scaling**: every `X` with `≥ 2` points has a copy `Y` (a dilate) with `δ(Y) = 1` and the
same `n`, `μ(Δ₂)`, `μ(δ)`.

TODO: prove.
What's missing: `Y := δ⁻¹ • X`; distances scale by `δ⁻¹`, so `diam`, `dist2`, `minDist`,
`mult` transform accordingly (`δ > 0` since the points are distinct).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty M. -/
theorem exists_normalize (hX : 2 ≤ X.card) :
    ∃ Y : Finset Pt, Y.card = X.card ∧ minDist Y = 1 ∧
      mult Y (dist2 Y) = mult X (dist2 X) ∧ mult Y (minDist Y) = mult X (minDist X) := by
  sorry

/-- **[C11]** `(2 · 1.94·10⁴ + 1)² < N₀`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem N0_check : (2 * (1.94 * 10 ^ 4) + 1 : ℝ) ^ 2 < N₀ := by
  norm_num [N₀]

/-- **Small cases** (§4): nondegenerate with `δ = 1`, `Δ₂ < 10⁴` ⇒ `n < N₀` (packing:
`n ≤ (2Δ + 1)²`).

TODO: prove.
What's missing: packing bound — disjoint discs of radius `1/2` around the points inside a disc
of radius `Δ + 1/2`, area comparison (or a grid-cell pigeonhole, which avoids measure theory).
Acceptance: no `sorry`.
Depends on: `N0_check`. Difficulty M–L. -/
theorem card_lt_N0 (h1 : minDist X = 1) (hnd : diam X ≤ 1.94 * dist2 X)
    (hsmall : dist2 X < 10 ^ 4) : (X.card : ℝ) < N₀ := by
  sorry

end

end Erdos132Main

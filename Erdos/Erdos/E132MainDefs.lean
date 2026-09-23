import Erdos.E132ConvexFinset
import Erdos.E132Ve87
import Mathlib.Analysis.Real.Pi.Bounds
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
  sorry

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
  sorry

/-- `μ(δ) ≤ 3n` (from the kissing bound).

TODO: prove.
What's missing: handshake applied to the `δ`-graph.
Acceptance: no `sorry`.
Depends on: `card_partners_minDist_le`, `two_mul_card_le_of_deg_le`. Difficulty S–M. -/
theorem mult_minDist_le (X : Finset Pt) : (mult X (minDist X) : ℝ) ≤ 3 * X.card := by
  sorry

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
  sorry

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
  sorry

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

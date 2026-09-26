import Erdos.E132Main97ANormal
import Erdos.E132Main97ACert

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A5: the visible path (V1–V4, Step 3)

`L97_reports/RouteA_visiblepath_report.md` §2 Steps 2–3, refereed in `REF_core_report.md`
§2.3–2.4 (fixes **G1** and **G4** are built in).

The drawing `𝒟` of `H = G[Yout]` minus isolated vertices (`Hv`) avoids `K′`.  The normal angles of
the vertices, sorted, are the events `ev 0 < … < ev (M−1) < ev M = ev 0 + 2π`; on each open
interval `I_i = (ev i, ev (i+1))` the first-hit edge `e_i = [eP i, eQ i]` is constant (`hit i`) or
the rays escape (`¬hit i`).  At the event `i` the path is `L_i → B_i → R_i` (`B_i` = first hit,
`L_i`/`R_i` = points of `e_{i−1}`/`e_i` on the ray).  A `VisPath` is this finite data; `Valid`
is its geometric meaning.  From it:

* `corners i : List Occ` — the corner occurrences at event `i` (**G1**: a dip `L_i = R_i ≠ B_i`
  gives two occurrences of one vertex);
* `turning_sum` (Step 3): `Σ κ = Σ_{hit} |I_i| − πJ` (pure telescoping of `ψ = ang(ν, d)`);
* `count_vOcc` (V4): `n + J ≤ m` (vertex occurrences);
* `Valid.foot` encodes V3.1 with the referee's compactness sentence (**G4**).

Only 1-D topology is used (IVT, compactness of the drawing, sorted finite lists).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

open Curve (dirMeasure)

noncomputable section

variable {X : Finset Pt} {ρ : ℕ}

/-! ## The drawing -/

/-- `h = ρ + ½`. -/
def hh (ρ : ℕ) : ℝ := (ρ : ℝ) + 1 / 2

/-- Vertices of `H`: points of `Yout ρ` with a unit neighbour in `Yout ρ`. -/
def Hv (X : Finset Pt) (ρ : ℕ) : Finset Pt :=
  (Yout X ρ).filter (fun v => ∃ q ∈ Yout X ρ, dist v q = 1)

/-- The drawing: the union of the unit segments with both ends in `V`. -/
def drawing (V : Finset Pt) : Set Pt :=
  {x | ∃ p ∈ V, ∃ q ∈ V, dist p q = 1 ∧ x ∈ segment ℝ p q}

/-- Parameters of the drawing points on the ray of angle `θ`. -/
def hitT (X : Finset Pt) (h : ℝ) (V : Finset Pt) (θ : ℝ) : Set ℝ :=
  {t | 0 < t ∧ rayPt X h θ t ∈ drawing V}

/-- `Hv ⊆ Yout ⊆ X`, and points of `Hv` are pairwise `≥ 1` apart.

TODO: prove.  What's missing: `filter_subset`, `sdiff_subset`, `one_le_dist`.
Acceptance: no `sorry`.  Depends on: `one_le_dist`. Difficulty S. -/
theorem Hv_spec (hX : Normal X) (ρ : ℕ) :
    Hv X ρ ⊆ Yout X ρ ∧ Hv X ρ ⊆ X ∧ ∀ v ∈ Hv X ρ, ∀ q ∈ Hv X ρ, v ≠ q → 1 ≤ dist v q := by
  sorry

/-- The drawing avoids `K′` (every drawing point is within `½` of a vertex of depth `< ρ`, and
depth is 1-Lipschitz, so it has depth `< ρ + ½ = h`).

TODO: prove.
What's missing: a point of a unit segment is within `½` of an endpoint (`segment` as convex
combination); `Yout` gives `w` with `|v − w| > Δ₂ − ρ`; `not_mem_Kin_of_far`.
Acceptance: no `sorry`.  Depends on: `not_mem_Kin_of_far`. Difficulty S–M. -/
theorem drawing_not_mem_Kin (ρ : ℕ) {x : Pt} (hx : x ∈ drawing (Hv X ρ)) :
    x ∉ Kin X (hh ρ) := by
  sorry

/-- The drawing lies in `K` and is compact.

TODO: prove.
What's missing: `Yset_subset_KBall`, `KBall_convex` (`Convex.segment_subset`); a finite union of
segments is compact (`isCompact_segment`-type, `Set.Finite.isCompact_biUnion`).
Acceptance: no `sorry`.  Depends on: `Yset_subset_KBall`, `KBall_convex`, `Hv_spec`.
Difficulty S–M. -/
theorem drawing_subset_KBall_isCompact (hX : Normal X) (ρ : ℕ) :
    drawing (Hv X ρ) ⊆ KBall X ∧ IsCompact (drawing (Hv X ρ)) := by
  sorry

/-- **(P1) unit edges do not cross.**  Two different unit segments with ends in a `1`-separated set
meet only in a common endpoint.

Why true: an interior common point `x` would give (crossing) `|pp'| + |qq'| < |pq| + |p'q'| = 2`
by the strict triangle inequality, or (collinear overlap, or an endpoint inside the other segment)
an endpoint within distance `< 1` of another endpoint.

TODO: prove.
Acceptance: no `sorry`.  Depends on: triangle inequality, `segment` algebra. Difficulty M. -/
theorem unit_segment_inter {V : Finset Pt} (hV : ∀ v ∈ V, ∀ q ∈ V, v ≠ q → 1 ≤ dist v q)
    {p q p' q' : Pt} (hp : p ∈ V) (hq : q ∈ V) (hp' : p' ∈ V) (hq' : q' ∈ V)
    (hpq : dist p q = 1) (hpq' : dist p' q' = 1) (hne : s(p, q) ≠ s(p', q'))
    {x : Pt} (hx : x ∈ segment ℝ p q) (hx' : x ∈ segment ℝ p' q') :
    (x = p ∨ x = q) ∧ (x = p' ∨ x = q') := by
  sorry

/-- A hit ray has a first hit (the drawing is compact and avoids `K′`, so `hitT θ` is closed and
bounded below by a positive number).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `drawing_subset_KBall_isCompact`, `drawing_not_mem_Kin`, `suppPt_spec`. Difficulty M. -/
theorem exists_first_hit (hC : CoreHyp X (hh ρ)) {θ : ℝ}
    (hne : (hitT X (hh ρ) (Hv X ρ) θ).Nonempty) :
    ∃ t, IsLeast (hitT X (hh ρ) (Hv X ρ) θ) t := by
  sorry

/-- **(V1) the first-hit edge is constant between events.**  On an open angle interval (of length
`≤ 2π`) containing no vertex angle, either all rays escape or all first hits lie on one unit
edge `[p, q]`, oriented so that `ν` increases from `p` to `q` (`det2(ν, q − p) > 0`).

Why true (REF_core §2.3): an edge meets `r_θ` iff `θ` is in its (closed) `ν`-range, whose ends are
vertex angles, so the set of edges met is constant; two edges met by all these rays cannot swap
their order along the rays (continuity of the hit parameters + IVT would give a common
non-vertex point, excluded by `unit_segment_inter`).  The orientation is `nu_segment` (case b; a
radial edge is met by one ray only).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `nu_segment`, `unit_segment_inter`, `exists_first_hit`, `rayPt_coords`.
Difficulty L (≈ 400 lines). -/
theorem first_hit_const (hC : CoreHyp X (hh ρ)) {α β : ℝ} (hαβ : α < β) (hβ : β ≤ α + 2 * π)
    (hfree : ∀ v ∈ Hv X ρ, ∀ θ ∈ Set.Ioo α β, dirVec θ ≠ nuVec X (hh ρ) v) :
    (∀ θ ∈ Set.Ioo α β, hitT X (hh ρ) (Hv X ρ) θ = ∅) ∨
    ∃ p ∈ Hv X ρ, ∃ q ∈ Hv X ρ, dist p q = 1 ∧
      (∀ θ ∈ Set.Icc α β, 0 < det2 (dirVec θ) (q - p)) ∧
      ∀ θ ∈ Set.Ioo α β, ∃ t, IsLeast (hitT X (hh ρ) (Hv X ρ) θ) t ∧
        rayPt X (hh ρ) θ t ∈ segment ℝ p q := by
  sorry

/-- **(V3.1) with the compactness sentence (G4).**  If the first hit `B` of the ray `θ₀` is not a
vertex, it is an interior point of a unique unit edge `[p, q]`, and the first hits of all nearby
rays (both sides) lie on that edge.

Why true (REF_core §2.3): if drawing points `x_k ∈ r_{θ_k}`, `θ_k → θ₀`, were below the hit point
of `[p, q]`, a subsequence on one edge `e′` converges to a drawing point of `r_{θ₀}` not beyond
`B`, i.e. to `B`, so `e′ = [p, q]` (`B` is interior to `[p, q]`, `unit_segment_inter`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exists_first_hit`, `unit_segment_inter`, `drawing_subset_KBall_isCompact`,
`nu_segment`. Difficulty L (≈ 300 lines). -/
theorem foot_edge (hC : CoreHyp X (hh ρ)) {θ₀ t₀ : ℝ}
    (hB : IsLeast (hitT X (hh ρ) (Hv X ρ) θ₀) t₀) (hBV : rayPt X (hh ρ) θ₀ t₀ ∉ Hv X ρ) :
    ∃ p ∈ Hv X ρ, ∃ q ∈ Hv X ρ, dist p q = 1 ∧ rayPt X (hh ρ) θ₀ t₀ ∈ segment ℝ p q ∧
      0 < det2 (dirVec θ₀) (q - p) ∧
      ∃ ε > 0, ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∃ t, IsLeast (hitT X (hh ρ) (Hv X ρ) θ) t ∧
        rayPt X (hh ρ) θ t ∈ segment ℝ p q := by
  sorry

/-! ## The visible path as finite data -/

/-- The visible path: `M` events with angles `ev i` (`ev M = ev 0 + 2π`), for each interval a hit
flag and the oriented first-hit edge `[eP i, eQ i]`, and at each event the points `L i`, `B i`,
`R i`.  All functions are read for indices `< M` (and `ev M`). -/
structure VisPath where
  M : ℕ
  ev : ℕ → ℝ
  hit : ℕ → Bool
  eP : ℕ → Pt
  eQ : ℕ → Pt
  L : ℕ → Pt
  B : ℕ → Pt
  R : ℕ → Pt

namespace VisPath

/-- Cyclic predecessor of an event index. -/
def prev (P : VisPath) (i : ℕ) : ℕ := if i = 0 then P.M - 1 else i - 1

/-- Relative angle `ψ(e_i, θ) = ang(dirVec θ, eQ i − eP i) ∈ [0, π]`. -/
def psiE (P : VisPath) (i : ℕ) (θ : ℝ) : ℝ := ang (dirVec θ) (P.eQ i - P.eP i)

/-- The corner occurrences at event `i`: `L_i` (if `e_{i−1}` is real and `L_i ≠ B_i`; out: inward
jump, `ψ = π`), `B_i` (in: `e_{i−1}` or `π`; out: `e_i` or `0`; an *end* if a side is virtual),
`R_i` (if `e_i` is real and `R_i ≠ B_i`; in: outward jump, `ψ = 0`).  Repeated points are merged
only with `B_i`; the dip `L_i = R_i ≠ B_i` gives two occurrences of one point (G1). -/
def corners (P : VisPath) (i : ℕ) : List Occ :=
  (if P.hit (P.prev i) = true ∧ P.L i ≠ P.B i then
      [⟨P.L i, P.ev i, P.psiE (P.prev i) (P.ev i), π, false⟩] else []) ++
  [⟨P.B i, P.ev i,
    (if P.hit (P.prev i) = true ∧ P.L i = P.B i then P.psiE (P.prev i) (P.ev i) else π),
    (if P.hit i = true ∧ P.R i = P.B i then P.psiE i (P.ev i) else 0),
    (!P.hit (P.prev i) || !P.hit i)⟩] ++
  (if P.hit i = true ∧ P.R i ≠ P.B i then
      [⟨P.R i, P.ev i, 0, P.psiE i (P.ev i), false⟩] else [])

/-- All corner occurrences, event by event. -/
def allCorners (P : VisPath) : List Occ := (List.range P.M).flatMap P.corners

/-- Vertex occurrences (feet removed). -/
def vOcc (P : VisPath) (V : Finset Pt) : List Occ :=
  P.allCorners.filter (fun o => decide (o.pt ∈ V))

/-- `J`: the number of escape intervals. -/
def J (P : VisPath) : ℕ := ((Finset.range P.M).filter (fun i => P.hit i = false)).card

/-- Event `i` starts a piece: `I_i` is hit, and `I_{i−1}` is not, or there is a vertex corner. -/
def IsStart (P : VisPath) (V : Finset Pt) (i : ℕ) : Prop :=
  P.hit i = true ∧ (P.hit (P.prev i) = false ∨ ∃ o ∈ P.corners i, o.pt ∈ V)

/-- `n`: the number of pieces. -/
def nP (P : VisPath) (V : Finset Pt) : ℕ := ((Finset.range P.M).filter (P.IsStart V)).card

/-- The geometric meaning of a `VisPath` for the drawing of `V` around `K′ = Kin X h`. -/
structure Valid (P : VisPath) (X : Finset Pt) (h : ℝ) (V : Finset Pt) : Prop where
  M_pos : 0 < P.M
  ev_mono : StrictMonoOn P.ev (Set.Iic P.M)
  ev_wrap : P.ev P.M = P.ev 0 + 2 * π
  /-- every event is the normal angle of a vertex -/
  ev_vertex : ∀ i < P.M, ∃ v ∈ V, dirVec (P.ev i) = nuVec X h v
  /-- every vertex angle is an event -/
  vertex_ev : ∀ v ∈ V, ∃ i < P.M, dirVec (P.ev i) = nuVec X h v
  /-- (V1) first hits on a hit interval lie on the oriented unit edge `e_i` -/
  hit_edge : ∀ i < P.M, P.hit i = true →
    P.eP i ∈ V ∧ P.eQ i ∈ V ∧ dist (P.eP i) (P.eQ i) = 1 ∧
    (∀ θ ∈ Set.Icc (P.ev i) (P.ev (i + 1)), 0 < det2 (dirVec θ) (P.eQ i - P.eP i)) ∧
    ∀ θ ∈ Set.Ioo (P.ev i) (P.ev (i + 1)), ∃ t, IsLeast (hitT X h V θ) t ∧
      rayPt X h θ t ∈ segment ℝ (P.eP i) (P.eQ i)
  /-- escape intervals -/
  escape : ∀ i < P.M, P.hit i = false →
    ∀ θ ∈ Set.Ioo (P.ev i) (P.ev (i + 1)), hitT X h V θ = ∅
  /-- `B_i` is the first hit of the event ray -/
  B_first : ∀ i < P.M, ∃ t, IsLeast (hitT X h V (P.ev i)) t ∧ P.B i = rayPt X h (P.ev i) t
  /-- `L_i` is the point of `e_{i−1}` on the event ray -/
  L_spec : ∀ i < P.M, P.hit (P.prev i) = true → ∃ t, 0 < t ∧ P.L i = rayPt X h (P.ev i) t ∧
    P.L i ∈ segment ℝ (P.eP (P.prev i)) (P.eQ (P.prev i))
  /-- `R_i` is the point of `e_i` on the event ray -/
  R_spec : ∀ i < P.M, P.hit i = true → ∃ t, 0 < t ∧ P.R i = rayPt X h (P.ev i) t ∧
    P.R i ∈ segment ℝ (P.eP i) (P.eQ i)
  /-- (V3.1, G4) a non-vertex first hit is a transversal crossing of one edge -/
  foot : ∀ i < P.M, P.B i ∉ V → P.hit (P.prev i) = true ∧ P.hit i = true ∧ P.L i = P.B i ∧
    P.R i = P.B i ∧ P.eP (P.prev i) = P.eP i ∧ P.eQ (P.prev i) = P.eQ i

end VisPath

open VisPath

/-- **The visible path exists** (Step 2: V1–V3).

Why true: sort the (finitely many, distinct mod `2π`) vertex angles into `ev`; on each interval
apply `first_hit_const` (choose `hit i` and `e_i`); `B_i` from `exists_first_hit`; `L_i`, `R_i`
are the points of `e_{i−1}`, `e_i` on the event ray (their closed `ν`-ranges contain the event);
`foot` is `foot_edge` + uniqueness of the edge through a non-vertex point (`unit_segment_inter`).

TODO: prove.
What's missing: the construction (`Finset.sort` of `(Hv X ρ).image (nuAng …)`, lifting to
`ev M = ev 0 + 2π`), and checking each field.
Acceptance: no `sorry`.
Depends on: `first_hit_const`, `foot_edge`, `exists_first_hit`, `unit_segment_inter`,
`rayPt_coords`, `ray_decomp`, `drawing_not_mem_Kin`. Difficulty L (≈ 400 lines). -/
theorem exists_visPath (hC : CoreHyp X (hh ρ)) (hV : (Hv X ρ).Nonempty) :
    ∃ P : VisPath, P.Valid X (hh ρ) (Hv X ρ) := by
  sorry

/-! ## Pure consequences: turning, counting -/

/-- All relative angles of corners are in `[0, π]` (`ang ∈ [0, π]`).

TODO: prove.  What's missing: unfold `corners`, `InnerProductGeometry.angle_nonneg`,
`angle_le_pi`.
Acceptance: no `sorry`.  Depends on: definitions. Difficulty S. -/
theorem VisPath.psi_mem (P : VisPath) {o : Occ} (ho : o ∈ P.allCorners) :
    (0 ≤ o.ψin ∧ o.ψin ≤ π) ∧ (0 ≤ o.ψout ∧ o.ψout ≤ π) := by
  sorry

/-- Every corner lies on its event ray, off `K′`: `dirVec o.θ = ν(o.pt)`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `Valid.B_first`, `Valid.L_spec`, `Valid.R_spec`, `rayPt_coords`. Difficulty S–M. -/
theorem VisPath.corner_on_ray (hC : CoreHyp X (hh ρ)) {P : VisPath}
    (hP : P.Valid X (hh ρ) (Hv X ρ)) {o : Occ} (ho : o ∈ P.allCorners) :
    o.pt ∉ Kin X (hh ρ) ∧ dirVec o.θ = nuVec X (hh ρ) o.pt := by
  sorry

/-- **Step 3, the turning identity** (telescoping):
`Σ_{all corners} κ = Σ_{i hit} (ev(i+1) − ev i) − πJ`.

Why true: inside event `i` the `κ`'s telescope to `ψout(last) − ψin(first)`, where
`ψout(last) = ψ(e_i, ev i)` or `0`, `ψin(first) = ψ(e_{i−1}, ev i)` or `π`; regroup by intervals
(`prev` is a bijection of `range M`; `dirVec` is `2π`-periodic for `i = 0`), and
`ψ(e_i, ev i) − ψ(e_i, ev(i+1)) = ev(i+1) − ev i` by `ang_dirVec_sub` (`hit_edge`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `ang_dirVec_sub`, `Valid.hit_edge`, `Valid.ev_wrap`. Difficulty M (≈ 200 lines). -/
theorem VisPath.turning_sum {h : ℝ} {V : Finset Pt} {P : VisPath} (hP : P.Valid X h V) :
    (P.allCorners.map Occ.κ).sum =
      ∑ i ∈ (Finset.range P.M).filter (fun i => P.hit i = true), (P.ev (i + 1) - P.ev i)
        - π * P.J := by
  sorry

/-- **Step 3, vertex part**: `Σ_{vertex occurrences} κ ≤ 2π − πJ` (feet have `κ ≥ 0`: an `L`-foot
has `κ = π − ψ ≥ 0`, an `R`-foot `κ = ψ ≥ 0`, a `B`-foot `κ = 0` by `Valid.foot`; and
`Σ_{hit} |I_i| ≤ ev M − ev 0 = 2π`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `turning_sum`, `psi_mem`, `Valid.foot`, `Valid.ev_mono`. Difficulty M. -/
theorem VisPath.turning_vOcc {h : ℝ} {V : Finset Pt} {P : VisPath} (hP : P.Valid X h V) :
    ((P.vOcc V).map Occ.κ).sum ≤ 2 * π - π * P.J := by
  sorry

/-- **(V4), occurrence counting (G1)**: `n + J ≤ m`.  Each escape interval `I_i` and each piece
start `i` carries a vertex occurrence at event `i` (`B_i ∈ V` unless both sides are hit and
`B_i` is a foot, by `Valid.foot`), and distinct events give distinct occurrences.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `Valid.foot`. Difficulty M. -/
theorem VisPath.count_vOcc {h : ℝ} {V : Finset Pt} {P : VisPath} (hP : P.Valid X h V) :
    P.nP V + P.J ≤ (P.vOcc V).length := by
  sorry

/-- At most two ends per escape interval: ends are `B`-corners at events with a virtual side,
and `#{i : ¬hit (prev i)} = #{i : ¬hit i} = J`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: definitions (`prev` is a bijection of `range M`). Difficulty S–M. -/
theorem VisPath.card_end_le (P : VisPath) (V A : Finset Pt) :
    ((P.vOcc V).filter (fun o => o.isEnd && decide (o.pt ∈ A))).length ≤ 2 * P.J := by
  sorry

/-- **G1: wedges of different occurrences of one point are disjoint.**  Occurrences of one point
are at one event (the point determines its ray, `corner_on_ray`; events are distinct mod `2π`);
at one event only the dip `L_i = R_i` repeats a point, and then the wedges
`(θ + π, θ + ψin(L) + π)` and `(θ + ψout(R), θ + π)` are disjoint.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `corner_on_ray`, `Valid.ev_mono`, `Valid.ev_wrap`, `psi_mem`. Difficulty M. -/
theorem VisPath.wedge_disj (hC : CoreHyp X (hh ρ)) {P : VisPath}
    (hP : P.Valid X (hh ρ) (Hv X ρ)) :
    (P.vOcc (Hv X ρ)).Pairwise (fun o o' => o.pt = o'.pt → Disjoint o.wedge o'.wedge) := by
  sorry

/-- The ends have distinct points (only `B`-corners are ends, one per event), so for `α ≥ 0`
`Σ_{ends at A} α(pt) ≤ Σ_{a ∈ A ∩ V} α a`.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `corner_on_ray`, `Valid.ev_mono`. Difficulty M. -/
theorem VisPath.sum_alpha_end (hC : CoreHyp X (hh ρ)) {P : VisPath}
    (hP : P.Valid X (hh ρ) (Hv X ρ)) (A : Finset Pt) (α : Pt → ℝ) (hα : ∀ a, 0 ≤ α a) :
    (((P.vOcc (Hv X ρ)).filter (fun o => o.isEnd && decide (o.pt ∈ A))).map
        (fun o => α o.pt)).sum ≤ ∑ a ∈ A ∩ Hv X ρ, α a := by
  sorry

end

end Erdos132Main

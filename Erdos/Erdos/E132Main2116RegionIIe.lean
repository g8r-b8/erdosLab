import Erdos.E132Main2116Defs

/-!
# Erdős Problem 132, `21/16` — rungs in Region II: `e(S) ≤ s + p/2 + C` (§11.1, Theorem IIe)

Paper §11.1: **lem:IIrung**, **lem:IIZ**, **lem:IIord**, gaps and **lem:IIarc**,
**lem:IIdisj**, **thm:IIBC** (break count `e(S) ≤ s + U + 70 + C_bad`), **lem:IIcons**, and the
proof of **thm:IIe** (`2U ≤ p + 34`).  Standing hypotheses: `Normal X` (so `Δ₂ ≥ 10⁴`) and
`√3/2 + 3β ≤ τ ≤ 1`; `F` is any direction field.  `p = |Q2 X|` is the number of **all** points
of `S` of `Δ₂`-degree `1` (paper lem:IIlp), the same `Q` as in `VS_weighted`.

Formalisation of the gap structure (no graph components needed):
* `RowR F a b` (pure right T-step, `E132MainRegions`) is a partial injective function
  (`rowR_fun`, `rowR_inj`); walks are `Relation.TransGen`/`ReflTransGen` of it.
* `NextRung X F vA zA vB zB`: `(vB, zB)` is the next good rung after `(vA, zA)` along the D-row
  (the gap `(A, B)` of the paper): `zB` is reached from `zA` by pure right D-row T-steps, and no
  rung D-end lies strictly between.
* `walkPt F vA vB b`: `b` is on the K-row walk from `vA` before `vB` (the half-open arc
  `[v_A, v_B)` of lem:IIdisj).
* `unbrokenK X F`: K-ends `vA` of rungs whose gap is **unbroken** (the K-walk from `vA`
  reaches `vB`); `U = |unbrokenK X F|` (each K-end carries at most one rung, `R1_v`).

The Region II ingredients reused: `RowR`, `RungM`, `R1_v`, `R1_z`, `rung_offset`, `lemmaB`,
`lemmaC`, `card_typeOne_le_five`, `breaks`, `card_tEdges_add_breaks_le`, `card_mixedT_le`,
`card_bad_le`, `good_subset_T_union_rungs`, `card_good_add_bad`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Gaps -/

/-- The gap `(A, B)`: `B = (vB, zB)` is the next good rung after `A = (vA, zA)` along the pure
D-row (paper §11.1 "Gaps"). -/
def NextRung (X : Finset Pt) (F : DirField X) (vA zA vB zB : Pt) : Prop :=
  RungM X F vA zA ∧ RungM X F vB zB ∧ Relation.TransGen (RowR F) zA zB ∧
    ∀ v z, RungM X F v z → Relation.TransGen (RowR F) zA z → Relation.TransGen (RowR F) z zB →
      False

/-- `b` lies on the pure right K-row walk from `vA`, before `vB` (the half-open arc
`[v_A, v_B)`). -/
def walkPt {X : Finset Pt} (F : DirField X) (vA vB b : Pt) : Prop :=
  Relation.ReflTransGen (RowR F) vA b ∧ ¬ Relation.ReflTransGen (RowR F) vB b

/-- K-ends of the rungs `A` whose gap `(A, B)` is **unbroken**: the pure right K-row walk from
`v_A` reaches `v_B`. -/
def unbrokenK (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (Sset X).filter (fun v => ∃ z vB zB, NextRung X F v z vB zB ∧ Relation.TransGen (RowR F) v vB)

/-- The **sign** `ς` of a rung (paper lem:IIrung(a)), up to a global convention: the side of
`u_v` on which `z` lies (`+1` if `σ = 0`). -/
def rungSign {X : Finset Pt} (F : DirField X) (v z : Pt) : ℝ :=
  if 0 ≤ det2 (F.u v) (z - v) then 1 else -1

/-! ## Rung-carrying D-row components (lem:IIrung, lem:IIZ, lem:IIord) -/

/-- **lem:IIZ(a)**: the component of the D-end `z` of a good rung `(v, z)` in the graph of pure
D-row T-edges lies on `C(w_v, Δ)`.

TODO: prove.
What's missing: paper proof of lem:IIZ(a).  `|z w| = Δ` (`IsRung`), `ŵ = (w − z)/Δ` is within
`arcsin(1/Δ)` of `u_v` (law of sines in the triangle `v z w`) and `u_v` within `β` of `u_z`
(good rung); a T-neighbour `z₁` of `z` has `η = ⟨z₁ − z, ŵ⟩ < 0.0201 < t`, so `|z₁ w| = Δ` by
`lemmaB` (threshold `≥ t` since `t ≤ 1`).  Induct along the component as in `lem:Bprime`
(an interior vertex of `Z ∩ C(w, Δ)` has its normal cone within `arcsin β` of `u`, and its
other T-neighbour is again on the circle); use `Relation.ReflTransGen.head_induction_on`.
Acceptance: no `sorry`.
Depends on: `lemmaB`, `rung_offset`, `RungM.ang`, `IsTEdge`, `R2`-type estimates.
Difficulty M–L. -/
theorem IIZ_circle (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v z z' : Pt} (h : RungM X F v z)
    (hz : Relation.ReflTransGen (fun a b => RowR F a b ∨ RowR F b a) z z') :
    dist z' (F.partner v) = diam X := by
  sorry

/-- **lem:IIZ(b)**: all good rungs whose D-ends lie in one pure D-row component have the same
chosen partner `w` (the *centre*).

TODO: prove.
What's missing: if `z' = z` then `v' = v` (`R1_z`).  Otherwise `z'` has a T-neighbour `z₁′` in
the component; by `IIZ_circle` for both rungs, `z′, z₁′ ∈ C(w, Δ) ∩ C(w_{v'}, Δ)`; two distinct
circles of radius `Δ` with centres in `X` (distance `≤ Δ`) meet in points `≥ √3Δ > 1` apart,
contradicting `|z′ z₁′| = 1`.
Acceptance: no `sorry`.
Depends on: `IIZ_circle`, `R1_z`, `two_circles`. Difficulty S–M. -/
theorem IIZ_centre (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v z v' z' : Pt} (h : RungM X F v z) (h' : RungM X F v' z')
    (hz : Relation.ReflTransGen (fun a b => RowR F a b ∨ RowR F b a) z z') :
    F.partner v' = F.partner v := by
  sorry

/-- **lem:IIord**: rungs of one component are in the same (counterclockwise) order about the
centre at their K-ends as at their D-ends.

TODO: prove.
What's missing: paper proof of lem:IIord.  `zB` is counterclockwise of `zA` on `C(w, Δ)`
(right T-steps are counterclockwise, `IIZ_circle`; total angle `≤ π/3`), `w_{vB} = w`
(`IIZ_centre`), and each rung is the graph of a monotone function of `|x − w|`
(lem:IIrung(c), from `rung_offset`); if the K-ends were in the opposite order the segments
would cross at an interior point, and the triangle inequality gives `|vA vB| < 1` or
`|zA zB| < 1` (or, collinear, `vA = vB`), contradicting `one_le_dist` / `R1_z`.
Acceptance: no `sorry`.
Depends on: `IIZ_circle`, `IIZ_centre`, `rung_offset`, `R1_z`, `one_le_dist`. Difficulty M. -/
theorem IIord (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {vA zA vB zB : Pt} (hA : RungM X F vA zA) (hB : RungM X F vB zB)
    (h : Relation.TransGen (RowR F) zA zB) :
    0 < det2 (vA - F.partner vA) (vB - F.partner vA) := by
  sorry

/-! ## The arcs of the gaps (lem:IIarc, lem:IIdisj) -/

/-- **lem:IIarc**: the K-row walk from `vA` before `vB` runs on `C(w, Δ₂) ∩ ∂K` (`w` the
centre), stays in the K-row, and its points other than `vA` (relative interior points of the
arc `γ_AB`) have `Δ₂`-degree `1`.

TODO: prove.
What's missing: paper proof of lem:IIarc and of "Interior walk points" in the proof of thm:IIe.
(a) `γ_AB ⊆ ∂K` (the arc between two points of `K ∩ C(w, Δ₂)` less than `π` apart,
`IIord` + (IIgapangle)); (b) as `lem:rigid`: a pure right T-neighbour of a walk point of
`γ_AB ∖ {vB}` is the point of `γ_AB` at angle `α₂` counterclockwise (`w_{vA} = w` by
`IIZ_centre`), and the walk cannot pass `vB`.  A relative interior point `b` of `γ_AB` with a
second partner `w′` would be an endpoint of the arc `C(w, Δ₂) ∩ D̄(w′, Δ₂) ⊇ γ_AB`; so
`deg2 b = 1`.
Acceptance: no `sorry`.
Depends on: `IIZ_circle`, `IIZ_centre`, `IIord`, `rung_offset`, `RowR`, `IsSideT`,
`ball_polygon_b`, `mem_KBall`. Difficulty L. -/
theorem IIarc_walk (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {vA zA vB zB b : Pt} (h : NextRung X F vA zA vB zB)
    (hb : walkPt F vA vB b) :
    dist b (F.partner vA) = dist2 X ∧ b ∉ Dset X ∧ (b ≠ vA → b ∈ Q2 X) := by
  sorry

/-- **lem:IIdisj** (half-open arcs): the walks `[v_A, v_B)` of distinct gaps are disjoint.

TODO: prove.
What's missing: paper proof of lem:IIdisj (same component: `IIord`; different components with
the same centre: the angular ranges are `≥ α₁` apart and `2φ_τ < α₁`; different centres: a
common point would be a common endpoint, i.e. a rung K-end, whose component has centre
`w_x`), with `IIarc_walk` placing the walk points on the arcs.
Acceptance: no `sorry`.
Depends on: `IIarc_walk`, `IIord`, `IIZ_circle`, `IIZ_centre`, `R1_v`, `R1_z`,
`rung_offset`, `alpha1`. Difficulty L. -/
theorem IIdisj_walk (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {vA zA vB zB vA' zA' vB' zB' b : Pt} (h : NextRung X F vA zA vB zB)
    (h' : NextRung X F vA' zA' vB' zB') (hne : vA ≠ vA') (hb : walkPt F vA vB b)
    (hb' : walkPt F vA' vB' b) : False := by
  sorry

/-! ## Break count and signs (thm:IIBC, lem:IIcons) -/

/-- **thm:IIBC** (rung form): `ρ ≤ B + U + 2`, where `B = |breaks|` (points of `S` without a
pure right T-neighbour) and `U = |unbrokenK|`.  With `e_T + B ≤ s + #mixed`
(`card_tEdges_add_breaks_le`) this is `e(S) ≤ s + U + #mixed + 2 + C_bad`.

TODO: prove.
What's missing: paper proof of thm:IIBC.  Map each good rung `A = (vA, zA)` (distinct rungs
have distinct K-ends, `R1_v`): if `A` has no `NextRung`, to the last vertex of the pure right
D-row walk from `zA` (a D-break; the walk is a path by `IIZ_circle`/lem:IIZ(a) and finite;
distinct components give distinct last vertices); if `(A, B)` is a broken gap, to the point
where the K-row walk from `vA` stops (a K-break in `walkPt F vA vB`, lem:IIarc(b); distinct by
`IIdisj_walk`); otherwise `vA ∈ unbrokenK`.  K-breaks are not in `D`, D-breaks are, so the
map into `breaks ⊔ unbrokenK` is injective.
Acceptance: no `sorry`.
Depends on: `IIZ_circle`, `IIarc_walk`, `IIdisj_walk`, `rowR_fun`, `rowR_inj`, `R1_v`, `R1_z`,
`card_le_card_of_injOn`. Difficulty L. -/
theorem IIBC (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    (rungs X F).card ≤ (breaks X F).card + (unbrokenK X F).card + 2 := by
  sorry

/-- **lem:IIcons(a)**: at most `6` unbroken gaps have equal signs.

TODO: prove.
What's missing: paper proof of lem:IIcons(a): with equal signs (IIstar) reads `jα₂ = kα₁`, so
the arc `γ_AB` has angle `> 0.99999` (`1/α₁ − 1/α₂ ≤ t + 1/(23Δ₂)`, `t ≤ 1`, `Δ₂ ≥ 10⁴`) and
length `> 0.99999 Δ₂`; the half-open arcs are disjoint (`IIdisj_walk`) inside `∂K`, of
perimeter `≤ 2πΔ₂`; `2π/0.99999 < 6.3`.
Acceptance: no `sorry`.
Depends on: `IIarc_walk`, `IIdisj_walk`, `rung_offset`, `alpha1`, `alpha2`, perimeter bound
(`card_le_arcLength`-type or `turning_sum_le`). Difficulty M–L. -/
theorem IIcons_a (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    ((unbrokenK X F).filter (fun v => ∃ z vB zB, NextRung X F v z vB zB ∧
      Relation.TransGen (RowR F) v vB ∧ rungSign F v z = rungSign F vB zB)).card ≤ 6 := by
  sorry

/-- **lem:IIcons(b)**: at most `24` rungs `B` are shared by two unbroken gaps `(A, B)`, `(B, C)`
(counted by their K-ends `v_B`).

TODO: prove.
What's missing: paper proof of lem:IIcons(b): if one of the two gaps has equal signs, `B` is
one of `≤ 2·6` rungs (`IIcons_a`); otherwise the signs alternate, adding (IIstar) gives
`(j + j′)α₂ = (k + k′)α₁`, and the arc `[v_A, v_C)` has length `> 0.99999Δ₂`; each point of
`∂K` is in at most two such arcs: `≤ 4π/0.99999 < 12.6`.
Acceptance: no `sorry`.
Depends on: `IIcons_a`, `IIarc_walk`, `IIdisj_walk`, `rung_offset`, `alpha1`, `alpha2`.
Difficulty M–L. -/
theorem IIcons_b (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    ((unbrokenK X F).filter (fun v => ∃ vA zA z, NextRung X F vA zA v z ∧
      vA ∈ unbrokenK X F)).card ≤ 24 := by
  sorry

/-- **Proof of thm:IIe, counting**: `2U ≤ p + 34`.

TODO: prove.
What's missing: paper proof of thm:IIe ("Endpoints", "Interior walk points", "Counting").
Each unbroken gap `(A, B)` has `≥ 2` points `v_A = v₀, …, v_j = v_B` on its closed walk; all
are in `Q2` except type-(i) endpoints (`≤ 5` vertices, `card_typeOne_le_five`, each in `≤ 2`
gaps: `≤ 10` pairs); type-(ii) K-ends are in no gap (`lemmaC`: their D-end has no T-neighbour);
interior walk points are in `Q2` (`IIarc_walk`).  Closed walks of distinct gaps share only a
common `v_B` (`IIdisj_walk`), which happens for `≤ 24` rungs (`IIcons_b`).  So
`2U − 10 ≤ Σ_gaps |Q2 ∩ walk| ≤ p + 24`.
Acceptance: no `sorry`.
Depends on: `IIarc_walk`, `IIdisj_walk`, `IIcons_b`, `card_typeOne_le_five`, `lemmaC`,
`R1_v`, `R1_z`. Difficulty L. -/
theorem two_U_le (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) : 2 * (unbrokenK X F).card ≤ (Q2 X).card + 34 := by
  sorry

/-! ## Theorem IIe -/

/-- **thm:IIe**: in Region II with `τ ≤ 1`, `e(S) ≤ s + p/2 + cIIe`, `p = |Q2|`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits `IIBC`, `two_U_le`).
Depends on: `card_good_add_bad`, `good_subset_T_union_rungs`, `card_tEdges_add_breaks_le`,
`card_mixedT_le`, `card_bad_le`, `IIBC`, `two_U_le`. -/
theorem regionIIe (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    (eS X : ℝ) ≤ (Sset X).card + 1 / 2 * (Q2 X).card + cIIe := by
  have hτ : 2 * beta < tau X := by
    have : (0 : ℝ) < √3 / 2 := by positivity
    unfold beta at hτ₁ ⊢; linarith
  have hsub := good_subset_T_union_rungs hX F hτ
  have hg := (card_le_card hsub).trans (card_union_le _ _)
  have hTB := card_tEdges_add_breaks_le hX F
  have hBC := IIBC hX F hτ₁ hτ₂
  have hU := two_U_le hX F hτ₁ hτ₂
  have hmix := card_mixedT_le hX F hτ₁
  have hbad := card_bad_le hX F
  have hgood : ((good X F).card : ℝ) + (breaks X F).card ≤
      (Sset X).card + (mixedT X F).card + (unbrokenK X F).card + 2 + (breaks X F).card := by
    have : (good X F).card + (breaks X F).card ≤
        (Sset X).card + (mixedT X F).card + (unbrokenK X F).card + 2 + (breaks X F).card := by
      omega
    exact_mod_cast this
  have hU' : 2 * ((unbrokenK X F).card : ℝ) ≤ (Q2 X).card + 34 := by exact_mod_cast hU
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  unfold cIIe
  linarith

end

end Erdos132Main

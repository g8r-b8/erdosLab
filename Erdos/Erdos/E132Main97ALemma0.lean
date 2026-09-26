import Erdos.E132Main97Defs

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A3: Lemma 0 (`int K′ ≠ ∅`)

`L97_reports/RouteA_visiblepath_report.md` §1 "Lemma 0", refereed in `REF_core_report.md` §2.1.
Under `|A| > 1000h` some point of `K` has depth `> h`, i.e. the inner parallel body
`K′ = {depth ≥ h}` has nonempty interior.  No Steinhagen, no perimeter:

1. a point `o` of maximal depth `r ≤ h` has active normals with `0` in their convex hull
   (first-order increase of a minimum of finitely many smooth functions), so by Carathéodory in the
   plane `K` lies in a strip of width `2r` or in a triangle of inradius `r`, whose smallest altitude
   is `≤ 3r`: `K` lies in a strip of width `3h` (`shallow_strip`);
2. Lemma F, steps 1–9 (chord inequality only): `diam K ≤ 100·width` (`lemmaF_diam`);
3. the ℓ¹ chain count on the upper and lower boundary graphs: `|A| ≤ 2L + 4w + 10`
   (`card_A_le_strip`);
4. `600h + 12h + 10 < 1000h` for `h ≥ 3/2` (`exists_deep`, assembled here).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- `o` has depth `> h`: every disc centre is closer than `Δ₂ − h`. -/
def IsDeep (X : Finset Pt) (h : ℝ) (o : Pt) : Prop := ∀ w ∈ X, dist o w < dist2 X - h

/-- Non-diametral points lie in `K`: every distance from a point of `Y = X ∖ D` is `≤ Δ₂`.

TODO: prove.
What's missing: for `y ∈ X ∖ D` and `w ∈ X`, `dist y w ∈ distSetS X` (or `= 0`), `≠ diam X` (else
`y ∈ D`), hence `≤ dist2 X` (`dist2` is the largest distance `< diam`; `le_diam`,
`Finset.le_max'`); `mem_KBall`.
Acceptance: no `sorry`.
Depends on: `mem_KBall`, `dist_le_diam`, definitions of `dist2`, `Dset`. Difficulty S–M. -/
theorem Yset_subset_KBall (hX : Normal X) : (Yset X : Set Pt) ⊆ KBall X := by
  sorry

/-- `A ⊆ Y` (both remove `D`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem Aset_subset_Yset : Aset X ⊆ Yset X := by
  intro a ha
  obtain ⟨haS, haD⟩ := mem_sdiff.1 ha
  exact mem_sdiff.2 ⟨(mem_filter.1 haS).1, haD⟩

/-- Each `a ∈ A` lies on a circle `C(w, Δ₂)`, `w ∈ X`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `mem_partners`. Difficulty S. -/
theorem exists_partner_of_mem_Aset {a : Pt} (ha : a ∈ Aset X) :
    ∃ w ∈ X, dist a w = dist2 X := by
  obtain ⟨haS, -⟩ := mem_sdiff.1 ha
  obtain ⟨-, w, hw⟩ := mem_filter.1 haS
  obtain ⟨hwX, -, hd⟩ := Defs.mem_partners.1 hw
  exact ⟨w, hwX, hd⟩

/-- **Lemma 0, step 1–4 of the report (strip).**  If no point is `h`-deep (every point has depth
`≤ h`) and `K ≠ ∅`, then `K` lies in a strip of width `3h`.

Why true: `depth` is continuous and `K` compact, so a point `o` of maximal depth `r ∈ [0, h]`
exists; the active centres `w` (`|o − w| = Δ₂ − r`) give unit vectors `u_w = (o − w)/|o − w|` with
`0 ∈ conv{u_w}` (else `o + εd` is deeper); by Carathéodory in `ℝ²`, `0` is in the hull of two
antipodal `u_w` (then `K` is in the strip `|(x − o)·u| ≤ r`) or of three (then `K` lies in the
triangle `⋂ {(x − o)·u_w ≤ r}` with incircle `D(o, r)`, whose smallest altitude
`r(a + b + c)/max ≤ 3r`).  In both cases a strip of width `≤ 3r ≤ 3h`.
(Correct, REF_core §2.1.)

TODO: prove.
What's missing: existence of the maximum (`IsCompact.exists_isMaxOn`, depth as a finite `min` of
continuous functions), the first-order argument, planar Carathéodory for unit vectors, the
inradius–altitude inequality.
Acceptance: no `sorry`.
Depends on: `KBall_isCompact`, `mem_KBall`. Difficulty L (≈ 400 lines). -/
theorem shallow_strip (hX : Normal X) {h : ℝ} (hh : 0 ≤ h) (hne : (KBall X).Nonempty)
    (hno : ∀ o, ¬ IsDeep X h o) :
    ∃ u : Pt, ‖u‖ = 1 ∧ ∃ c : ℝ, ∀ x ∈ KBall X, |inner ℝ x u - c| ≤ 3 * h / 2 := by
  sorry

/-- **Lemma F** (angle_R6 §5.2, steps 1–9; chord inequality only): if `K` lies in a strip of width
`wd` then `diam K ≤ 100·wd`.

Why true: the minimal width `w₀ ≤ wd`; Lemma F gives `diam K ≤ 100 w₀` when `Δ ≤ 1.94Δ₂` (steps
1–9; step 9 covers `w₀ > 0.02Δ₂` via `diam K ≤ 2Δ₂`).  If `K` has at most one point the claim is
trivial; `K` is never a nondegenerate segment (it is an intersection of discs of radius `Δ₂` with
at least two distinct centres).  (Re-checked in REF_core §1(a).)

TODO: prove.
What's missing: steps 2–8 of Lemma F with the given strip direction in place of the minimal-width
direction (the proof only uses that `K` is in the strip), the numeric step 8.
Acceptance: no `sorry`.
Depends on: `mem_KBall`, `Normal.nondeg`. Difficulty M–L (≈ 250 lines). -/
theorem lemmaF_diam (hX : Normal X) {u : Pt} (hu : ‖u‖ = 1) {c wd : ℝ} (hwd : 0 ≤ wd)
    (hstrip : ∀ x ∈ KBall X, |inner ℝ x u - c| ≤ wd / 2) :
    ∀ x ∈ KBall X, ∀ y ∈ KBall X, dist x y ≤ 100 * wd := by
  sorry

/-- **ℓ¹ chain count** (report Lemma 0, step 6).  If `K` lies in a strip of width `wd` (direction
`u`) and has diameter `≤ L`, then `|A| ≤ 2L + 4wd + 10`.

Why true: `A ⊆ ∂K` and `K` is strictly convex, so `A` splits into points of the upper and of the
lower boundary graph over the axis `perp u`; along each graph, sorted by abscissa,
`Σ|Δx| ≤ L`, `Σ|Δy| ≤ 2wd` (a concave/convex graph is monotone on two pieces), and each step has
`|Δx| + |Δy| ≥ dist ≥ 1` (`minDist = 1`).  So `|A| ≤ 2(L + 2wd + 1)`.

TODO: prove.
What's missing: the upper/lower split (a point `a ∈ A` with `⟪n_a, u⟫ ≥ 0` is on the upper graph,
where `n_a = (a − w)/Δ₂`, `w` a `Δ₂`-partner; every point of `K` on the vertical line through `a`
has `⟪·, u⟫ ≤ ⟪a, u⟫`), monotonicity pieces, and the chain sum.
Acceptance: no `sorry`.
Depends on: `exists_partner_of_mem_Aset`, `Yset_subset_KBall`, `one_le_dist`. Difficulty M–L
(≈ 300 lines). -/
theorem card_A_le_strip (hX : Normal X) {u : Pt} (hu : ‖u‖ = 1) {c wd L : ℝ} (hwd : 0 ≤ wd)
    (hstrip : ∀ x ∈ KBall X, |inner ℝ x u - c| ≤ wd / 2)
    (hdiam : ∀ x ∈ KBall X, ∀ y ∈ KBall X, dist x y ≤ L) :
    ((Aset X).card : ℝ) ≤ 2 * L + 4 * wd + 10 := by
  sorry

/-- **Lemma 0.**  If `h ≥ 3/2` and `|A| > 1000h`, some point is `h`-deep (`int K′ ≠ ∅`).

Proved (assembly): otherwise `shallow_strip` gives a strip of width `3h`, `lemmaF_diam` gives
`diam K ≤ 300h`, and `card_A_le_strip` gives `|A| ≤ 600h + 12h + 10 < 1000h`.
Acceptance: no `sorry` (modulo dependencies).
Depends on: `shallow_strip`, `lemmaF_diam`, `card_A_le_strip`, `Yset_subset_KBall`. Difficulty —
(assembly). -/
theorem exists_deep (hX : Normal X) {h : ℝ} (hh : 3 / 2 ≤ h)
    (hA : 1000 * h < (Aset X).card) : ∃ o, IsDeep X h o := by
  by_contra hno
  have hno' : ∀ o, ¬ IsDeep X h o := fun o ho => hno ⟨o, ho⟩
  have hAne : (Aset X).Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < (Aset X).card := by linarith
    exact_mod_cast this
  obtain ⟨a, ha⟩ := hAne
  have hKne : (KBall X).Nonempty :=
    ⟨a, Yset_subset_KBall hX (Aset_subset_Yset ha)⟩
  obtain ⟨u, hu, c, hstrip⟩ := shallow_strip hX (by linarith) hKne hno'
  have hstrip' : ∀ x ∈ KBall X, |inner ℝ x u - c| ≤ 3 * h / 2 := hstrip
  have hdiam := lemmaF_diam hX hu (wd := 3 * h) (by linarith) hstrip'
  have hcard := card_A_le_strip hX hu (wd := 3 * h) (L := 100 * (3 * h)) (by linarith) hstrip' hdiam
  linarith

end

end Erdos132Main

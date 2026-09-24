import Erdos.E132Main15Defs

/-!
# Erdős Problem 132, `15/11` theorem — Theorem N1 (the R-neighbour lemma)

**Theorem N1** (`angle_R4.md` §5.1, Appendix A.4): all but `O(1)` points `y ∈ R` have `m_y ≤ 4`,
hence `deg y + m_y ≤ 10`, hence (with the exact identity) `μ(δ) ≤ e(S) + 5r + C`.

## Formulation (deviation from the paper, by design)

The paper works with the boundary arc `γ_y` of `∂K` of arc length `≤ 232` around the nearest
boundary point.  Convex-curve arc length is not available (the `54/37` formalisation avoided it,
see `E132ConvexCurve.lean`), so we use a **Euclidean-local** version with the same three cases:

* **flat** (`IsFlatAt X y`): all unit outer normals at boundary points of `K` in `B̄(y, 1)` lie
  within `1/4` (in norm) of one unit vector `n`.  Then every `S`-neighbour `q` of `y` has
  `(q − y)·n > −1/4` (the segment `[y, q]` leaves `K` at a boundary point whose normal `ν`
  has `(q − y)·ν > 0`), i.e. lies in an open arc of length `2 arccos(−1/4) < 240°`, which holds at
  most 4 points pairwise `60°` apart.  (`mS_le_four_of_flat`)
* **thin** (Lemma T): two boundary points in `B̄(y,1)` with nearly antipodal unit normals
  (`ν₁·ν₂ ≤ −(1 − 10⁻⁴)`, i.e. opening `< 1°`).  The paper's *fatness step* shows `K` lies in a
  `400 × 9` box, so `|X ∖ D| ≤ 10⁴` in total. (`thin_box`, `card_sep_box_le`, `thin_card_le`)
* **big turning** (Lemma BT): otherwise two normals at points of `∂K ∩ B̄(y,1)` differ by `> 1/4`
  and are not nearly antipodal; every direction between them is the normal of a support point
  within distance `150` of `y` (linear algebra: `norm_le_of_inner_bounds`), so
  `turning(K, ∂K ∩ B̄(y,150)) ≥ 1/4`; by `turning_sum_le` with multiplicity `601²` there are
  `≤ 8π·601²` such `y`. (`turning_ge_of_nonflat`, `card_bigTurning_le`)

`R ∩ D`: all other points lie in an open half-plane at `y`, so `m_y ≤ 4` directly
(`mS_le_four_of_D`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Definitions -/

/-- **Flat at `y`**: the unit outer normals of `K` at boundary points within distance `1` of `y`
all lie within `1/4` of a single unit vector. -/
def IsFlatAt (X : Finset Pt) (y : Pt) : Prop :=
  ∃ n : Pt, ‖n‖ = 1 ∧ ∀ b ∈ frontier (KBall X), dist y b ≤ 1 →
    ∀ ν ∈ normalCone (KBall X) b, ‖ν‖ = 1 → ‖ν - n‖ ≤ 1 / 4

/-- The boundary piece `∂K ∩ B̄(y, 150)` whose turning is measured in Lemma BT. -/
def bdryNear (X : Finset Pt) (y : Pt) : Set Pt := frontier (KBall X) ∩ Metric.closedBall y 150

/-- Thin-case bound on `|X ∖ D|` (paper: `< 5106`). -/
def cThin : ℝ := 10 ^ 4

/-! ## Elementary geometry -/

/-- **Arc packing**: points at distance `1` from `y`, pairwise `≥ 1` apart, all in the open cone
`(q − y)·n > −1/4` (an open arc of length `2 arccos(−1/4) < 4π/3`), number at most 4.

TODO: prove.
What's missing: write `q − y = dirVec (θ_n + ψ_q)` with `ψ_q ∈ (−arccos(−1/4), arccos(−1/4))`
(`exists_angle`, `Real.arccos`); distance `≥ 1` between unit vectors ⇔ `|ψ_q − ψ_q'| ≥ π/3`
(on this arc of length `< 2π`); sort the `ψ`'s (or use `card_le_of_sep_real` /
`Curve.card_le_of_sep` with spacing `π/3`): `(card − 1)·π/3 < 2 arccos(−1/4) < 4π/3`.
Acceptance: no `sorry`.
Depends on: `card_le_of_sep_real`, `exists_angle`, `dirVec`. Difficulty M. -/
theorem card_sep_arc_le_four {y n : Pt} (hn : ‖n‖ = 1) (P : Finset Pt)
    (h1 : ∀ q ∈ P, dist q y = 1) (hsep : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → 1 ≤ dist q q')
    (hcone : ∀ q ∈ P, -(1 / 4) < inner ℝ (q - y) n) : P.card ≤ 4 := by
  sorry

/-- Helper: a point strictly inside every disc `D(w, Δ₂)` is interior to `K`. -/
theorem n1_mem_interior_of_lt {z : Pt} (h : ∀ w ∈ X, dist z w < dist2 X) :
    z ∈ interior (KBall X) := by
  have hsub : (⋂ w ∈ X, Metric.ball w (dist2 X)) ⊆ KBall X :=
    Set.iInter₂_mono fun _ _ => Metric.ball_subset_closedBall
  have hopen : IsOpen (⋂ w ∈ X, Metric.ball w (dist2 X)) :=
    isOpen_biInter_finset fun _ _ => Metric.isOpen_ball
  refine interior_mono hsub (hopen.interior_eq.symm ▸ ?_)
  simp only [Set.mem_iInter, Metric.mem_ball]
  exact h

/-- `R ∖ D ⊂ int K` (Appendix A (0.3b)): `y` has no partner at distance `Δ₂` or `Δ`, so
`|y − w| < Δ₂` for all `w ∈ X`, and a finite intersection of open discs is open.

TODO: none — proved.
What's missing: `dist y w ≤ Δ₂` (`dist_le_dist2`, `y ∉ D`) and `≠ Δ₂` (`y ∉ S`) for `w ∈ X`,
`w ≠ y`; then `⋂_{w∈X} ball w Δ₂` is open, contains `y`, and is `⊆ KBall X`.
Acceptance: no `sorry`.
Depends on: `dist_le_dist2`, `mem_KBall`. Difficulty S–M. -/
theorem Rset_interior (hX : Normal X) {y : Pt} (hy : y ∈ Rset X) (hyD : y ∉ Dset X) :
    y ∈ interior (KBall X) := by
  have hyX : y ∈ X := (mem_sdiff.1 hy).1
  have hyS : y ∉ Sset X := (mem_sdiff.1 hy).2
  have hpos := hX.dist2_pos
  refine n1_mem_interior_of_lt fun w hw => ?_
  by_cases hwy : w = y
  · subst hwy; simpa using hpos
  have hle := dist_le_dist2 hyX hw (dist_ne_diam_of_not_mem_Dset hyX hyD hw hwy)
  refine lt_of_le_of_ne hle fun heq => hyS ?_
  exact mem_filter.2 ⟨hyX, w, mem_partners.2 ⟨hw, hwy, heq⟩⟩

/-- Points of `S` are not interior to `K`: `S ∖ D ⊂ ∂K` (`ball_polygon_b`) and `D ∩ K = ∅`
(`ball_polygon_c` with `t > 0`).

TODO: none — proved.
What's missing: case split on `q ∈ Dset X`; `frontier ∩ interior = ∅` for a closed set;
`tgap X > 0` from `Two X`.
Acceptance: no `sorry`.
Depends on: `ball_polygon_b`, `ball_polygon_c`, `two_of_pos`. Difficulty S. -/
theorem Sset_not_interior (hX : Normal X) {q : Pt} (hq : q ∈ Sset X) :
    q ∉ interior (KBall X) := by
  by_cases hqD : q ∈ Dset X
  · intro hint
    have hT := two_of_pos hX.dist2_pos
    have h := ball_polygon_c hqD (interior_subset hint)
    rw [dist_self] at h
    unfold tgap at h; linarith [hT.lt]
  · exact (ball_polygon_b hq hqD).2

/-- A segment from an interior point to a non-interior point meets the frontier at a point
`y + λ(q − y)` with `λ ∈ (0, 1]`.

TODO: none — proved.
What's missing: `λ₀ := sSup {λ ∈ [0,1] | y + λ(q−y) ∈ interior K}`; closedness of `K`
puts the point at `λ₀` in `K`, maximality puts it outside `interior K`; `λ₀ > 0` since
`interior K` is open.  (Or: `IsConnected` of the segment + `frontier` meets it.)
Acceptance: no `sorry`.
Depends on: Mathlib topology. Difficulty M. -/
theorem exists_frontier_seg {K : Set Pt} (hKc : IsClosed K) {y q : Pt} (hy : y ∈ interior K)
    (hq : q ∉ interior K) :
    ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ y + l • (q - y) ∈ frontier K := by
  set f : ℝ → Pt := fun l => y + l • (q - y) with hfdef
  have hf : Continuous f := by fun_prop
  set S := Set.Icc (0 : ℝ) 1 ∩ f ⁻¹' (interior K)ᶜ with hSdef
  have hSc : IsClosed S := isClosed_Icc.inter (isOpen_interior.isClosed_compl.preimage hf)
  have hS1 : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_rfl⟩, by simp [f, hq]⟩
  have hSne : S.Nonempty := ⟨1, hS1⟩
  have hSbdd : BddBelow S := ⟨0, fun l hl => hl.1.1⟩
  set l₀ := sInf S with hl₀def
  have hl₀ : l₀ ∈ S := hSc.csInf_mem hSne hSbdd
  have hl₀pos : 0 < l₀ := by
    rcases hl₀.1.1.eq_or_lt with h | h
    · exfalso
      have h2 := hl₀.2
      rw [← h] at h2
      simp [f] at h2
      exact h2 hy
    · exact h
  refine ⟨l₀, hl₀pos, hl₀.1.2, ?_⟩
  rw [hKc.frontier_eq]
  refine ⟨?_, hl₀.2⟩
  have hin : ∀ l ∈ Set.Ico 0 l₀, f l ∈ K := fun l hl => by
    by_contra hK
    have : l₀ ≤ l := csInf_le hSbdd
      ⟨⟨hl.1, by linarith [hl.2, hl₀.1.2]⟩, fun hi => hK (interior_subset hi)⟩
    linarith [hl.2]
  have hcl : l₀ ∈ closure (Set.Ico 0 l₀) := by
    rw [closure_Ico hl₀pos.ne]; exact ⟨hl₀pos.le, le_rfl⟩
  have hmem := hf.continuousAt.continuousWithinAt.mem_closure_image hcl
  exact closure_minimal (Set.image_subset_iff.2 hin) hKc hmem

/-- A nonzero outer normal at a boundary point `b = y + λ(q − y)` (`λ > 0`) of the segment
from an interior point `y` satisfies `(q − y)·ν > 0`.

TODO: none — proved.
What's missing: `y + ε ν ∈ K` for small `ε > 0` (interior), so
`(y + εν − b)·ν ≤ 0`, i.e. `−λ (q−y)·ν + ε‖ν‖² ≤ 0`.
Acceptance: no `sorry`.
Depends on: `normalCone`. Difficulty S–M. -/
theorem inner_pos_of_seg {K : Set Pt} {y q ν : Pt} {l : ℝ} (hy : y ∈ interior K) (hl : 0 < l)
    (hν : ν ∈ normalCone K (y + l • (q - y))) (hν0 : ν ≠ 0) : 0 < inner ℝ (q - y) ν := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  have hνpos : 0 < ‖ν‖ := norm_pos_iff.2 hν0
  set t := ε / 2 / ‖ν‖ with htdef
  have ht : 0 < t := by positivity
  have hmem : y + t • ν ∈ K := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, htdef, div_mul_cancel₀ _ hνpos.ne']
    linarith)
  have h := hν _ hmem
  have e : y + t • ν - (y + l • (q - y)) = t • ν - l • (q - y) := by abel
  rw [e, inner_sub_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq] at h
  simp only [conj_trivial] at h
  have h2 : 0 < t * ‖ν‖ ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith

/-! ## The three cases -/

/-- **Flat case** (Lemma F, Euclidean-local form): `m_y ≤ 4`.

TODO: none — proved.
What's missing: for each `S`-neighbour `q` of `y` (`Sset_not_interior`), take the frontier point
`b = y + λ(q − y)` (`exists_frontier_seg`, `dist y b = λ ≤ 1`) and a unit normal `ν` there
(`exists_unit_normal`); `inner_pos_of_seg` gives `(q−y)·ν > 0`, and flatness
`‖ν − n‖ ≤ 1/4` gives `(q − y)·n > −1/4`.  Conclude with `card_sep_arc_le_four` (neighbours
are pairwise `≥ 1` apart since `δ = 1`).
Acceptance: no `sorry`.
Depends on: `Sset_not_interior`, `exists_frontier_seg`, `inner_pos_of_seg`, `exists_unit_normal`,
`KBall_convex`, `KBall_isClosed`, `card_sep_arc_le_four`. Difficulty M. -/
theorem mS_le_four_of_flat (hX : Normal X) {y : Pt} (hy : y ∈ interior (KBall X))
    (hflat : IsFlatAt X y) : mS X y ≤ 4 := by
  obtain ⟨n, hn, hfl⟩ := hflat
  unfold mS
  apply card_sep_arc_le_four (y := y) hn
  · intro q hq
    obtain ⟨-, -, hd⟩ := mem_partners.1 (mem_filter.1 hq).1
    rw [dist_comm, hd, hX.minDist_eq]
  · intro q hq q' hq' hne
    exact one_le_dist hX.minDist_eq (mem_partners.1 (mem_filter.1 hq).1).1
      (mem_partners.1 (mem_filter.1 hq').1).1 hne
  · intro q hq
    obtain ⟨hqp, hqS⟩ := mem_filter.1 hq
    obtain ⟨-, -, hd⟩ := mem_partners.1 hqp
    rw [hX.minDist_eq] at hd
    obtain ⟨l, hl0, hl1, hb⟩ :=
      exists_frontier_seg (KBall_isClosed X) hy (Sset_not_interior hX hqS)
    obtain ⟨ν, hν1, hν⟩ := exists_unit_normal (KBall_convex X) ⟨y, hy⟩ hb
    have hdb : dist y (y + l • (q - y)) ≤ 1 := by
      rw [dist_eq_norm, show y - (y + l • (q - y)) = -(l • (q - y)) by abel, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos hl0, ← dist_eq_norm, dist_comm, hd, mul_one]
      exact hl1
    have hνn := hfl _ hb hdb ν hν hν1
    have hν0 : ν ≠ 0 := by rintro rfl; simp at hν1
    have hpos := inner_pos_of_seg hy hl0 hν hν0
    have hqy : ‖q - y‖ = 1 := by rw [← dist_eq_norm, dist_comm, hd]
    have hab := abs_real_inner_le_norm (q - y) (n - ν)
    rw [hqy, norm_sub_rev, one_mul] at hab
    have hsplit : inner ℝ (q - y) n = inner ℝ (q - y) ν + inner ℝ (q - y) (n - ν) := by
      rw [inner_sub_right]; ring
    rw [hsplit]
    have := (abs_le.1 (hab.trans hνn)).1
    linarith

/-- **`R ∩ D`** (Appendix A (0.3a)): for `y ∈ D` with diametral partner `w`, every other
`x ∈ X` has `(x − y)·(w − y) ≥ |x − y|²/2 > 0`; so `m_y ≤ deg y ≤ 4`.

TODO: none — proved.
What's missing: `|x − w| ≤ Δ` expands to the inequality; apply `card_sep_arc_le_four` with
`n = (w − y)/Δ` to `partners X δ y` (the cone condition `> 0 > −1/4`).
Acceptance: no `sorry`.
Depends on: `dist_le_diam`, `card_sep_arc_le_four`. Difficulty S–M. -/
theorem mS_le_four_of_D (hX : Normal X) {y : Pt} (hyX : y ∈ X) (hyD : y ∈ Dset X) :
    mS X y ≤ 4 := by
  obtain ⟨w, hw⟩ := (mem_filter.1 hyD).2
  obtain ⟨hwX, hwy, hdw⟩ := mem_partners.1 hw
  have hΔ : 0 < diam X := by rw [← hdw]; exact dist_pos.2 (Ne.symm hwy)
  set n : Pt := (diam X)⁻¹ • (w - y) with hndef
  have hn : ‖n‖ = 1 := by
    rw [hndef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΔ), ← dist_eq_norm,
      dist_comm, hdw, inv_mul_cancel₀ hΔ.ne']
  unfold mS
  apply card_sep_arc_le_four (y := y) hn
  · intro q hq
    obtain ⟨-, -, hd⟩ := mem_partners.1 (mem_filter.1 hq).1
    rw [dist_comm, hd, hX.minDist_eq]
  · intro q hq q' hq' hne
    exact one_le_dist hX.minDist_eq (mem_partners.1 (mem_filter.1 hq).1).1
      (mem_partners.1 (mem_filter.1 hq').1).1 hne
  · intro q hq
    obtain ⟨hqX, -, hd⟩ := mem_partners.1 (mem_filter.1 hq).1
    rw [hX.minDist_eq] at hd
    have hqw := dist_le_diam hqX hwX
    have e1 := dist_sq_pt q w
    have e2 := dist_sq_pt y q
    have e3 := dist_sq_pt y w
    rw [hd] at e2; rw [hdw] at e3
    have hsq : dist q w ^ 2 ≤ diam X ^ 2 := pow_le_pow_left₀ dist_nonneg hqw 2
    rw [hndef, inner_smul_right, inner_pt]
    simp only [PiLp.sub_apply]
    have : 0 < (q 0 - y 0) * (w 0 - y 0) + (q 1 - y 1) * (w 1 - y 1) := by nlinarith
    have := mul_pos (inv_pos.2 hΔ) this
    linarith

/-- **(0.3b)** Every boundary point of `K` lies on a circle `C(w, Δ₂)` with `w ∈ X`, and
`(b − w)/Δ₂` is then an outer normal at `b`.  (Used in the fatness step of Lemma T.)

TODO: none — proved.
What's missing: if `|b − w| < Δ₂` for all `w ∈ X` then `b` is interior (finite intersection of
open discs); `K ⊂ D(w, Δ₂)` gives the normal (`neg_mem_normalCone`).
Acceptance: no `sorry`.
Depends on: `mem_KBall`, `neg_mem_normalCone`. Difficulty S–M. -/
theorem frontier_on_circle (hX : Normal X) {b : Pt} (hb : b ∈ frontier (KBall X)) :
    ∃ w ∈ X, dist b w = dist2 X := by
  have hbK : b ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hb.1
  by_contra hne
  push Not at hne
  exact hb.2 (n1_mem_interior_of_lt fun w hw =>
    lt_of_le_of_ne (mem_KBall.1 hbK w hw) (hne w hw))

/-- **Lemma T, fatness step** (Appendix A.1 with REF4 fix 1): if two boundary points within
distance 1 of `y ∈ K` have nearly antipodal unit outer normals (`K` lies in a cone of opening
`< 1°` or a strip, `y` at distance `≤ 1` from both lines), then `K` lies in a box of length
`400` and width `9`.

TODO: prove.
What's missing: the fatness step verbatim: bisector frame `(e, e⊥)`; levels `[E₋, E₊]`,
`L = E₊ − E₋`, `W ≤ w_y + 2 tan(θ/2) L`, `w_y ≤ 2/cos(θ/2)`; top/bottom points `p_top, p_bot`
at the middle level with outer normals from `frontier_on_circle`, `cos φ > 0`,
`|tan φ| ≤ 2W/L`; `(w_bot − w_top)·e⊥ ≥ −W + 2Δ₂ cos φ*` versus `|w_bot − w_top| ≤ Δ ≤ 1.94Δ₂`
forces `L < 400`; then `W < 9`.  Constants: exact rational bounds as in `r4_nb_exact.py (3)`.
Acceptance: no `sorry`.
Depends on: `frontier_on_circle`, `Normal` (`Δ ≤ 1.94Δ₂`, `Δ₂ ≥ 10⁴`),
`KBall_convex`, `KBall_isCompact`. Difficulty L–XL. -/
theorem thin_box (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ 1) (h₂ : dist y b₂ ≤ 1)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ∃ e : Pt, ‖e‖ = 1 ∧ ∃ c₀ c₁ : ℝ, ∀ x ∈ KBall X,
      c₀ ≤ inner ℝ x e ∧ inner ℝ x e ≤ c₀ + 400 ∧
        c₁ ≤ inner ℝ x (perp e) ∧ inner ℝ x (perp e) ≤ c₁ + 9 := by
  sorry

/-- **Box packing**: points pairwise `≥ 1` apart in a `400 × 9` box number at most `10⁴`.

TODO: prove.
What's missing: grid pigeonhole with half-open cells of side `7/10` (diameter `< 1`):
`⌈400/0.7⌉·⌈9/0.7⌉ ≤ 572·13 < 10⁴` cells, at most one point per cell
(as in `card_lt_N0` / `card_sep_le_81`).
Acceptance: no `sorry`.
Depends on: `Defs.floor_cell_lt`, `Defs.close_of_floor_eq` (or a fresh grid argument). Difficulty M. -/
theorem card_sep_box_le {P : Finset Pt} (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → 1 ≤ dist a b)
    {e : Pt} (he : ‖e‖ = 1) {c₀ c₁ : ℝ}
    (hbox : ∀ x ∈ P, c₀ ≤ inner ℝ x e ∧ inner ℝ x e ≤ c₀ + 400 ∧
      c₁ ≤ inner ℝ x (perp e) ∧ inner ℝ x (perp e) ≤ c₁ + 9) :
    (P.card : ℝ) ≤ cThin := by
  sorry

/-- **Lemma T** (thin `K`): `|X ∖ D| ≤ 10⁴`.

TODO: none — proved.
What's missing: `X ∖ D ⊆ K` (`ball_polygon_a`), points `≥ 1` apart (`one_le_dist`),
`thin_box`, `card_sep_box_le`.
Acceptance: no `sorry` (inherits).
Depends on: `thin_box`, `card_sep_box_le`, `ball_polygon_a`, `one_le_dist`. Difficulty S. -/
theorem thin_card_le (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ 1) (h₂ : dist y b₂ ≤ 1)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ((X \ Dset X).card : ℝ) ≤ cThin := by
  obtain ⟨e, he, c₀, c₁, hbox⟩ := thin_box hX hy hb₁ hb₂ h₁ h₂ hν₁ hν₂ hn₁ hn₂ hthin
  refine card_sep_box_le (P := X \ Dset X) (fun a ha b hb hab => ?_) he (c₀ := c₀) (c₁ := c₁)
    (fun x hx => hbox x (ball_polygon_a (mem_sdiff.1 hx).1 (mem_sdiff.1 hx).2))
  exact one_le_dist hX.minDist_eq (mem_sdiff.1 ha).1 (mem_sdiff.1 hb).1 hab

/-- **Support points stay close** (linear algebra of the non-thin case): if
`|v·ν₁|, |v·ν₂| ≤ 1` for unit `ν₁, ν₂` with `|ν₁·ν₂| ≤ 1 − 10⁻⁴`, then `‖v‖ ≤ 150`.
(`(1 − c²)‖v‖² = s₁² − 2c s₁s₂ + s₂² ≤ 2(1 + |c|)`, so `‖v‖² ≤ 2/(1 − |c|) ≤ 2·10⁴`.)

TODO: none — proved.
What's missing: the 2D Gram identity in coordinates (`inner_pt`, `unit_sq`), then `nlinarith`.
Acceptance: no `sorry`.
Depends on: `inner_pt`, `norm_sq_pt`. Difficulty S–M. -/
theorem norm_le_of_inner_bounds {ν₁ ν₂ v : Pt} (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1)
    (hc : |inner ℝ ν₁ ν₂| ≤ 1 - 1 / 10 ^ 4) (hs₁ : |inner ℝ v ν₁| ≤ 1)
    (hs₂ : |inner ℝ v ν₂| ≤ 1) : ‖v‖ ≤ 150 := by
  have ha := unit_sq hn₁
  have hb := unit_sq hn₂
  have hv := norm_sq_pt v
  rw [inner_pt] at hc hs₁ hs₂
  have key : (1 - (ν₁ 0 * ν₂ 0 + ν₁ 1 * ν₂ 1) ^ 2) * (v 0 ^ 2 + v 1 ^ 2) =
      (v 0 * ν₁ 0 + v 1 * ν₁ 1) ^ 2 + (v 0 * ν₂ 0 + v 1 * ν₂ 1) ^ 2 -
        2 * (ν₁ 0 * ν₂ 0 + ν₁ 1 * ν₂ 1) * (v 0 * ν₁ 0 + v 1 * ν₁ 1) *
          (v 0 * ν₂ 0 + v 1 * ν₂ 1) := by
    linear_combination ((v 0 * ν₁ 0 + v 1 * ν₁ 1) ^ 2 -
      (ν₁ 0 ^ 2 + ν₁ 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2)) * hb +
      ((v 0 * ν₂ 0 + v 1 * ν₂ 1) ^ 2 - (v 0 ^ 2 + v 1 ^ 2)) * ha
  rw [← hv] at key
  generalize ν₁ 0 * ν₂ 0 + ν₁ 1 * ν₂ 1 = c at hc key
  generalize v 0 * ν₁ 0 + v 1 * ν₁ 1 = s₁ at hs₁ key
  generalize v 0 * ν₂ 0 + v 1 * ν₂ 1 = s₂ at hs₂ key
  have hc1 : |c| ≤ 1 := by linarith
  have hp : |c * s₁ * s₂| ≤ 1 := by
    rw [abs_mul, abs_mul]
    have := abs_nonneg c; have := abs_nonneg s₁; have := abs_nonneg s₂
    calc |c| * |s₁| * |s₂| ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hp' := neg_abs_le (c * s₁ * s₂)
  have h1 : s₁ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one s₁).2 hs₁
  have h2 : s₂ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one s₂).2 hs₂
  have hc2 : c ^ 2 ≤ (1 - 1 / 10 ^ 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg c) hc 2
  have hV0 : 0 ≤ ‖v‖ ^ 2 := by positivity
  have h4 : (1 - c ^ 2) * ‖v‖ ^ 2 ≤ 4 := by rw [key]; linarith
  have h5 : (1 - (1 - 1 / 10 ^ 4) ^ 2) * ‖v‖ ^ 2 ≤ (1 - c ^ 2) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hV0
  have hVb : ‖v‖ ^ 2 ≤ 150 ^ 2 := by norm_num at h5 ⊢; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg v) (by norm_num) two_ne_zero).1 hVb

/-- **Non-flat, non-thin ⇒ big turning** (Lemma BT, local part): every direction `d` strictly
between `ν₁` and `ν₂` (short arc, length `∠(ν₁,ν₂) ≥ ‖ν₁ − ν₂‖ > 1/4`) is an outer normal at a
support point `x_d ∈ ∂K`; `x_d` beats `b₁, b₂` in direction `d` and lies in both supporting
half-planes, so `v = x_d − y` has `|v·ν_i| ≤ 1` and `‖v‖ ≤ 150`.  Hence
`turning(K, ∂K ∩ B̄(y,150)) ≥ 1/4`.

TODO: prove.
What's missing: parametrise the short arc `ν₁ = dirVec c`, `ν₂ = dirVec (c ± α)`
(`exists_dirVec_pair`); for `θ` inside, `d = a ν₁ + b ν₂` with `a, b ≥ 0`; support point by
compactness (`IsCompact.exists_isMaxOn`), `mem_frontier_of_max`; bounds
`g_i ≤ v·ν_i ≤ h_i` with `g_i, h_i ∈ [−1, 1]`; `norm_le_of_inner_bounds`
(`|ν₁·ν₂| ≤ 1 − 10⁻⁴` from `hnt` and `‖ν₁ − ν₂‖ > 1/4`); endpoints use `b₁, b₂` themselves;
`le_turning_of_Icc`; `norm_sub_le_ang`.
Acceptance: no `sorry`.
Depends on: `norm_le_of_inner_bounds`, `le_turning_of_Icc`, `mem_frontier_of_max`,
`exists_dirVec_pair`, `norm_sub_le_ang`, `KBall_isCompact`. Difficulty M–L. -/
theorem turning_ge_of_nonflat (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ interior (KBall X))
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ 1) (h₂ : dist y b₂ ≤ 1)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hfar : 1 / 4 < ‖ν₁ - ν₂‖)
    (hnt : -(1 - 1 / 10 ^ 4) < inner ℝ ν₁ ν₂) :
    1 / 4 ≤ turning (KBall X) (bdryNear X y) := by
  sorry

/-- **Ball packing**: points pairwise `≥ 1` apart within distance `ρ` of `x` number at most
`(4ρ + 1)²`.

TODO: none — proved.
What's missing: grid pigeonhole (half-open cells of side `7/10`), generalising
`card_sep_le_81` (the case `ρ = 2`).
Acceptance: no `sorry`.
Depends on: `Defs.floor_cell_lt`-style grid lemmas. Difficulty M. -/
theorem card_sep_ball_le {P : Finset Pt} (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → 1 ≤ dist a b)
    (x : Pt) (ρ : ℕ) (hx : ∀ a ∈ P, dist a x ≤ ρ) : P.card ≤ (4 * ρ + 1) ^ 2 := by
  let f : Pt → ℤ × ℤ := fun a => (⌊2 * (a 0 - x 0)⌋, ⌊2 * (a 1 - x 1)⌋)
  have hbox : ∀ a ∈ P, f a ∈ (Icc (-(2 * ρ : ℤ)) (2 * ρ)) ×ˢ (Icc (-(2 * ρ : ℤ)) (2 * ρ)) := by
    intro a ha
    have hd := hx a ha
    have hsq := dist_sq_pt a x
    have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
    have h4 : dist a x ^ 2 ≤ (ρ : ℝ) ^ 2 := pow_le_pow_left₀ dist_nonneg hd 2
    have b0 : |a 0 - x 0| ≤ ρ := by
      rw [← abs_of_nonneg hρ]; apply sq_le_sq.1; nlinarith [sq_nonneg (a 1 - x 1)]
    have b1 : |a 1 - x 1| ≤ ρ := by
      rw [← abs_of_nonneg hρ]; apply sq_le_sq.1; nlinarith [sq_nonneg (a 0 - x 0)]
    rw [abs_le] at b0 b1
    simp only [f, mem_product, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Int.le_floor]; push_cast; linarith
    · rw [Int.floor_le_iff]; push_cast; linarith
    · rw [Int.le_floor]; push_cast; linarith
    · rw [Int.floor_le_iff]; push_cast; linarith
  have := card_le_card_of_injOn f hbox (fun a ha b hb e => by
    by_contra hab
    have h1 := hsep a ha b hb hab
    simp only [f, Prod.mk.injEq] at e
    have c0 := Int.floor_le (2 * (a 0 - x 0))
    have c1 := Int.lt_floor_add_one (2 * (a 0 - x 0))
    have c2 := Int.floor_le (2 * (b 0 - x 0))
    have c3 := Int.lt_floor_add_one (2 * (b 0 - x 0))
    have c4 := Int.floor_le (2 * (a 1 - x 1))
    have c5 := Int.lt_floor_add_one (2 * (a 1 - x 1))
    have c6 := Int.floor_le (2 * (b 1 - x 1))
    have c7 := Int.lt_floor_add_one (2 * (b 1 - x 1))
    rw [e.1] at c0 c1; rw [e.2] at c4 c5
    have d0 : |a 0 - b 0| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have d1 : |a 1 - b 1| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have hsq := dist_sq_pt a b
    have : dist a b ^ 2 < 1 := by
      rw [hsq]
      have := sq_abs (a 0 - b 0); have := sq_abs (a 1 - b 1)
      nlinarith [abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1)]
    nlinarith [dist_nonneg (x := a) (y := b)])
  rw [card_product, Int.card_Icc] at this
  have e : (2 * (ρ : ℤ) + 1 - -(2 * ρ)).toNat = 4 * ρ + 1 := by omega
  rw [e] at this
  rw [sq]; exact this

/-- **Lemma BT** (count): at most `8π·601²` points `y ∈ X` have
`turning(K, ∂K ∩ B̄(y, 150)) ≥ 1/4`.

TODO: none — proved.
What's missing: `turning_sum_le` with `γ_y = bdryNear X y` (closed, `⊆ frontier`), multiplicity
`M = 601²` from `card_sep_ball_le` (a boundary point `b` lies in `B̄(y,150)` for at most
`(4·150+1)²` points `y`, pairwise `≥ 1` apart); then `#Y · (1/4) ≤ 2π M`.
Acceptance: no `sorry`.
Depends on: `turning_sum_le`, `card_sep_ball_le`, `KBall_convex`, `KBall_isCompact`,
`one_le_dist`. Difficulty M. -/
theorem card_bigTurning_le (hX : Normal X) (Y : Finset Pt) (hY : Y ⊆ X)
    (hbig : ∀ y ∈ Y, 1 / 4 ≤ turning (KBall X) (bdryNear X y)) :
    (Y.card : ℝ) ≤ 8 * π * 601 ^ 2 := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hsep : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → 1 ≤ dist a b := fun a ha b hb hab =>
    one_le_dist hX.minDist_eq (hY ha) (hY hb) hab
  have hsum := turning_sum_le (KBall_convex X) (KBall_isCompact hne) Y (fun y => bdryNear X y)
    (fun y _ => Set.inter_subset_left)
    (fun y _ => isClosed_frontier.inter Metric.isClosed_closedBall) (601 ^ 2)
    (fun b => by
      have := card_sep_ball_le (P := Y.filter (fun y => b ∈ bdryNear X y))
        (fun a ha c hc hac => hsep a (mem_filter.1 ha).1 c (mem_filter.1 hc).1 hac) b 150
        (fun a ha => by
          have h := (mem_filter.1 ha).2.2
          rw [Metric.mem_closedBall, dist_comm] at h
          push_cast; exact h)
      simpa using this)
  have hle : ∑ y ∈ Y, (1 / 4 : ℝ) ≤ ∑ y ∈ Y, turning (KBall X) (bdryNear X y) :=
    sum_le_sum hbig
  rw [sum_const, nsmul_eq_mul] at hle
  push_cast at hsum
  linarith

/-- The boundary data at a point of `R ∖ D` with `m_y ≥ 1`: a frontier point within distance `1`
carrying a unit outer normal.

TODO: none — proved.
What's missing: pick an `S`-neighbour `q`; `exists_frontier_seg`, `exists_unit_normal`.
Acceptance: no `sorry` (inherits).
Depends on: `Sset_not_interior`, `exists_frontier_seg`, `exists_unit_normal`. Difficulty S. -/
theorem exists_near_normal (hX : Normal X) {y : Pt} (hy : y ∈ interior (KBall X))
    (hm : 0 < mS X y) :
    ∃ b ∈ frontier (KBall X), dist y b ≤ 1 ∧ ∃ ν ∈ normalCone (KBall X) b, ‖ν‖ = 1 := by
  obtain ⟨q, hq⟩ := card_pos.1 hm
  obtain ⟨hqp, hqS⟩ := mem_filter.1 hq
  obtain ⟨-, -, hd⟩ := mem_partners.1 hqp
  rw [hX.minDist_eq] at hd
  obtain ⟨l, hl0, hl1, hb⟩ :=
    exists_frontier_seg (KBall_isClosed X) hy (Sset_not_interior hX hqS)
  obtain ⟨ν, hν1, hν⟩ := exists_unit_normal (KBall_convex X) ⟨y, hy⟩ hb
  refine ⟨_, hb, ?_, ν, hν, hν1⟩
  rw [dist_eq_norm, show y - (y + l • (q - y)) = -(l • (q - y)) by abel, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos hl0, ← dist_eq_norm, dist_comm, hd, mul_one]
  exact hl1

/-- The number `8π·601² + 10⁴` fits in `cN1 = 10⁷`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem cN1_check : 8 * π * 601 ^ 2 + cThin ≤ cN1 := by
  have := Real.pi_lt_d2
  norm_num [cThin, cN1]
  nlinarith

/-- **Theorem N1** (Appendix A.4): at most `cN1` points `y ∈ R` have `m_y > 4`.

TODO: none — proved from the lemma statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `mS_le_four_of_D`, `Rset_interior`, `mS_le_four_of_flat`, `exists_near_normal`,
`thin_card_le`, `turning_ge_of_nonflat`, `card_bigTurning_le`, `cN1_check`. -/
theorem N1 (hX : Normal X) :
    (((Rset X).filter (fun y => 4 < mS X y)).card : ℝ) ≤ cN1 := by
  set E := (Rset X).filter (fun y => 4 < mS X y) with hE
  have hRX : Rset X ⊆ X := sdiff_subset
  -- every exceptional point is in `R ∖ D`, interior, and not flat
  have key : ∀ y ∈ E, y ∉ Dset X ∧ y ∈ interior (KBall X) ∧ ∃ b₁ ∈ frontier (KBall X),
      dist y b₁ ≤ 1 ∧ ∃ ν₁ ∈ normalCone (KBall X) b₁, ‖ν₁‖ = 1 ∧ ∃ b₂ ∈ frontier (KBall X),
      dist y b₂ ≤ 1 ∧ ∃ ν₂ ∈ normalCone (KBall X) b₂, ‖ν₂‖ = 1 ∧ 1 / 4 < ‖ν₂ - ν₁‖ := by
    intro y hy
    obtain ⟨hyR, hm⟩ := mem_filter.1 hy
    have hyD : y ∉ Dset X := fun hD => by
      have := mS_le_four_of_D hX (hRX hyR) hD; omega
    have hint := Rset_interior hX hyR hyD
    refine ⟨hyD, hint, ?_⟩
    obtain ⟨b₁, hb₁, hd₁, ν₁, hν₁, hn₁⟩ := exists_near_normal hX hint (by omega)
    refine ⟨b₁, hb₁, hd₁, ν₁, hν₁, hn₁, ?_⟩
    by_contra hc
    push Not at hc
    have hflat : IsFlatAt X y := ⟨ν₁, hn₁, fun b hb hd ν hν hn => hc b hb hd ν hν hn⟩
    have := mS_le_four_of_flat hX hint hflat
    omega
  have hc := cN1_check
  have hπ := Real.pi_pos
  by_cases hthin : ∃ y ∈ E, ∃ b₁ ∈ frontier (KBall X), dist y b₁ ≤ 1 ∧
      ∃ ν₁ ∈ normalCone (KBall X) b₁, ‖ν₁‖ = 1 ∧ ∃ b₂ ∈ frontier (KBall X), dist y b₂ ≤ 1 ∧
      ∃ ν₂ ∈ normalCone (KBall X) b₂, ‖ν₂‖ = 1 ∧ inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)
  · obtain ⟨y, hy, b₁, hb₁, hd₁, ν₁, hν₁, hn₁, b₂, hb₂, hd₂, ν₂, hν₂, hn₂, hin⟩ := hthin
    have hyK := interior_subset (key y hy).2.1
    have h := thin_card_le hX hyK hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hin
    have hsub : E ⊆ X \ Dset X := fun z hz =>
      mem_sdiff.2 ⟨hRX (mem_filter.1 hz).1, (key z hz).1⟩
    have : (E.card : ℝ) ≤ (X \ Dset X).card := by exact_mod_cast card_le_card hsub
    nlinarith
  · push Not at hthin
    have hbig : ∀ y ∈ E, 1 / 4 ≤ turning (KBall X) (bdryNear X y) := by
      intro y hy
      obtain ⟨-, hint, b₁, hb₁, hd₁, ν₁, hν₁, hn₁, b₂, hb₂, hd₂, ν₂, hν₂, hn₂, hfar⟩ := key y hy
      have hnt := hthin y hy b₁ hb₁ hd₁ ν₁ hν₁ hn₁ b₂ hb₂ hd₂ ν₂ hν₂ hn₂
      rw [norm_sub_rev] at hfar
      exact turning_ge_of_nonflat hX hint hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hfar hnt
    have := card_bigTurning_le hX E (fun z hz => hRX (mem_filter.1 hz).1) hbig
    have : (0 : ℝ) ≤ cThin := by norm_num [cThin]
    linarith

/-- **(E′)** `μ(δ) ≤ e(S) + 5r + cN1`: the exact identity with `deg y + m_y ≤ 10` off the
N1-exceptions and `≤ 12` on them.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `mu_delta_identity`, `N1`, `mS_le_degδ`, `degδ_le_six`. -/
theorem E_bound15 (hX : Normal X) :
    (mult X (minDist X) : ℝ) ≤ eS X + 5 * (Rset X).card + cN1 := by
  have hid := mu_delta_identity X
  set E := (Rset X).filter (fun y => 4 < mS X y) with hE
  have hsum : ∑ y ∈ Rset X, (degδ X y + mS X y) ≤ 10 * (Rset X).card + 2 * E.card := by
    have h1 : ∀ y ∈ Rset X, degδ X y + mS X y ≤ 10 + (if 4 < mS X y then 2 else 0) := by
      intro y _
      have := degδ_le_six X y
      have := mS_le_degδ X y
      split_ifs with h <;> omega
    calc ∑ y ∈ Rset X, (degδ X y + mS X y)
        ≤ ∑ y ∈ Rset X, (10 + (if 4 < mS X y then 2 else 0)) := sum_le_sum h1
      _ = 10 * (Rset X).card + 2 * E.card := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, mul_comm, ← sum_filter, sum_const,
          smul_eq_mul, hE]
        ring
  have hN := N1 hX
  rw [← hE] at hN
  have : 2 * mult X (minDist X) ≤ 2 * eS X + 10 * (Rset X).card + 2 * E.card := by omega
  have : (2 * mult X (minDist X) : ℝ) ≤ 2 * eS X + 10 * (Rset X).card + 2 * E.card := by
    exact_mod_cast this
  linarith

end

end Erdos132Main

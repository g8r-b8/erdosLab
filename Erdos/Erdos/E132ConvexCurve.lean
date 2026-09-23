import Erdos.E132MainDefs

/-!
# Erdős Problem 132, `54/37` theorem — direction-measure counting for outward normals

Infrastructure for the bad-edge counts KK, DD and (c2) of §5.2 (`E132MainLocal.lean`).

The paper counts bad edges with arc length along `∂K` (Lemma 5.2, the walk of (c2)).  Here we
avoid convex-curve arc length altogether and work with a finite set `V` of points carrying unit
*outward normals* `nrm v` with the strict chord inequalities `(w − v)·nrm v < 0` (a
`NormalConfig`).  For such a configuration:

* two points whose normals lie in a common half-plane `{n · g ≥ c}` are separated along `g^⊥`:
  `c·|w − v| ≤ |det(g, w − v)|` (`NormalConfig.sep_det2`, via `wedge_sep`);
* hence the points whose normals lie in the *cap* between the normals of a unit edge `pq`
  number at most `2/|n_p + n_q| + 1` (`NormalConfig.card_cap_le`), and a direction lies in the
  caps of at most `D·N` oriented edges (`D` = degree bound);
* integrating over directions (`sum_dirMeasure_le`), with each cap of measure `∠(n_p, n_q)`
  (`ang_le_dirMeasure_cap`): `#E · β₀ ≤ 2π·D·N` (`NormalConfig.card_mul_le_of_edges`) —
  this gives KK and DD;
* for (c2), windows of half-width `1/800` around the normals, and the discrete "walk":
  a point `v` at depth `≤ 1` in a disc `D(x, R) ⊇ V` whose normal is not nearly parallel to
  `x − v` has all window-neighbours on one side within distance `412`
  (`NormalConfig.card_walk_mul_le`).
-/

open Finset Real
open Erdos132Convex (Pt)
open scoped Classical

namespace Erdos132Main

namespace Curve

noncomputable section

/-! ## Planar coordinates -/

theorem inner_coord (x y : Pt) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem norm_sq_coord (x : Pt) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord]; ring

theorem det2_eq_inner_perp (u e : Pt) : det2 u e = inner ℝ e (perp u) := by
  simp [det2, perp, inner_coord]; ring

theorem det2_sub_right (u x y : Pt) : det2 u (x - y) = det2 u x - det2 u y := by
  simp only [det2, PiLp.sub_apply]; ring

theorem det2_swap (a b : Pt) : det2 b a = - det2 a b := by
  simp only [det2]; ring

theorem lagrange (e u : Pt) : inner ℝ e u ^ 2 + det2 u e ^ 2 = ‖e‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_sq_coord, norm_sq_coord, inner_coord, det2]; ring

theorem abs_det2_le (w e : Pt) : |det2 w e| ≤ ‖e‖ * ‖w‖ := by
  have h := lagrange e w
  have h2 : det2 w e ^ 2 ≤ (‖e‖ * ‖w‖) ^ 2 := by nlinarith [sq_nonneg (inner ℝ e w)]
  have := sq_le_sq.1 h2
  rwa [abs_of_nonneg (by positivity : 0 ≤ ‖e‖ * ‖w‖)] at this

/-- Inner product in an orthonormal frame `(e, e^⊥)`. -/
theorem inner_frame {e : Pt} (he : ‖e‖ = 1) (w₁ w₂ : Pt) :
    inner ℝ w₁ w₂ = inner ℝ w₁ e * inner ℝ w₂ e + det2 e w₁ * det2 e w₂ := by
  have h := norm_sq_coord e
  rw [he] at h
  rw [inner_coord, inner_coord, inner_coord]
  simp only [det2]
  linear_combination (w₁ 0 * w₂ 0 + w₁ 1 * w₂ 1) * h

/-- Unit vectors with `a · b ≥ 1` coincide. -/
theorem eq_of_one_le_inner {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (h : 1 ≤ inner ℝ a b) :
    a = b := by
  have h2 := norm_sub_sq_real a b
  rw [ha, hb] at h2
  have : ‖a - b‖ ^ 2 ≤ 0 := by linarith
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- Unit vectors with `det(a, b) = 0` are equal or opposite. -/
theorem eq_or_eq_neg_of_det2_eq_zero {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (h : det2 a b = 0) : a = b ∨ a = -b := by
  have hl := lagrange b a
  rw [h, ha, hb] at hl
  have h1 : inner ℝ b a = 1 ∨ inner ℝ b a = -1 := by
    have : (inner ℝ b a - 1) * (inner ℝ b a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases h1 with h1 | h1
  · left; exact eq_of_one_le_inner ha hb (by rw [real_inner_comm]; linarith)
  · right
    have hn : ‖-b‖ = 1 := by rw [norm_neg, hb]
    exact eq_of_one_le_inner ha hn (by rw [inner_neg_right, real_inner_comm]; linarith)

/-- Grassmann–Plücker relation in the plane. -/
theorem plucker (w u n h : Pt) :
    det2 w n * det2 u h = det2 w u * det2 n h + det2 w h * det2 u n := by
  simp only [det2]; ring

/-! ## Directions -/

theorem continuous_dirVec : Continuous dirVec := by
  unfold dirVec; fun_prop

theorem norm_dirVec (θ : ℝ) : ‖dirVec θ‖ = 1 := by
  have h := norm_sq_coord (dirVec θ)
  have h2 : (dirVec θ) 0 ^ 2 + (dirVec θ) 1 ^ 2 = 1 := by simp [dirVec]
  rw [h2] at h
  nlinarith [norm_nonneg (dirVec θ)]

theorem dirVec_add_int_mul (θ : ℝ) (k : ℤ) : dirVec (θ + k * (2 * π)) = dirVec θ := by
  simp [dirVec, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem exists_dirVec {n : Pt} (hn : ‖n‖ = 1) : ∃ θ : ℝ, dirVec θ = n := by
  set z : ℂ := ⟨n 0, n 1⟩
  have hsq := norm_sq_coord n
  rw [hn] at hsq
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [z]
    rw [show n 0 * n 0 + n 1 * n 1 = 1 by nlinarith, Real.sqrt_one]
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  refine ⟨Complex.arg z, ?_⟩
  ext i; fin_cases i
  · simp [dirVec, Complex.cos_arg hz0, hz, z]
  · simp [dirVec, Complex.sin_arg, hz, z]

theorem inner_dirVec (θ φ : ℝ) : inner ℝ (dirVec θ) (dirVec φ) = Real.cos (θ - φ) := by
  rw [inner_coord, Real.cos_sub]; simp [dirVec]

/-- `dirVec` is `1`-Lipschitz (chord `≤` arc). -/
theorem norm_dirVec_sub_le (θ φ : ℝ) : ‖dirVec θ - dirVec φ‖ ≤ |θ - φ| := by
  have h := norm_sub_sq_real (dirVec θ) (dirVec φ)
  rw [norm_dirVec, norm_dirVec, inner_dirVec] at h
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ - φ)
  have hsq : ‖dirVec θ - dirVec φ‖ ^ 2 ≤ |θ - φ| ^ 2 := by rw [sq_abs]; nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).1 hsq

/-! ## Measure of sets of directions -/

/-- The measure of the set of directions `θ ∈ [0, 2π)` with `dirVec θ ∈ Q`. -/
def dirMeasure (Q : Set Pt) : ℝ :=
  (MeasureTheory.volume {θ : ℝ | θ ∈ Set.Ico 0 (2 * π) ∧ dirVec θ ∈ Q}).toReal

/-- A closed arc of directions of length `α ≤ 2π` inside `Q` gives `dirMeasure Q ≥ α`. -/
theorem le_dirMeasure_of_Icc {Q : Set Pt} {c α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 2 * π)
    (h : ∀ θ ∈ Set.Icc c (c + α), dirVec θ ∈ Q) : α ≤ dirMeasure Q := by
  have hpi := Real.pi_pos
  set k : ℤ := ⌊c / (2 * π)⌋
  set c' := c - k * (2 * π)
  have hk1 : (k : ℝ) ≤ c / (2 * π) := Int.floor_le _
  have hk2 : c / (2 * π) < k + 1 := Int.lt_floor_add_one _
  have hc0 : 0 ≤ c' := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 hk1; simp only [c']; linarith
  have hc1 : c' < 2 * π := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 hk2; simp only [c']; linarith
  have h' : ∀ θ ∈ Set.Icc c' (c' + α), dirVec θ ∈ Q := by
    intro θ hθ
    rw [← dirVec_add_int_mul θ k]
    exact h _ ⟨by simp only [c'] at hθ; linarith [hθ.1], by simp only [c'] at hθ; linarith [hθ.2]⟩
  set T : Set ℝ := {θ | θ ∈ Set.Ico 0 (2 * π) ∧ dirVec θ ∈ Q}
  have hT1 : Set.Ico c' (min (c' + α) (2 * π)) ⊆ T := fun θ hθ =>
    ⟨⟨by linarith [hθ.1], lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩,
      h' θ ⟨hθ.1, (lt_of_lt_of_le hθ.2 (min_le_left _ _)).le⟩⟩
  have hT2 : Set.Ico 0 (c' + α - 2 * π) ⊆ T := fun θ hθ => by
    refine ⟨⟨hθ.1, by linarith [hθ.2]⟩, ?_⟩
    rw [← dirVec_add_int_mul θ 1]
    exact h' _ ⟨by push_cast; linarith [hθ.1], by push_cast; linarith [hθ.2]⟩
  have hdisj : Disjoint (Set.Ico c' (min (c' + α) (2 * π))) (Set.Ico 0 (c' + α - 2 * π)) := by
    rw [Set.disjoint_left]; intro θ h1 h2; linarith [h1.1, h2.2]
  have hvol : MeasureTheory.volume (Set.Ico c' (min (c' + α) (2 * π)) ∪
      Set.Ico 0 (c' + α - 2 * π)) = ENNReal.ofReal α := by
    rw [MeasureTheory.measure_union hdisj measurableSet_Ico, Real.volume_Ico, Real.volume_Ico]
    rcases le_or_gt (c' + α) (2 * π) with hle | hlt
    · rw [min_eq_left hle, sub_zero,
        ENNReal.ofReal_of_nonpos (show c' + α - 2 * π ≤ 0 by linarith), add_zero,
        add_sub_cancel_left]
    · rw [min_eq_right hlt.le, sub_zero, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
  have hTfin : MeasureTheory.volume T ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono (fun θ h => h.1))
  have hle := MeasureTheory.measure_mono (μ := MeasureTheory.volume) (Set.union_subset hT1 hT2)
  rw [hvol] at hle
  have := ENNReal.toReal_mono hTfin hle
  rwa [ENNReal.toReal_ofReal hα] at this

/-- Multiplicity bound: if every direction lies in at most `M` of the closed sets `Q i`, the
direction measures sum to at most `2πM`. -/
theorem sum_dirMeasure_le {ι : Type*} (A : Finset ι) (Q : ι → Set Pt)
    (hQ : ∀ i ∈ A, IsClosed (Q i)) (M : ℕ)
    (hM : ∀ θ : ℝ, (A.filter (fun i => dirVec θ ∈ Q i)).card ≤ M) :
    ∑ i ∈ A, dirMeasure (Q i) ≤ 2 * π * M := by
  classical
  set I : Set ℝ := Set.Ico 0 (2 * π)
  let C : ι → Set ℝ := fun i => {θ | θ ∈ I ∧ dirVec θ ∈ Q i}
  have hCm : ∀ i ∈ A, MeasurableSet (C i) := fun i hi =>
    measurableSet_Ico.inter ((hQ i hi).preimage continuous_dirVec).measurableSet
  have hpt : ∀ θ, ∑ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ ≤
      I.indicator (fun _ => (M : ENNReal)) θ := by
    intro θ
    by_cases hI : θ ∈ I
    · rw [Set.indicator_of_mem hI]
      simp only [Set.indicator_apply]
      rw [Finset.sum_boole]
      have : (A.filter (fun i => θ ∈ C i)).card ≤ M := by
        refine le_trans (Finset.card_le_card ?_) (hM θ)
        intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, hi.2.2⟩
      exact_mod_cast this
    · rw [Set.indicator_of_notMem hI]
      have : ∀ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ = 0 := fun i _ =>
        Set.indicator_of_notMem (fun h => hI h.1) _
      rw [Finset.sum_eq_zero this]
  have hsum : ∑ i ∈ A, MeasureTheory.volume (C i) ≤ M * ENNReal.ofReal (2 * π) := by
    calc ∑ i ∈ A, MeasureTheory.volume (C i)
        = ∑ i ∈ A, ∫⁻ θ, (C i).indicator (fun _ => (1 : ENNReal)) θ := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [MeasureTheory.lintegral_indicator_const (hCm i hi), one_mul]
      _ = ∫⁻ θ, ∑ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ := by
          rw [MeasureTheory.lintegral_finsetSum]
          exact fun i hi => measurable_const.indicator (hCm i hi)
      _ ≤ ∫⁻ θ, I.indicator (fun _ => (M : ENNReal)) θ := MeasureTheory.lintegral_mono hpt
      _ = M * ENNReal.ofReal (2 * π) := by
          rw [MeasureTheory.lintegral_indicator_const measurableSet_Ico, Real.volume_Ico,
            sub_zero]
  have hfin : ∀ i ∈ A, MeasureTheory.volume (C i) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono (fun θ h => h.1))
  have h1 : ∑ i ∈ A, dirMeasure (Q i) = (∑ i ∈ A, MeasureTheory.volume (C i)).toReal := by
    rw [ENNReal.toReal_sum hfin]; rfl
  rw [h1]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
    ENNReal.ofReal_ne_top) hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at h2
  linarith

theorem card_mul_le_of_dirMeasure {ι : Type*} (A : Finset ι) (Q : ι → Set Pt)
    (hQ : ∀ i ∈ A, IsClosed (Q i)) (M : ℕ)
    (hM : ∀ θ : ℝ, (A.filter (fun i => dirVec θ ∈ Q i)).card ≤ M) {α : ℝ}
    (hα : ∀ i ∈ A, α ≤ dirMeasure (Q i)) : (A.card : ℝ) * α ≤ 2 * π * M := by
  have h := sum_dirMeasure_le A Q hQ M hM
  have h2 : ∑ _i ∈ A, α ≤ ∑ i ∈ A, dirMeasure (Q i) := Finset.sum_le_sum hα
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  linarith

/-! ## Caps and windows of directions -/

/-- The *cap* of unit vectors on the short arc between `a` and `b`. -/
def cap (a b : Pt) : Set Pt := {m | 1 + inner ℝ a b ≤ inner ℝ m (a + b)}

/-- The *window* of half-width `ε` (chordal) around `a`. -/
def window (a : Pt) (ε : ℝ) : Set Pt := {m | ‖m - a‖ ≤ ε}

theorem isClosed_cap (a b : Pt) : IsClosed (cap a b) := by
  exact isClosed_le continuous_const (by fun_prop)

theorem isClosed_window (a : Pt) (ε : ℝ) : IsClosed (window a ε) := by
  exact isClosed_le (by fun_prop) continuous_const

/-- The cap between two non-antipodal unit vectors has direction measure `≥ ∠(a, b)`. -/
theorem ang_le_dirMeasure_cap {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : 0 < 1 + inner ℝ a b) : ang a b ≤ dirMeasure (cap a b) := by
  set g := a + b with hg_def
  set A := ang a b with hA_def
  have hk : inner ℝ a b = Real.cos A := by
    have := InnerProductGeometry.cos_angle_mul_norm_mul_norm a b
    rw [ha, hb, mul_one, mul_one] at this; exact this.symm
  have hA0 : 0 ≤ A := InnerProductGeometry.angle_nonneg a b
  have hAπ : A ≤ π := InnerProductGeometry.angle_le_pi a b
  have hpi := Real.pi_pos
  have hg2 : ‖g‖ ^ 2 = 2 + 2 * inner ℝ a b := by rw [hg_def, norm_add_sq_real, ha, hb]; ring
  have hc2 : 0 ≤ Real.cos (A / 2) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hhalf : Real.cos (A / 2) ^ 2 = 1 / 2 + Real.cos A / 2 := by
    rw [Real.cos_sq, show 2 * (A / 2) = A by ring]
  have hgc : ‖g‖ = 2 * Real.cos (A / 2) := by
    have : ‖g‖ ^ 2 = (2 * Real.cos (A / 2)) ^ 2 := by rw [hg2, mul_pow, hhalf, hk]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 this
  have hgpos : 0 < ‖g‖ := by
    have : 0 < ‖g‖ ^ 2 := by rw [hg2]; linarith
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; norm_num at this)
  have hu : ‖‖g‖⁻¹ • g‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgpos.ne']
  obtain ⟨θb, hθb⟩ := exists_dirVec hu
  have hgθ : g = ‖g‖ • dirVec θb := by rw [hθb, smul_smul, mul_inv_cancel₀ hgpos.ne', one_smul]
  refine le_dirMeasure_of_Icc hA0 (by linarith) (c := θb - A / 2) fun θ hθ => ?_
  show 1 + inner ℝ a b ≤ inner ℝ (dirVec θ) (a + b)
  rw [← hg_def, hgθ, real_inner_smul_right, inner_dirVec]
  have habs : |θ - θb| ≤ A / 2 := abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hcos : Real.cos (A / 2) ≤ Real.cos (θ - θb) := by
    rw [← Real.cos_abs (θ - θb)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
  rw [hgc, hk]
  nlinarith

theorem two_mul_le_dirMeasure_window {a : Pt} (ha : ‖a‖ = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε ≤ π) : 2 * ε ≤ dirMeasure (window a ε) := by
  obtain ⟨θa, rfl⟩ := exists_dirVec ha
  refine le_dirMeasure_of_Icc (by linarith) (by linarith) (c := θa - ε) fun θ hθ => ?_
  show ‖dirVec θ - dirVec θa‖ ≤ ε
  refine (norm_dirVec_sub_le θ θa).trans ?_
  exact abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-! ## Planar lemmas on caps and wedges -/

/-- A unit vector in the cap of `(a, b)` (`det(a, b) > 0`) is between them. -/
theorem det2_nonneg_of_mem_cap {a b m : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hm : ‖m‖ = 1)
    (hab : 0 < det2 a b) (h : m ∈ cap a b) : 0 ≤ det2 a m ∧ 0 ≤ det2 m b := by
  sorry

/-- A unit vector between `a` and `b` (`det(a, b) > 0`) is in their cap. -/
theorem mem_cap_of_det2 {a b m : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hm : ‖m‖ = 1)
    (hab : 0 < det2 a b) (h1 : 0 ≤ det2 a m) (h2 : 0 ≤ det2 m b) : m ∈ cap a b := by
  sorry

/-- Two unit vectors `u, w` on the clockwise side of `n`, with `u` closer to `n`: `u` is
counter-clockwise from `w`. -/
theorem det2_tail {u w n : Pt} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hn : ‖n‖ = 1)
    (hun : 0 ≤ det2 u n) (hwn : 0 ≤ det2 w n) (huw : inner ℝ w n ≤ inner ℝ u n)
    (hw1 : -1 < inner ℝ w n) : 0 ≤ det2 w u := by
  sorry

/-- **Wedge separation.**  If `d · a ≤ 0 ≤ d · b` with `det(a, b) > 0` and both unit normals in
the half-plane `{n · g ≥ c}`, then `d` makes a small angle with `g^⊥`: `c|d| ≤ det(g, d)`. -/
theorem wedge_sep {a b g d : Pt} {c : ℝ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : 0 ≤ c)
    (hag : c ≤ inner ℝ a g) (hbg : c ≤ inner ℝ b g) (hab : 0 < det2 a b)
    (hda : inner ℝ d a ≤ 0) (hdb : 0 ≤ inner ℝ d b) : c * ‖d‖ ≤ det2 g d := by
  sorry

/-! ## Separated reals -/

/-- `c`-separated reals in `[a, b]` number at most `(b − a)/c + 1`. -/
theorem card_le_of_sep {c a : ℝ} (hc : 0 < c) (T : Finset ℝ) : ∀ b : ℝ, a ≤ b + c →
    (∀ x ∈ T, a ≤ x ∧ x ≤ b) → (∀ x ∈ T, ∀ y ∈ T, x ≠ y → c ≤ |x - y|) →
    (T.card : ℝ) ≤ (b - a) / c + 1 := by
  sorry

/-- One-sided count: `c`-separated values `s` on `G`, any two within `ℓ` when ordered. -/
theorem card_le_of_oneSided {G : Finset Pt} (s : Pt → ℝ) {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hsep : ∀ v ∈ G, ∀ w ∈ G, v ≠ w → c ≤ |s v - s w|)
    (hside : ∀ v ∈ G, ∀ w ∈ G, s v < s w → s w - s v ≤ ℓ) :
    (G.card : ℝ) ≤ ℓ / c + 1 := by
  sorry

/-! ## Configurations of points with outward normals -/

/-- A finite set `V` with unit outward normals: `1`-separated, strict chord inequalities. -/
structure NormalConfig (V : Finset Pt) (nrm : Pt → Pt) : Prop where
  unit : ∀ v ∈ V, ‖nrm v‖ = 1
  sep : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → 1 ≤ dist v w
  chord : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → inner ℝ (w - v) (nrm v) < 0

variable {V : Finset Pt} {nrm : Pt → Pt}

/-- Distinct points with normals in a common open half-plane have non-parallel normals. -/
theorem NormalConfig.det2_ne (hV : NormalConfig V nrm) {v w g : Pt} {c : ℝ} (hc : 0 < c)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) (hvg : c ≤ inner ℝ (nrm v) g)
    (hwg : c ≤ inner ℝ (nrm w) g) : det2 (nrm v) (nrm w) ≠ 0 := by
  sorry

/-- Oriented separation along `g^⊥`. -/
theorem NormalConfig.sep_det2 (hV : NormalConfig V nrm) {v w g : Pt} {c : ℝ} (hc : 0 ≤ c)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) (hvg : c ≤ inner ℝ (nrm v) g)
    (hwg : c ≤ inner ℝ (nrm w) g) (hdet : 0 < det2 (nrm v) (nrm w)) :
    c * dist w v ≤ det2 g (w - v) := by
  sorry

/-- Unoriented separation along `g^⊥`. -/
theorem NormalConfig.sep_abs (hV : NormalConfig V nrm) {v w g : Pt} {c : ℝ} (hc : 0 < c)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) (hvg : c ≤ inner ℝ (nrm v) g)
    (hwg : c ≤ inner ℝ (nrm w) g) : c * dist w v ≤ |det2 g (w - v)| := by
  sorry

/-- The points whose normals lie in the cap of a unit edge `pq` number at most `N`
(`N > 2/|n_p + n_q|`). -/
theorem NormalConfig.card_cap_le (hV : NormalConfig V nrm) {p q : Pt} (hp : p ∈ V) (hq : q ∈ V)
    (hpq : dist p q = 1) (hdet : 0 < det2 (nrm p) (nrm q)) {κ : ℝ} (hκ : 0 < κ)
    (hκp : κ ≤ ‖nrm p + nrm q‖) {N : ℕ} (hN : 2 / κ < N) :
    (V.filter (fun v => nrm v ∈ cap (nrm p) (nrm q))).card ≤ N := by
  sorry

/-- **Edge count** (KK / DD): unit edges with normals at angle `> β₀` and `|n_p + n_q| ≥ κ`,
degree `≤ D`, satisfy `#E · β₀ ≤ 2π·D·N` for any `N > 2/κ`. -/
theorem NormalConfig.card_mul_le_of_edges (hV : NormalConfig V nrm) {E : Finset (Sym2 Pt)}
    {β₀ κ : ℝ} {D N : ℕ}
    (hE : ∀ p q, s(p, q) ∈ E → p ∈ V ∧ q ∈ V ∧ dist p q = 1 ∧ β₀ < ang (nrm p) (nrm q) ∧
      κ ≤ ‖nrm p + nrm q‖)
    (hdeg : ∀ p, (E.filter (fun e => p ∈ e)).card ≤ D) (hβ₀ : 0 ≤ β₀) (hκ : 0 < κ)
    (hN : 2 / κ < N) : (E.card : ℝ) * β₀ ≤ 2 * π * (D * N) := by
  sorry

/-- The discrete walk: a window-neighbour `y` of `v` on the side away from `x` is within `412`
of `v`. -/
theorem walk_close {v x y m nv ny : Pt} {R : ℝ} (hR : 10 ^ 4 ≤ R) (hm : ‖m‖ = 1)
    (hnv : ‖nv - m‖ ≤ 1 / 800) (hny : ‖ny - m‖ ≤ 1 / 800) (hxv : dist v x ≤ R)
    (hR1 : R - 1 ≤ dist v x) (hs : dist v x / 201 ≤ |det2 nv (x - v)|) (hyx : dist y x ≤ R)
    (hcv : inner ℝ (y - v) nv < 0) (hcy : 0 < inner ℝ (y - v) ny)
    (hsep : 99 / 100 * ‖y - v‖ ≤ |det2 m (y - v)|)
    (hside : det2 m (y - v) * det2 m (x - v) < 0) : ‖y - v‖ ≤ 412 := by
  sorry

/-- The side of the walk is well defined: `det(m, x − v) ≠ 0`. -/
theorem walk_side_ne {v x m nv : Pt} {R : ℝ} (hR : 10 ^ 4 ≤ R) (hm : ‖m‖ = 1)
    (hnv : ‖nv - m‖ ≤ 1 / 800) (hR1 : R - 1 ≤ dist v x)
    (hs : dist v x / 201 ≤ |det2 nv (x - v)|) : det2 m (x - v) ≠ 0 := by
  sorry

/-- **Walk count** ((c2)): points `v ∈ W ⊆ V` at depth `≤ 1` in a disc `D(x_v, R) ⊇ V` with
`|det(n_v, x_v − v)| ≥ |x_v − v|/201` satisfy `#W/400 ≤ 2π·834`. -/
theorem NormalConfig.card_walk_mul_le (hV : NormalConfig V nrm) {W : Finset Pt} (hW : W ⊆ V)
    {R : ℝ} (hR : 10 ^ 4 ≤ R)
    (hx : ∀ v ∈ W, ∃ x : Pt, (∀ y ∈ V, dist y x ≤ R) ∧ R - 1 ≤ dist v x ∧
      dist v x / 201 ≤ |det2 (nrm v) (x - v)|) :
    (W.card : ℝ) * (1 / 400) ≤ 2 * π * 834 := by
  sorry

end

end Curve

end Erdos132Main

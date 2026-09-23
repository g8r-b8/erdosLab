import Erdos.E132MainDefs
import Erdos.E132Layer

/-!
# Erdős Problem 132, `54/37` theorem — degenerate regime (§8)

`Δ > 1.94 Δ₂` and `n ≥ 4` ⇒ `μ(Δ₂) ≤ n + 1`.  Scale-invariant: no normalisation needed.

Steps: (1) no two disjoint diametral pairs; (2) the diameter graph is a star `{y} ∪ A`;
(3) `Δ₂`-pairs: none inside `B := X ∖ D`, at most one inside `A`, none between `y` and `A`, so
`μ(Δ₂) ≤ 1 + I` with `I` the `B–W` incidences, `W := {y} ∪ A`; (4) `I ≤ |B| + |W|`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open Erdos132Convex (orient)
open Erdos132Layer (sqd dist_sq_eq_sqd dist_eq_iff_sqd dist_le_iff_sqd sqd_comm sqd_pos_of_ne)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

namespace Degen

/-! ## Helpers (namespaced to avoid clashes with `E132MainLocal`) -/

theorem mem_distSetS' {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    dist x y ∈ distSetS X := by
  simp only [distSetS, pairsS, mem_image, mem_filter]
  exact ⟨s(x, y), ⟨Finset.mk_mem_sym2_iff.2 ⟨hx, hy⟩, by simpa using hxy⟩, rfl⟩

theorem nonneg_of_mem {d : ℝ} (hd : d ∈ distSetS X) : 0 ≤ d := by
  simp only [distSetS, mem_image] at hd
  obtain ⟨z, -, rfl⟩ := hd
  induction z using Sym2.ind with
  | _ a b => exact (dist_nonneg : 0 ≤ dist a b)

theorem diam_nonneg' (X : Finset Pt) : 0 ≤ diam X := by
  unfold diam; split_ifs with h
  · exact nonneg_of_mem (max'_mem _ h)
  · exact le_rfl

theorem dist2_nonneg' (X : Finset Pt) : 0 ≤ dist2 X := by
  unfold dist2; split_ifs with h
  · exact nonneg_of_mem (mem_of_mem_erase (max'_mem _ h))
  · exact le_rfl

theorem le_diam {d : ℝ} (hd : d ∈ distSetS X) : d ≤ diam X := by
  unfold diam; rw [dite_eq_left ⟨_, hd⟩]; exact le_max' _ _ hd

theorem dist_le_diam' {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) : dist x y ≤ diam X := by
  by_cases hxy : x = y
  · subst hxy; rw [dist_self]; exact diam_nonneg' X
  · exact le_diam (mem_distSetS' hx hy hxy)

/-- No distance strictly between `Δ₂` and `Δ`. -/
theorem gap {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) : dist x y ≤ dist2 X ∨ dist x y = diam X := by
  by_cases hne : dist x y = diam X
  · exact Or.inr hne
  left
  by_cases hxy : x = y
  · subst hxy; rw [dist_self]; exact dist2_nonneg' X
  · have hm : dist x y ∈ (distSetS X).erase (diam X) := mem_erase.2 ⟨hne, mem_distSetS' hx hy hxy⟩
    unfold dist2; rw [dite_eq_left ⟨_, hm⟩]; exact le_max' _ _ hm

/-- The diameter is attained when `X` has two points. -/
theorem exists_diam_pair (h2 : 2 ≤ X.card) : ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ dist a b = diam X := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < X.card)
  have hne : (distSetS X).Nonempty := ⟨_, mem_distSetS' ha hb hab⟩
  have hm : diam X ∈ distSetS X := by unfold diam; rw [dite_eq_left hne]; exact max'_mem _ _
  simp only [distSetS, pairsS, mem_image, mem_filter] at hm
  obtain ⟨z, ⟨hz, hzd⟩, hzv⟩ := hm
  induction z using Sym2.ind with
  | _ u v =>
    refine ⟨u, (Finset.mk_mem_sym2_iff.1 hz).1, v, (Finset.mk_mem_sym2_iff.1 hz).2, ?_, hzv⟩
    simpa using hzd

/-- Squared form of the gap. -/
theorem gap_sq {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    sqd x y ≤ dist2 X ^ 2 ∨ sqd x y = diam X ^ 2 := by
  rw [← dist_sq_eq_sqd]
  rcases gap hx hy with h | h
  · exact Or.inl (pow_le_pow_left₀ dist_nonneg h 2)
  · exact Or.inr (by rw [h])

theorem sqd_le_diam {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) : sqd x y ≤ diam X ^ 2 := by
  rw [← dist_sq_eq_sqd]; exact pow_le_pow_left₀ dist_nonneg (dist_le_diam' hx hy) 2

/-- `1.94² Δ₂² < Δ²` in the degenerate regime. -/
theorem sq_gap (hdeg : 1.94 * dist2 X < diam X) : 37636 * dist2 X ^ 2 < 10000 * diam X ^ 2 := by
  have h0 := dist2_nonneg' X
  nlinarith

/-! ## Real-number cores -/

/-- Rhombus: `P₁P₂P₃P₄` with four sides of squared length `D`, `P₁ ≠ P₃`, `P₂ ≠ P₄` has
`|P₁P₃|² + |P₂P₄|² = 4D` (here `P₁ = 0`, `P₂ = x`, `P₃ = y`, `P₄ = z`). -/
theorem rhombus_real {x0 x1 y0 y1 z0 z1 D : ℝ} (h1 : x0 ^ 2 + x1 ^ 2 = D)
    (h2 : (x0 - y0) ^ 2 + (x1 - y1) ^ 2 = D) (h3 : (z0 - y0) ^ 2 + (z1 - y1) ^ 2 = D)
    (h4 : z0 ^ 2 + z1 ^ 2 = D) (hy : y0 ^ 2 + y1 ^ 2 ≠ 0)
    (hxz : (x0 - z0) ^ 2 + (x1 - z1) ^ 2 ≠ 0) :
    (y0 ^ 2 + y1 ^ 2) + ((x0 - z0) ^ 2 + (x1 - z1) ^ 2) = 4 * D := by
  -- `e = x − z` is orthogonal to `y` and to `s = x + z`
  have ey : (x0 - z0) * y0 + (x1 - z1) * y1 = 0 := by linear_combination (h3 - h2 + h1 - h4) / 2
  have es : (x0 - z0) * (x0 + z0) + (x1 - z1) * (x1 + z1) = 0 := by linear_combination h1 - h4
  -- hence `det(y, s) = 0`
  have hd0 : (x0 - z0) * (y0 * (x1 + z1) - y1 * (x0 + z0)) = 0 := by
    linear_combination (x1 + z1) * ey - y1 * es
  have hd1 : (x1 - z1) * (y0 * (x1 + z1) - y1 * (x0 + z0)) = 0 := by
    linear_combination -(x0 + z0) * ey + y0 * es
  have hdet : y0 * (x1 + z1) - y1 * (x0 + z0) = 0 := by
    by_contra hne
    have a : x0 - z0 = 0 := (mul_eq_zero.1 hd0).resolve_right hne
    have b : x1 - z1 = 0 := (mul_eq_zero.1 hd1).resolve_right hne
    exact hxz (by rw [a, b]; ring)
  -- `s · y = |y|²`
  have sy : (x0 + z0) * y0 + (x1 + z1) * y1 = y0 ^ 2 + y1 ^ 2 := by
    linear_combination (h1 - h2 + h4 - h3) / 2
  -- so `s = y`
  have s0 : (y0 ^ 2 + y1 ^ 2) * (x0 + z0 - y0) = 0 := by
    linear_combination y0 * sy - y1 * hdet
  have s1 : (y0 ^ 2 + y1 ^ 2) * (x1 + z1 - y1) = 0 := by
    linear_combination y1 * sy + y0 * hdet
  have e0 := (mul_eq_zero.1 s0).resolve_left hy
  have e1 := (mul_eq_zero.1 s1).resolve_left hy
  have hy0 : y0 = x0 + z0 := by linarith
  have hy1 : y1 = x1 + z1 := by linarith
  subst hy0 hy1
  linear_combination 2 * h1 + 2 * h4

/-- Arc bound: `a` the apex of an equilateral triangle `abc` of side² `D`, `p` on the circle about
`a` of radius² `D`; then `p` is not within `Δ₂` of both `b` and `c` (`(2 sin 15°)² > 1/1.94²`). -/
theorem arc_real {b0 b1 c0 c1 p0 p1 D q : ℝ} (hb : b0 ^ 2 + b1 ^ 2 = D) (hc : c0 ^ 2 + c1 ^ 2 = D)
    (hbc : (b0 - c0) ^ 2 + (b1 - c1) ^ 2 = D) (hp : p0 ^ 2 + p1 ^ 2 = D)
    (hpb : (p0 - b0) ^ 2 + (p1 - b1) ^ 2 ≤ q) (hpc : (p0 - c0) ^ 2 + (p1 - c1) ^ 2 ≤ q)
    (hq : 37636 * q < 10000 * D) (hq0 : 0 ≤ q) : False := by
  have hs : (b0 + c0) ^ 2 + (b1 + c1) ^ 2 = 3 * D := by linear_combination 2 * hb + 2 * hc - hbc
  have e1 : 2 * (p0 * b0 + p1 * b1) = D + D - ((p0 - b0) ^ 2 + (p1 - b1) ^ 2) := by
    linear_combination hp + hb
  have e2 : 2 * (p0 * c0 + p1 * c1) = D + D - ((p0 - c0) ^ 2 + (p1 - c1) ^ 2) := by
    linear_combination hp + hc
  have hps : 2 * D - q ≤ p0 * (b0 + c0) + p1 * (b1 + c1) := by linarith
  have hcs : (p0 * (b0 + c0) + p1 * (b1 + c1)) ^ 2 ≤ 3 * D ^ 2 := by
    have : (p0 * (b0 + c0) + p1 * (b1 + c1)) ^ 2 + (p0 * (b1 + c1) - p1 * (b0 + c0)) ^ 2 =
        D * (3 * D) := by linear_combination (p0 ^ 2 + p1 ^ 2) * hs + 3 * D * hp
    nlinarith [sq_nonneg (p0 * (b1 + c1) - p1 * (b0 + c0))]
  have h2 : 0 ≤ 2 * D - q := by linarith
  have h3 : (2 * D - q) ^ 2 ≤ 3 * D ^ 2 := by
    have := mul_le_mul hps hps h2 (h2.trans hps)
    nlinarith
  have hD : 0 < D := by linarith
  have hprod : 0 ≤ (10000 * D - 37636 * q) * (140544 * D - 37636 * q) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [pow_pos hD 2]

/-- Circumradius: a point within `Δ₂` of the three vertices of an equilateral triangle of side
`Δ` forces `3Δ₂² ≥ Δ²`. -/
theorem tri_real {u0 u1 v0 v1 w0 w1 t0 t1 D q : ℝ} (huv : (u0 - v0) ^ 2 + (u1 - v1) ^ 2 = D)
    (hvw : (v0 - w0) ^ 2 + (v1 - w1) ^ 2 = D) (huw : (u0 - w0) ^ 2 + (u1 - w1) ^ 2 = D)
    (htu : (t0 - u0) ^ 2 + (t1 - u1) ^ 2 ≤ q) (htv : (t0 - v0) ^ 2 + (t1 - v1) ^ 2 ≤ q)
    (htw : (t0 - w0) ^ 2 + (t1 - w1) ^ 2 ≤ q) : D ≤ 3 * q := by
  nlinarith [sq_nonneg (3 * t0 - u0 - v0 - w0), sq_nonneg (3 * t1 - u1 - v1 - w1)]

/-! ## Point-level versions -/

theorem sqd_coord (x y : Pt) : sqd x y = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := rfl

theorem rhombus {P₁ P₂ P₃ P₄ : Pt} {D : ℝ} (h1 : sqd P₁ P₂ = D) (h2 : sqd P₂ P₃ = D)
    (h3 : sqd P₃ P₄ = D) (h4 : sqd P₄ P₁ = D) (h13 : P₁ ≠ P₃) (h24 : P₂ ≠ P₄) :
    sqd P₁ P₃ + sqd P₂ P₄ = 4 * D := by
  have a := sqd_pos_of_ne h13
  have b := sqd_pos_of_ne h24
  simp only [sqd_coord] at *
  have := rhombus_real (x0 := P₂ 0 - P₁ 0) (x1 := P₂ 1 - P₁ 1) (y0 := P₃ 0 - P₁ 0)
    (y1 := P₃ 1 - P₁ 1) (z0 := P₄ 0 - P₁ 0) (z1 := P₄ 1 - P₁ 1) (D := D)
    (by linear_combination h1) (by linear_combination h2) (by linear_combination h3)
    (by linear_combination h4) (by nlinarith) (by nlinarith)
  linear_combination this

theorem arc {a b c p : Pt} {D q : ℝ} (hab : sqd a b = D) (hac : sqd a c = D) (hbc : sqd b c = D)
    (hap : sqd a p = D) (hpb : sqd p b ≤ q) (hpc : sqd p c ≤ q) (hq : 37636 * q < 10000 * D)
    (hq0 : 0 ≤ q) : False := by
  simp only [sqd_coord] at *
  exact arc_real (b0 := b 0 - a 0) (b1 := b 1 - a 1) (c0 := c 0 - a 0) (c1 := c 1 - a 1)
    (p0 := p 0 - a 0) (p1 := p 1 - a 1) (by linear_combination hab) (by linear_combination hac)
    (by linear_combination hbc) (by linear_combination hap) (by linarith) (by linarith) hq hq0

theorem tri {u v w t : Pt} {D q : ℝ} (huv : sqd u v = D) (hvw : sqd v w = D) (huw : sqd u w = D)
    (htu : sqd t u ≤ q) (htv : sqd t v ≤ q) (htw : sqd t w ≤ q) : D ≤ 3 * q := by
  simp only [sqd_coord] at *
  exact tri_real huv hvw huw htu htv htw

theorem diam_pos (hdeg : 1.94 * dist2 X < diam X) : 0 < diam X := by
  have := dist2_nonneg' X; linarith

theorem sqd_eq_diam {x y : Pt} (hdeg : 1.94 * dist2 X < diam X) (h : dist x y = diam X) :
    sqd x y = diam X ^ 2 := (dist_eq_iff_sqd (diam_pos hdeg).le).1 h

theorem sqd_le_dist2 {x y : Pt} (h : dist x y ≤ dist2 X) : sqd x y ≤ dist2 X ^ 2 :=
  (dist_le_iff_sqd (dist2_nonneg' X)).1 h

end Degen

open Degen

/-- **[C10]** with `q = 1/1.94²`: `1 + 3q < 2`, `q < 2 − √3 = (2 sin 15°)²`, `q < 1/3`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c10 :
    (1 : ℝ) + 3 * (1 / 1.94 ^ 2) < 2 ∧ (1 : ℝ) / 1.94 ^ 2 < 2 - √3 ∧
      (1 : ℝ) / 1.94 ^ 2 < 1 / 3 := by
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by norm_num, ?_, by norm_num⟩
  norm_num; linarith

/-- Cross-distance identity (Step 1): `Σ|a − b|² = |xx′|² + |zz′|² + 4|m − m′|²`
(written with `(x + x′) − (z + z′) = 2(m − m′)`).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem cross_dist_identity (x x' z z' : Pt) :
    dist x z ^ 2 + dist x z' ^ 2 + dist x' z ^ 2 + dist x' z' ^ 2 =
      dist x x' ^ 2 + dist z z' ^ 2 + dist (x + x') (z + z') ^ 2 := by
  have key : ∀ a b : Pt, dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
    intro a b
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
  simp only [key, PiLp.add_apply]
  ring

/-- **Step 1**: no two disjoint diametral pairs when `Δ > 1.94Δ₂`.

TODO: prove.
What's missing: at least two cross distances equal `Δ` ([C10] + `cross_dist_identity`);
disjoint cross pairs ⇒ rhombus of side `Δ` with a diagonal `≥ √2Δ`; sharing a point ⇒
equilateral triangle and a distance in `[2Δ sin 15°, Δ)`, hence in `(Δ₂, Δ)`.
Acceptance: no `sorry`.
Depends on: `c10`, `cross_dist_identity`. Difficulty L. -/
theorem degen_step1 (hdeg : 1.94 * dist2 X < diam X) {x x' z z' : Pt} (hx : x ∈ X)
    (hx' : x' ∈ X) (hz : z ∈ X) (hz' : z' ∈ X) (h₁ : dist x x' = diam X)
    (h₂ : dist z z' = diam X) (hxz : x ≠ z) (hxz' : x ≠ z') (hx'z : x' ≠ z) (hx'z' : x' ≠ z') :
    False := by
  have hq := sq_gap hdeg
  have hr0 := dist2_nonneg' X
  have hD := diam_pos hdeg
  have hD2 : 0 < diam X ^ 2 := by positivity
  have sxx := sqd_eq_diam hdeg h₁
  have szz := sqd_eq_diam hdeg h₂
  have g1 := gap_sq hx hz
  have g2 := gap_sq hx hz'
  have g3 := gap_sq hx' hz
  have g4 := gap_sq hx' hz'
  have l1 := sqd_le_diam hx hz
  have l2 := sqd_le_diam hx hz'
  have l3 := sqd_le_diam hx' hz
  have l4 := sqd_le_diam hx' hz'
  set D := diam X ^ 2 with hDdef
  set r := dist2 X ^ 2 with hrdef
  have hr : 0 ≤ r := by positivity
  have hsum : 2 * D ≤ sqd x z + sqd x z' + sqd x' z + sqd x' z' := by
    have := cross_dist_identity x x' z z'
    simp only [dist_sq_eq_sqd] at this
    rw [this, sxx, szz]; nlinarith [sqd_comm (x + x') (z + z'), dist_sq_eq_sqd (x + x') (z + z'),
      sq_nonneg (dist (x + x') (z + z'))]
  have n14 : sqd x z = D → sqd x' z' = D → False := fun h1 h4 => by
    have := rhombus h1 szz (by rw [sqd_comm]; exact h4) (by rw [sqd_comm]; exact sxx) hxz' hx'z.symm
    rw [sqd_comm z x'] at this
    linarith
  have n23 : sqd x z' = D → sqd x' z = D → False := fun h2 h3 => by
    have := rhombus h2 (by rw [sqd_comm]; exact szz) (by rw [sqd_comm]; exact h3)
      (by rw [sqd_comm]; exact sxx) hxz hx'z'.symm
    rw [sqd_comm z' x'] at this
    linarith
  have hq' : 37636 * r < 10000 * D := hq
  have a12 : sqd x z = D → sqd x z' = D → sqd x' z ≤ r → sqd x' z' ≤ r → False :=
    fun h1 h2 h3 h4 => arc h1 h2 szz sxx h3 h4 hq' hr
  have a34 : sqd x' z = D → sqd x' z' = D → sqd x z ≤ r → sqd x z' ≤ r → False :=
    fun h3 h4 h1 h2 => arc h3 h4 szz (by rw [sqd_comm]; exact sxx) h1 h2 hq' hr
  have a13 : sqd x z = D → sqd x' z = D → sqd x z' ≤ r → sqd x' z' ≤ r → False :=
    fun h1 h3 h2 h4 => arc (by rw [sqd_comm]; exact h1) (by rw [sqd_comm]; exact h3) sxx szz
      (by rw [sqd_comm]; exact h2) (by rw [sqd_comm]; exact h4) hq' hr
  have a24 : sqd x z' = D → sqd x' z' = D → sqd x z ≤ r → sqd x' z ≤ r → False :=
    fun h2 h4 h1 h3 => arc (by rw [sqd_comm]; exact h2) (by rw [sqd_comm]; exact h4) sxx
      (by rw [sqd_comm]; exact szz) (by rw [sqd_comm]; exact h1) (by rw [sqd_comm]; exact h3) hq' hr
  rcases g1 with h1 | h1 <;> rcases g2 with h2 | h2 <;> rcases g3 with h3 | h3 <;>
    rcases g4 with h4 | h4 <;>
    first
    | linarith
    | exact n14 h1 h4
    | exact n23 h2 h3
    | exact a12 h1 h2 h3 h4
    | exact a34 h3 h4 h1 h2
    | exact a13 h1 h3 h2 h4
    | exact a24 h2 h4 h1 h3

/-- **Step 2**: the diameter graph is a star with centre `y`.

TODO: prove.
What's missing: by Step 1 it is a star or a triangle; a triangle with a 4th point is impossible
(`Δ₂² < Δ²/3` = circumradius², [C10]).
Acceptance: no `sorry`.
Depends on: `degen_step1`, `c10`. Difficulty M. -/
theorem degen_star (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) :
    ∃ y ∈ X, ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y := by
  have nd : ∀ {a b c d : Pt}, a ∈ X → b ∈ X → c ∈ X → d ∈ X → dist a b = diam X →
      dist c d = diam X → a ≠ c → a ≠ d → b ≠ c → b ≠ d → False :=
    fun ha hb hc hd h1 h2 h3 h4 h5 h6 => degen_step1 hdeg ha hb hc hd h1 h2 h3 h4 h5 h6
  obtain ⟨u, hu, v, hv, huv, duv⟩ := exists_diam_pair (by omega : 2 ≤ X.card)
  by_cases hU : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = u ∨ b = u
  · exact ⟨u, hu, hU⟩
  by_cases hV : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = v ∨ b = v
  · exact ⟨v, hv, hV⟩
  exfalso
  push Not at hU hV
  obtain ⟨a, ha, b, hb, hab, dab, hau, hbu⟩ := hU
  obtain ⟨c, hc, d, hd, hcd, dcd, hcv, hdv⟩ := hV
  -- an edge `(v, w)` with `w ≠ u`
  obtain ⟨w, hw, dvw, hwu, hwv⟩ : ∃ w ∈ X, dist v w = diam X ∧ w ≠ u ∧ w ≠ v := by
    by_cases hav : a = v
    · subst hav; exact ⟨b, hb, dab, hbu, hab.symm⟩
    by_cases hbv : b = v
    · subst hbv; exact ⟨a, ha, by rw [dist_comm]; exact dab, hau, hab⟩
    exact (nd ha hb hu hv dab duv hau hav hbu hbv).elim
  -- an edge `(u, w')` with `w' ≠ v`
  obtain ⟨w', hw', duw', hw'v, hw'u⟩ : ∃ w ∈ X, dist u w = diam X ∧ w ≠ v ∧ w ≠ u := by
    by_cases hcu : c = u
    · subst hcu; exact ⟨d, hd, dcd, hdv, hcd.symm⟩
    by_cases hdu : d = u
    · subst hdu; exact ⟨c, hc, by rw [dist_comm]; exact dcd, hcv, hcd⟩
    exact (nd hc hd hu hv dcd duv hcu hcv hdu hdv).elim
  have hww : w = w' := by
    by_contra hne
    exact nd hv hw hu hw' dvw duw' (Ne.symm huv) (Ne.symm hw'v) hwu hne
  subst hww
  -- a fourth point
  obtain ⟨t, ht, htn⟩ := exists_mem_notMem_of_card_lt_card
    (s := ({u, v, w} : Finset Pt)) (t := X) (by
      have := card_le_three (a := u) (b := v) (c := w); omega)
  simp only [mem_insert, mem_singleton, not_or] at htn
  obtain ⟨htu, htv, htw⟩ := htn
  have fu : dist t u ≤ dist2 X := (gap ht hu).resolve_right fun h =>
    nd ht hu hv hw h dvw htv htw huv (Ne.symm hwu)
  have fv : dist t v ≤ dist2 X := (gap ht hv).resolve_right fun h =>
    nd ht hv hu hw h duw' htu htw (Ne.symm huv) (Ne.symm hwv)
  have fw : dist t w ≤ dist2 X := (gap ht hw).resolve_right fun h =>
    nd ht hw hu hv h duv htu htv hwu hwv
  have := tri (sqd_eq_diam hdeg duv) (sqd_eq_diam hdeg dvw) (sqd_eq_diam hdeg duw')
    (sqd_le_dist2 fu) (sqd_le_dist2 fv) (sqd_le_dist2 fw)
  have hq := sq_gap hdeg
  have := dist2_nonneg' X
  nlinarith

/-- `W := {y} ∪ Diam(y)` (the diametral points for a star centre `y`). -/
def Wset (X : Finset Pt) (y : Pt) : Finset Pt := insert y (partners X (diam X) y)

/-- `B := X ∖ W`. -/
def Bset (X : Finset Pt) (y : Pt) : Finset Pt := X \ Wset X y

/-- `I`: incidences `(b, w) ∈ B × W` with `|bw| = Δ₂`. -/
def incid (X : Finset Pt) (y : Pt) : ℕ :=
  ((Bset X y ×ˢ Wset X y).filter (fun bw => dist bw.1 bw.2 = dist2 X)).card

/-- **Step 3a**: no `Δ₂`-pair inside `B` (`diam K < Δ₂`: lens bounding box, [C10]).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `ball_polygon_a`-type facts, `c10`. Difficulty M. -/
theorem degen_B_no_pair (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt}
    (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    mult (Bset X y) (dist2 X) = 0 := by
  sorry

/-- **Step 3b**: at most one `Δ₂`-pair inside `A = Diam(y)` (the two extreme points of the arc).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `c10`, `degen_star`. Difficulty M. -/
theorem degen_A_le_one (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt}
    (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    mult (partners X (diam X) y) (dist2 X) ≤ 1 := by
  sorry

/-- **Step 3**: `μ(Δ₂) ≤ 1 + I`.

TODO: prove (split the `Δ₂`-pairs by where the endpoints lie; `y–A` pairs are at distance `Δ`).
Acceptance: no `sorry`.
Depends on: `degen_B_no_pair`, `degen_A_le_one`. Difficulty M. -/
theorem degen_step3 (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt} (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    mult X (dist2 X) ≤ 1 + incid X y := by
  sorry

/-- **Step 4 (incidence bound)** `I ≤ |B| + |W|`.

TODO: prove.
What's missing: each `J_w = C(w, Δ₂) ∩ K` is a single arc; no point is interior to two arcs
(internally tangent equal circles coincide); nondegenerate arcs are edges of `∂K`; injective
map `b ↦` following edge.
Acceptance: no `sorry`.
Depends on: circle geometry; `degen_B_no_pair`. Difficulty L–XL. -/
theorem degen_step4 (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) {y : Pt} (hy : y ∈ X)
    (hstar : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = diam X → a = y ∨ b = y) :
    incid X y ≤ (Bset X y).card + (Wset X y).card := by
  sorry

/-- **§8 Degenerate regime**: `Δ > 1.94Δ₂`, `n ≥ 4` ⇒ `μ(Δ₂) ≤ n + 1`.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `degen_star`, `degen_step3`, `degen_step4`. -/
theorem degenerate (h4 : 4 ≤ X.card) (hdeg : 1.94 * dist2 X < diam X) :
    (mult X (dist2 X) : ℝ) ≤ X.card + 1 := by
  obtain ⟨y, hy, hstar⟩ := degen_star h4 hdeg
  have h3 := degen_step3 h4 hdeg hy hstar
  have h4' := degen_step4 h4 hdeg hy hstar
  have hW : Wset X y ⊆ X := insert_subset hy (filter_subset _ _)
  have hc : (Bset X y).card + (Wset X y).card = X.card := card_sdiff_add_card_eq_card hW
  have : mult X (dist2 X) ≤ X.card + 1 := by omega
  exact_mod_cast this

end

end Erdos132Main

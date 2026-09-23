import Erdos.E132MainDefs

/-!
# Erdős Problem 132, `54/37` theorem — local geometry (§3) and bad edges (§5)

Lemmas 3.1–3.4, the rung identity, the T-edge/rung dichotomy, (T1), (T2), arc spacing,
turning along an arc; the lens lemma 5.1, lens-corner arc length 5.2, and the bad-edge counts
KK, DD, (c1), (c2).  See `E132MainDefs.lean` for the conventions.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## §3 Ball polygon and exact identities -/

/-- **Lemma 3.1(a)** `X ∖ D ⊆ K`.

TODO: prove.
What's missing: a non-diametral point has all its distances `≤ Δ₂` (no distance of `X` lies in
`(Δ₂, Δ)`, by definition of `dist2` as a max of `distSet ∖ {Δ}`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S–M. -/
theorem ball_polygon_a {y : Pt} (hy : y ∈ X) (hyD : y ∉ Dset X) : y ∈ KBall X := by
  sorry

/-- **Lemma 3.1(b)** `S ∖ D ⊆ ∂K`.

TODO: prove.
What's missing: `v ∈ K ∩ C(w, Δ₂)` with `K ⊆ D(w, Δ₂)` is not interior.
Acceptance: no `sorry`.
Depends on: `ball_polygon_a`. Difficulty S–M. -/
theorem ball_polygon_b {v : Pt} (hv : v ∈ Sset X) (hvD : v ∉ Dset X) : v ∈ frontier (KBall X) := by
  sorry

/-- **Lemma 3.1(c)** `dist(z, K) ≥ t` for `z ∈ D`.

TODO: prove.
What's missing: `K ⊆ D(x, Δ₂)` for the diametral partner `x` of `z`; triangle inequality.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem ball_polygon_c {z y : Pt} (hz : z ∈ Dset X) (hy : y ∈ KBall X) : tgap X ≤ dist z y := by
  sorry

/-- The direction field exists.

TODO: prove (choose partners; `p ∈ S ∖ D` → a `Δ₂`-partner, `p ∈ S ∩ D` → a diametral one).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem dirField_nonempty (X : Finset Pt) : Nonempty (DirField X) := by
  sorry

/-- `u_p` is a unit vector for `p ∈ S`.

TODO: prove (`partner p ≠ p` since its distance is `Δ₂ > 0` or `Δ > 0`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem DirField.norm_u (F : DirField X) {p : Pt} (hp : p ∈ Sset X) : ‖F.u p‖ = 1 := by
  sorry

/-- **Lemma 3.2(a)** For `p ∈ S ∩ D`: `(y − p)·u_p ≥ |y − p|²/(2Δ)`.

TODO: prove (law of cosines, `|y − x_p| ≤ Δ`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S–M. -/
theorem exact_identity_a (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∈ Dset X)
    (hy : y ∈ X) : dist y p ^ 2 / (2 * diam X) ≤ inner ℝ (y - p) (F.u p) := by
  sorry

/-- **Lemma 3.2(b)** For `p ∈ S ∖ D`: normal (`(y − p)·u_p ≥ |y − p|²/(2Δ₂)`) or exception
(`|y w_p| = Δ`).

TODO: prove (law of cosines; `|y w_p| ∈ [0, Δ₂] ∪ {Δ}`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S–M. -/
theorem exact_identity_b (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X)
    (hy : y ∈ X) :
    dist y p ^ 2 / (2 * dist2 X) ≤ inner ℝ (y - p) (F.u p) ∨ dist y (F.partner p) = diam X := by
  sorry

/-- **Rung identity, algebra** [C2]: `(1 + Δ₂² − Δ²)/(2Δ₂) = −τ` with `t = Δ − Δ₂`.

TODO: fill (Phase 2 leaf: `field_simp; ring`).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem rung_identity_alg (Δ Δ₂ : ℝ) (h : Δ₂ ≠ 0) :
    (1 + Δ₂ ^ 2 - Δ ^ 2) / (2 * Δ₂) =
      -((Δ - Δ₂) - (1 - (Δ - Δ₂) ^ 2) / (2 * Δ₂)) := by
  sorry

/-- [C2] `τ − t = (t² − 1)/(2Δ₂)`.

TODO: fill (Phase 2 leaf).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem tau_sub_tgap (X : Finset Pt) : tau X - tgap X = (tgap X ^ 2 - 1) / (2 * dist2 X) := by
  sorry

/-- [C2] `τ > 1 ⟺ t > 1` (for `t ≥ 0`, `Δ₂ > 0`).

TODO: fill (Phase 2 leaf).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem one_lt_tau_iff_alg {t Δ₂ : ℝ} (ht : 0 ≤ t) (hΔ : 0 < Δ₂) :
    1 < t - (1 - t ^ 2) / (2 * Δ₂) ↔ 1 < t := by
  sorry

/-- **Lemma 3.2(c)** Exception at distance 1: `(y − p)·u_p = −τ` **exactly**.

TODO: prove.
What's missing: law of cosines in `y p w_p` plus `rung_identity_alg`.
Acceptance: no `sorry`.
Depends on: `rung_identity_alg`, `DirField.norm_u`. Difficulty M. -/
theorem exact_identity_c (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X)
    (hexc : dist y (F.partner p) = diam X) (h1 : dist y p = 1) :
    inner ℝ (y - p) (F.u p) = - tau X := by
  sorry

/-- Exceptions at distance 1 exist only when `τ ≤ 1` (Cauchy–Schwarz on 3.2(c)).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `DirField.norm_u`. Difficulty S. -/
theorem tau_le_one_of_exception (F : DirField X) {p y : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X)
    (hexc : dist y (F.partner p) = diam X) (h1 : dist y p = 1) : tau X ≤ 1 := by
  sorry

/-- **Rung offsets**: a rung `(v, z)` has `z − v = −τ u_v + σ s u_v^⊥` with `σ = ±1`,
`s = √(1 − τ²)`.

TODO: prove.
What's missing: decompose the unit vector `z − v` in the orthonormal basis `(u_v, u_v^⊥)`.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `DirField.norm_u`. Difficulty M. -/
theorem rung_offset (F : DirField X) {v z : Pt} (h : IsRung F v z) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ z - v = (-tau X) • F.u v + (σ * sOff X) • perp (F.u v) := by
  sorry

/-- **Lemma 3.3 (no common normal)**: distinct `p, q ∈ S ∖ D` have `u_p ≠ u_q`.

TODO: prove ((q − p)·u_p > 0 and (p − q)·u_q > 0 by 3.2(b), normal case).
Acceptance: no `sorry`.
Depends on: `exact_identity_b`. Difficulty S–M. -/
theorem u_ne (F : DirField X) {p q : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X) (hq : q ∈ Sset X)
    (hqD : q ∉ Dset X) (hpq : p ≠ q) : F.u p ≠ F.u q := by
  sorry

/-- **T-edge / rung dichotomy** (§3): if `τ > 2β` every good edge is a T-edge or a rung.

TODO: prove.
What's missing: case analysis on 3.2(a)/(b); `|a + b| ≤ |u_p − u_q| ≤ ∠ ≤ β`; an exception
target is in `D`, which sees everything as normal; an exception with the other end in `(0, β)`
gives `|a + b| ≥ τ − β > β`.
Acceptance: no `sorry`.
Depends on: `exact_identity_a`, `exact_identity_b`, `exact_identity_c`. Difficulty M. -/
theorem good_dichotomy (hX : Normal X) (F : DirField X) (hτ : 2 * beta < tau X) {p q : Pt}
    (hp : p ∈ Sset X) (hq : q ∈ Sset X) (hpq : dist p q = 1)
    (hg : ang (F.u p) (F.u q) ≤ beta) :
    IsTEdge F p q ∨ IsRung F p q ∨ IsRung F q p := by
  sorry

/-- The far end of a good rung: `(v − z)·u_z ∈ [τ − β, τ + β]`.

TODO: prove (`|a + b| ≤ β` with `a = −τ`).
Acceptance: no `sorry`.
Depends on: `exact_identity_c`. Difficulty S. -/
theorem rung_far_end (F : DirField X) {v z : Pt} (h : IsRung F v z)
    (hg : ang (F.u v) (F.u z) ≤ beta) :
    tau X - beta ≤ inner ℝ (v - z) (F.u z) ∧ inner ℝ (v - z) (F.u z) ≤ tau X + beta := by
  sorry

/-- **(T1)** each `p` has at most one T-neighbour on each side of `ℝu_p`.

TODO: prove.
What's missing: two T-directions on one side have elevation in `(0, arcsin β)`, so are `< 60°`
apart, but two points at distance 1 from `p` and `≥ 1` from each other are `≥ 60°` apart.
Acceptance: no `sorry`.
Depends on: `DirField.norm_u`. Difficulty M. -/
theorem T1 (hX : Normal X) (F : DirField X) {σ : ℝ} {p q₁ q₂ : Pt} (hσ : σ = 1 ∨ σ = -1)
    (h₁ : IsSideT F σ p q₁) (h₂ : IsSideT F σ p q₂) : q₁ = q₂ := by
  sorry

/-- **(T2)** if `q` is the right T-neighbour of `p`, then `p` is the left T-neighbour of `q`.

TODO: prove (`∠(u_p, u_q) ≤ β` and `q − p` nearly perpendicular to both).
Acceptance: no `sorry`.
Depends on: `DirField.norm_u`. Difficulty M. -/
theorem T2 (hX : Normal X) (F : DirField X) {p q : Pt} (h : IsSideT F (-1) p q) :
    IsSideT F 1 q p := by
  sorry

/-- T-edges number at most `|S|` (each vertex has `≤ 2` T-edges by (T1)).

TODO: prove.
Acceptance: no `sorry`.
Depends on: `T1`, `two_mul_card_le_of_deg_le`. Difficulty M. -/
theorem card_tEdges_le (hX : Normal X) (F : DirField X) : (tEdges X F).card ≤ (Sset X).card := by
  sorry

/-- `edges = good ⊔ bad`.

TODO: fill (`filter_card_add_filter_neg_card_eq_card`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_good_add_bad (F : DirField X) : (good X F).card + (bad X F).card = eS X := by
  sorry

/-- For `τ > 2β`: `good ⊆ tEdges ∪ rungs`.

TODO: prove from the dichotomy.
Acceptance: no `sorry`.
Depends on: `good_dichotomy`. Difficulty S–M. -/
theorem good_subset_T_union_rungs (hX : Normal X) (F : DirField X) (hτ : 2 * beta < tau X) :
    good X F ⊆ tEdges X F ∪ rungs X F := by
  sorry

/-! ## Turning measure -/

/-- **Lemma 3.4 (multiplicity)**: if every boundary point lies in at most `M` of the sets
`γ_i ⊆ ∂K`, then `Σ turning(γ_i) ≤ 2πM`.

TODO: prove.
What's missing: for all but countably many directions `ν` the support point `y_ν` is unique;
`ν ∈ N(γ_i) ⟺ y_ν ∈ γ_i`; integrate the indicator sum over `ν ∈ [0, 2π)`.
Acceptance: no `sorry`.
Depends on: measure theory on `ℝ`, support functions of convex bodies. Difficulty L. -/
theorem turning_sum_le {K : Set Pt} (hK : Convex ℝ K) (hKc : IsCompact K) {ι : Type*}
    (A : Finset ι) (γ : ι → Set Pt) (hγ : ∀ i ∈ A, γ i ⊆ frontier K) (M : ℕ)
    (hM : ∀ x, (A.filter (fun i => x ∈ γ i)).card ≤ M) :
    ∑ i ∈ A, turning K (γ i) ≤ 2 * π * M := by
  sorry

/-- The turning of a connected boundary arc is at least the angle between (outward) normals at
its ends.

TODO: prove.
What's missing: normal-cone map is upper semicontinuous with arc values (nonempty interior),
so the union over a connected arc is a connected subset of `S¹` containing both normals.
Acceptance: no `sorry`.
Depends on: normal-cone topology. Difficulty L. -/
theorem turning_ge_angle {K : Set Pt} (hK : Convex ℝ K) (hKc : IsCompact K)
    (hint : (interior K).Nonempty) {γ : ℝ → Pt} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hsub : γ '' Set.Icc a b ⊆ frontier K) {ν₁ ν₂ : Pt}
    (h₁ : ν₁ ∈ normalCone K (γ a)) (h₂ : ν₂ ∈ normalCone K (γ b)) (hn₁ : ν₁ ≠ 0)
    (hn₂ : ν₂ ≠ 0) : ang ν₁ ν₂ ≤ turning K (γ '' Set.Icc a b) := by
  sorry

/-- **Arc spacing**: `1`-separated points on a `1`-Lipschitz arc of length `ℓ` number `≤ ℓ + 1`.

TODO: prove (pull back to parameters, which are pairwise `≥ 1` apart in `[a, b]`).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty M. -/
theorem card_le_arcLength {P : Finset Pt} (hP : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ dist x y)
    {γ : ℝ → Pt} (hγ : LipschitzWith 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hsub : ∀ x ∈ P, x ∈ γ '' Set.Icc a b) : (P.card : ℝ) ≤ b - a + 1 := by
  sorry

/-! ## §5.1 Lens lemma -/

/-- Half-angle of a lens: `cos φ₀ = d/(2R)`. -/
def phi0 (d R : ℝ) : ℝ := Real.arccos (d / (2 * R))

/-- Corner radius `ρ₀ = 1/sin(φ₀/2)`. -/
def rho0 (d R : ℝ) : ℝ := 1 / Real.sin (phi0 d R / 2)

/-- **Lemma 5.1 (lens lemma)**: `p` on the `C(c₁, R)`-arc, `q` on the `C(c₂, R)`-arc of the lens
`D(c₁,R) ∩ D(c₂,R)`, `|pq| ≤ 1`, and `R ≥ 2/(cos(φ₀/2) − cos φ₀)` ⇒ a common corner `c` within
circular arc length `ρ₀` of both.

TODO: prove.
What's missing: coordinates `c₁,₂ = (∓d/2, 0)`; (1) `|φ|, |ψ| > φ₀/2`; (2) MVT for `cos`,
`R(φ₀ − |φ|) ≤ ρ₀`; (3) same-sign argument using `R ≥ 1/sin²(φ₀/2)`.
Acceptance: no `sorry`.
Depends on: real trig. Difficulty L. -/
theorem lens_corner {c₁ c₂ p q : Pt} {R : ℝ} (hd0 : 0 < dist c₁ c₂) (hd : dist c₁ c₂ < 2 * R)
    (hR : 2 / (Real.cos (phi0 (dist c₁ c₂) R / 2) - Real.cos (phi0 (dist c₁ c₂) R)) ≤ R)
    (hp : dist p c₁ = R) (hp₂ : dist p c₂ ≤ R) (hq : dist q c₂ = R) (hq₁ : dist q c₁ ≤ R)
    (hpq : dist p q ≤ 1) :
    ∃ c : Pt, dist c c₁ = R ∧ dist c c₂ = R ∧
      R * ang (p - c₁) (c - c₁) ≤ rho0 (dist c₁ c₂) R ∧
      R * ang (q - c₂) (c - c₂) ≤ rho0 (dist c₁ c₂) R := by
  sorry

/-- **Lemma 5.2 (lens-corner arc length)**: for compact convex `K' ⊆` lens, `p, q ∈ ∂K'` as in
5.1 with `|pq| = 1`, the boundary arc of `K'` from `p` to `q` on the corner's side has length
`≤ 2ρ₀`.

TODO: prove.
What's missing: perimeter monotonicity for nested convex sets (not in Mathlib), applied to
`K' ∩ H ⊆ Λ ∩ H`; parametrisation of `∂K'` by arc length.
Acceptance: no `sorry`.
Depends on: `lens_corner`; convex perimeter monotonicity. Difficulty XL. -/
theorem lens_arc_length {c₁ c₂ p q : Pt} {R : ℝ} {K' : Set Pt} (hK' : Convex ℝ K')
    (hKc : IsCompact K') (hsub : K' ⊆ Metric.closedBall c₁ R ∩ Metric.closedBall c₂ R)
    (hd0 : 0 < dist c₁ c₂) (hd : dist c₁ c₂ < 2 * R)
    (hR : 2 / (Real.cos (phi0 (dist c₁ c₂) R / 2) - Real.cos (phi0 (dist c₁ c₂) R)) ≤ R)
    (hp : dist p c₁ = R) (hq : dist q c₂ = R) (hpK : p ∈ frontier K') (hqK : q ∈ frontier K')
    (hpq : dist p q = 1) :
    ∃ γ : ℝ → Pt, ∃ ℓ : ℝ, 0 ≤ ℓ ∧ ℓ ≤ 2 * rho0 (dist c₁ c₂) R ∧ LipschitzWith 1 γ ∧
      γ 0 = p ∧ γ ℓ = q ∧ γ '' Set.Icc 0 ℓ ⊆ frontier K' := by
  sorry

/-- **[C7]** KK lens constants: `2/(1 − 0.97) < 8.2²`.

TODO: fill (Phase 2 leaf).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c7_kk : (2 : ℝ) / (1 - 0.97) < 8.2 ^ 2 := by
  sorry

/-- **[C3]** `2/Δ₂ ≤ β/2` for `Δ₂ ≥ 10⁴`.

TODO: fill (Phase 2 leaf).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c3 {Δ₂ : ℝ} (h : 10 ^ 4 ≤ Δ₂) : 2 / Δ₂ ≤ beta / 2 := by
  sorry

/-! ## §5.2 Bad-edge counts -/

/-- Bad edges with both ends in `S ∖ D`. -/
def badKK (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun z => ∀ p ∈ z, p ∉ Dset X)

/-- Bad edges with both ends in `S ∩ D`. -/
def badDD (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun z => ∀ p ∈ z, p ∈ Dset X)

/-- Bad cross edges `zv` (`z ∈ D`, `v ∉ D`) with `|z w_v| = Δ` — case (c1). -/
def badC1 (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun e => ∃ v z, e = s(v, z) ∧ v ∉ Dset X ∧ z ∈ Dset X ∧
    dist z (F.partner v) = diam X)

/-- Bad cross edges with `|z w_v| ≠ Δ` (hence `≤ Δ₂`) — case (c2). -/
def badC2 (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (bad X F).filter (fun e => ∃ v z, e = s(v, z) ∧ v ∉ Dset X ∧ z ∈ Dset X ∧
    dist z (F.partner v) ≠ diam X)

/-- Every bad edge is KK, DD, (c1) or (c2).

TODO: prove (case split on the ends of `e ∈ Sym2`).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem bad_subset (F : DirField X) :
    bad X F ⊆ badKK X F ∪ badDD X F ∪ badC1 X F ∪ badC2 X F := by
  sorry

/-- **[C9]** numeric constants of §5: KK `12π(4·8.2+1)/β < 1.28·10⁵`, DD `12π·9/β < 3.4·10⁴`,
(c1) `24π/β < 7600`, (c2) `48π(2·600+1)/β < 1.82·10⁷`, and the total `< cBad`.

TODO: fill (Phase 2 leaf, `pi_lt_d4`).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c9 :
    12 * π * (4 * 8.2 + 1) / beta < 128000 ∧ 12 * π * 9 / beta < 34000 ∧
      24 * π / beta < 7600 ∧ 48 * π * (2 * 600 + 1) / beta < 18200000 ∧
      (128000 + 34000 + 7600 + 18200000 : ℝ) ≤ cBad := by
  sorry

/-- **KK bound** `#KK-bad < 1.28·10⁵`.

TODO: prove.
What's missing: `w_p = w_q` ⇒ good ([C3]); else lens `Λ(w_p, w_q) ⊇ K`, Lemmas 5.1/5.2 give an
arc `γ_pq ⊆ ∂K` of length `≤ 2ρ₀` with turning `> β` (`turning_ge_angle`); multiplicity
`M ≤ 6(4ρ₀ + 1)` (`card_le_arcLength`, kissing); Lemma 3.4.  Small-perimeter case separately.
Acceptance: no `sorry`.
Depends on: `lens_corner`, `lens_arc_length`, `turning_ge_angle`, `turning_sum_le`,
`card_le_arcLength`, `card_partners_minDist_le`, `c3`, `c7_kk`, `c9`. Difficulty XL. -/
theorem card_badKK_le (hX : Normal X) (F : DirField X) : ((badKK X F).card : ℝ) ≤ 128000 := by
  sorry

/-- **DD bound** `#DD-bad < 3.4·10⁴` (same argument on `∂P₁`, lens radius `Δ`, `ρ₀ ≤ 2`).

TODO: prove.
Acceptance: no `sorry`.
Depends on: as `card_badKK_le`, with `convexHull ℝ X` in place of `K`. Difficulty XL
(shares the machinery with KK: L once KK is done). -/
theorem card_badDD_le (hX : Normal X) (F : DirField X) : ((badDD X F).card : ℝ) ≤ 34000 := by
  sorry

/-- **(c1) bound** `< 24π/β < 7600`: the normal cone of `P₁` at `z` has angle `> β/2`; normal
cones are interior-disjoint.

TODO: prove.
Acceptance: no `sorry`.
Depends on: `turning_sum_le` (or a direct disjoint-cones count), `exact_identity_a`, `c3`, `c9`,
kissing. Difficulty L. -/
theorem card_badC1_le (hX : Normal X) (F : DirField X) : ((badC1 X F).card : ℝ) ≤ 7600 := by
  sorry

/-- **[C8]** `cos α ≥ −0.8821` on `ρ ∈ [1 − 10⁻⁴, 1]` (step 3 of (c2)).

TODO: fill (Phase 2 leaf).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c8_cos {ρ : ℝ} (h0 : 1 - 1 / 10 ^ 4 ≤ ρ) (h1 : ρ ≤ 1) :
    -0.8821 ≤ (1 + ρ ^ 2 - 1.94 ^ 2) / (2 * ρ) := by
  sorry

/-- **[C8]** the walk leaves the disc: `(Δ₂ − d₀)² + (2/5)(Δ₂ − d₀)·L·β > Δ₂²` at `L = 6/β`.

TODO: fill (Phase 2 leaf).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c8_walk {Δ₂ d₀ : ℝ} (h : 10 ^ 4 ≤ Δ₂) (h0 : 0 ≤ d₀) (h1 : d₀ ≤ 1) :
    Δ₂ ^ 2 < (Δ₂ - d₀) ^ 2 + 2 / 5 * (Δ₂ - d₀) * (6 / beta) * beta := by
  sorry

/-- **(c2) bound** `< 48π(2L + 1)/β < 1.82·10⁷` (`L = 600`).

TODO: prove.
What's missing: depth `d₀ ∈ [0, 1 − t]`; `α ∈ (β/2, 151.9°]` ([C8] `c8_cos`); walk along `∂K`
with forward tangents within `β/4` of `e₀` leaves `D(x_z, Δ₂)` by `σ = L` (`c8_walk`), so
`J_v` has turning `> β/4`; Lemma 3.4 with multiplicity `2L + 1`.
Acceptance: no `sorry`.
Depends on: `turning_sum_le`, `card_le_arcLength`, `c8_cos`, `c8_walk`, `c9`, kissing;
one-sided tangents of convex curves. Difficulty XL. -/
theorem card_badC2_le (hX : Normal X) (F : DirField X) : ((badC2 X F).card : ℝ) ≤ 18200000 := by
  sorry

/-- **Total bad edges** `≤ cBad`.

TODO: none (proved from the four counts).
Acceptance: no `sorry` (inherits).
Depends on: `bad_subset`, `card_badKK_le`, `card_badDD_le`, `card_badC1_le`, `card_badC2_le`,
`c9`. -/
theorem card_bad_le (hX : Normal X) (F : DirField X) : ((bad X F).card : ℝ) ≤ cBad := by
  have h := card_le_card (bad_subset F)
  have h1 := card_union_le (badKK X F ∪ badDD X F ∪ badC1 X F) (badC2 X F)
  have h2 := card_union_le (badKK X F ∪ badDD X F) (badC1 X F)
  have h3 := card_union_le (badKK X F) (badDD X F)
  have e1 := card_badKK_le hX F
  have e2 := card_badDD_le hX F
  have e3 := card_badC1_le hX F
  have e4 := card_badC2_le hX F
  have hc := c9.2.2.2.2
  have : ((bad X F).card : ℝ) ≤ (badKK X F).card + (badDD X F).card + (badC1 X F).card +
      (badC2 X F).card := by
    exact_mod_cast h.trans (h1.trans (by omega))
  linarith

end

end Erdos132Main

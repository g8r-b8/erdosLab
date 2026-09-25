# E report: the fan zone of Region III, quantified (angle R7, branch E)

Branch E of angle R7 (Erdős #132 / CDL Problem 1.6), 2026-09-25. Relaunch after an outage; written incrementally and committed per section.
Sources: angle_R7.md, angle_R7_reports/D1_report.md (D1r) with REF_D1_report.md, paper v3 (paper/paper.tex: §9 = Theorem N3,
Region III §5.3), scripts r6_n3_examples.py, r7_C_cone.py (Lemma AI), r7_A3_dp.py (Lemma DP).
New scripts: `scripts/r7_E_*.py` (all run under `tools/memcap.sh 4000 .venv/bin/python`).

Notation as in D1r: R = Δ₂, Δ = R + t, τ = t − (1 − t²)/(2R) (so Δ² = R² + 2Rτ + 1), θ₀ = arccos τ,
G := 2R sin(θ₀ − π/6) (C's parameter; G = 1 is A3's resonance strip), K = ∩_{x∈X} D(x, R), D = diametral endpoints,
S = points with a Δ₂-partner, 𝓡 = X∖S, r = |𝓡|. F* and F*₄ are as in D1r §6 (Corollary 6.1): good y ∈ 𝓡∖D with S∩D-neighbours
within a₀ of ±30° and a K-neighbour within a₀ of ±90°; F*₄ = the points of F*∖Exc owning 4 edges. Throughout, a₀ ≤ 10⁻².

## 1. The exact fan window

### 1.1 Statement

**Lemma EW (exact window; PROVED, exact).** Let w, y, k, z₂, z₃ ∈ X with

  |k − w| = R,  |z₂ − w| = |z₃ − w| = Δ,  |y − w| < R,  |y − k| = |y − z₂| = |y − z₃| = 1.

Then

  **τ ∈ [τ_lo(R), √3/2)**,  τ_lo(R) := cos(π/6 + arcsin(1/R)) = (√3·√(R² − 1) − 1)/(2R) = √3/2 − 1/(2R) − √3/(4R²) + O(R⁻³).

Equivalently **0 < G ≤ 2**, i.e. Δ² ∈ [R² + √3√(R² − 1), R² + √3R + 1). Moreover ρ := |y − w| ∈ [√(R² − 1), R), so
R − |y − w| ≤ R − √(R² − 1) < 1/(2√(R²−1)): the point y is within about 1/(2R) of the circle C(w, R).
Conversely, every τ in the window is realised by such a local 5-point configuration, and the lower end τ = τ_lo is exactly
R4's fan (the configuration of paper Remark "rem:sharp", `r6_n3_examples.py` (a)), in which |z₂z₃| = |z₃k| = 1.

In t (the quantity used by N3, B and D1r): t = √(R² + 2Rτ + 1) − R, so the window is
t ∈ [√3/2 − 3/(8R) + O(R⁻²), √3/2 + 1/(8R) + O(R⁻²)); at R = 10⁴, 10⁶, 10⁸ the exact endpoints are
√3/2 − 0.37501083/R, √3/2 − 0.37500011/R, √3/2 − 0.375/R and √3/2 + 0.12498918/R, √3/2 + 0.12499989/R, √3/2 + 0.125/R.

*Proof.* Put the origin at w and measure the angle ψ of a neighbour q = y + (sin ψ, cos ψ) of y from the outward radial
direction (y − w)/ρ. By the law of cosines |q − w|² = ρ² + 1 + 2ρ cos ψ, so

  cos ψ_z = (Δ² − ρ² − 1)/(2ρ),  cos ψ_k = (R² − ρ² − 1)/(2ρ).

C(y,1) ∩ C(w,Δ) consists of exactly the two points at ψ = ±ψ_z, so {z₂, z₃} are these two points, mirror images in the line wy.
Likewise k is at ψ = ±ψ_k; call z₃ the middle on k's side. Since Δ > R, cos ψ_z > cos ψ_k, so 0 ≤ ψ_z < ψ_k ≤ π.
- |z₂ − z₃| = 2 sin ψ_z ≥ 1 gives ψ_z ≥ 30°, i.e. **Δ² ≤ U(ρ) := ρ² + 1 + √3ρ**.
- |z₃ − k| = 2 sin((ψ_k − ψ_z)/2) ≥ 1 gives ψ_k − ψ_z ≥ 60°, i.e. **Δ² ≥ L(ρ) := ρ² + 1 + 2ρ cos(ψ_k − 60°)**.
- Together ψ_k ≥ 90°, i.e. cos ψ_k ≤ 0, i.e. **ρ ≥ ρ₀ := √(R² − 1)**; and ρ < R by hypothesis.

Write c := ρ cos ψ_k = (R² − ρ² − 1)/2 ∈ (−½, 0] on [ρ₀, R). Then L(ρ) = (ρ² + 1 + R²)/2 + √3·√(ρ² − c²) and
dL/dρ = ρ + √3ρ(1 + c)/√(ρ² − c²) > 0. So L is increasing and min L = L(ρ₀) = R² + √3ρ₀. U is increasing, so
Δ² ≤ U(ρ) < U(R) = R² + √3R + 1. With Δ² = R² + 2Rτ + 1 this is τ ∈ [(√3ρ₀ − 1)/(2R), √3/2). Finally
(√3ρ₀ − 1)/(2R) = (√3/2)cos γ − (1/2)sin γ = cos(π/6 + γ) with sin γ = 1/R, so θ₀ ≤ π/6 + γ and G = 2R sin(θ₀ − π/6) ≤ 2R sin γ = 2;
τ < √3/2 is θ₀ > π/6, i.e. G > 0. Realisability: for τ in the window the feasible ρ form the non-empty interval
[max(ρ₀, U⁻¹(Δ²)), min(R, L⁻¹(Δ²))], because L(ρ₀) = U(ρ₀) and both are increasing. ∎

*Checks* (`r7_E_window.py`, all pass): the identity for L, the derivative and L(ρ₀) = R² + √3ρ₀ in sympy; the windows,
G(τ_lo) = 2 and τ_lo = cos(π/6 + arcsin(1/R)) to 50 digits at R = 10⁴, 10⁶, 10⁸; R4's fan has τ = τ_lo(10⁴) to 40 digits
(t = 0.86598790270…, τ = 0.86597539945…); 200 random τ in the window give explicit 5-point configurations meeting every constraint
with all pairwise distances ≥ 1 (60 digits).

### 1.2 Why every fan satisfies the hypotheses of Lemma EW

Let y ∈ F* (any a₀ ≤ 10⁻², any ε₀ ≤ a₀ with D1r's goodness). By Lemma S(2), y has S∩D-neighbours z₂, z₃ within a₀ of ∓30° and
a K-neighbour k within a₀ of +90° or −90°. Let w be **any** Δ₂-partner of k (k ∈ S∖D ⊂ ∂K, so it has one). Lemma S(d), applied
to each middle separately (it only uses c(m) ≥ cos(30° + a₀), |Δx| ≤ 2 and (S1)), shows that z₂ and z₃ are non-normal for k,
so |z₂ − w| = |z₃ − w| = Δ by paper Lemma 2.2(b). (This is REF_D1's remark R1: both middles are exceptions for the same k and w.)
Also y ∈ 𝓡∖D ⊂ int K ⊂ int D(w, R), so |y − w| < R. All hypotheses of Lemma EW hold.

The same argument covers HF1 (the second D-neighbour is in 𝓡∩D, but Lemma 2.2(b) applies to every z ∈ X) and every fan type of
paper Lemma 9.7 (F6, F5, HF1, HF2), at every ε₀ ≤ 1/50, because Lemma S(d) and paper Lemma "pin" use the same two facts.

**Corollary EW.** For every a₀ ≤ 10⁻² (in particular at D1's ε₀ = 10⁻⁶ and at N3's ε₀ = 1/50), and every X:

  F*(a₀) ≠ ∅  ⇒  τ ∈ [τ_lo(Δ₂), √3/2)  ⇔  0 < G ≤ 2.

The window does not depend on ε₀, θ or a₀; only which points are "good" does (the non-good points number O(1/ε₀) and are in Exc).

### 1.3 Reconciliation with the earlier windows

| source | parameters | window where fans may exist | status | relation to Lemma EW |
|---|---|---|---|---|
| N3, paper Lemma "pin" | ε₀ = 1/50, Δ₂ ≥ 10⁴ | t ∈ [0.751, 0.950] (stated [0.75, 0.95]) | refereed | a relaxation: |t − Δc| < 0.0404 with Δc ∈ [0.7914, 0.9096] only uses the angle tolerances |
| B / REF_B (B1's P1.2) | ε₀ = 10⁻⁶, δ₀ = 10⁻⁴ (flat model) | \|t − √3/2\| ≤ 5ε₀ + δ₀ < 2·10⁻⁴ | refereed | a relaxation (flat model tolerance δ₀) |
| D1r Lemma S, Lemma 4.0 | θ = 10⁻³, ε₀ = 10⁻⁶ | \|t − √3/2\| ≤ κ(θ) < 1.5525·10⁻³; κ(θ) ≤ 1.51max(θ,ε₀) + 3.01ε₀ + 2/Δ₂ | refereed once | a relaxation (one middle, frame tolerance θ) |
| REF_D1 R1 | both middles, any θ | \|t − √3/2\| ≤ κ′(ε₀, Δ₂) ≤ 7ε₀ + 5/Δ₂ (< 4.57·10⁻⁴ at 10⁻⁶, 10⁴) | refereed once (sampled bound) | a relaxation (normals only within ε₀) |
| **Lemma EW (this report)** | none | **τ ∈ [cos(π/6 + arcsin(1/Δ₂)), √3/2)**, i.e. t ∈ [√3/2 − 0.3751/Δ₂, √3/2 + 0.1251/Δ₂) | proved, exact | exact: uses that k, z₂, z₃ are on circles about the **same** w |

The earlier windows all bound t through |t − Δc| with the heights c measured in y's frame, whose normal is known only up to ε₀;
that is where ε₀ and θ enter. Lemma EW instead works in the frame of the common centre w, where every position is determined
exactly by ρ = |y − w|; the only inequalities used are the three minimum-distance conditions and |y − w| < Δ₂.

**The limit ε₀ → 0.** Yes: t = √3/2 + O(1/R), and more precisely the fan zone is the τ-interval of length 1/(2R) + O(R⁻²) just
below √3/2, uniformly in ε₀. So there are no "O_{ε₀}(1) exceptional t": for each Δ₂ the set of admissible t is one explicit interval.
What depends on ε₀ is only the number of non-good points, O(1/ε₀), which D1r puts in Exc.

**Relation between t, τ and the resonance window.**
- τ ≤ t (as t ≤ 1), and t − τ = (1 − t²)/(2R) = 1/(8R) + O(R⁻²) on the window.
- In C's parameter: fans need 0 < G ≤ 2. A3's resonance strip (τ = cos(π/6 + α₂/2), exactly G = 1) is the midpoint of the fan
  window; Theorem W's sharp curve G = 1 lies inside it. In A3's d = 2 sin θ₀ − 1: 0 < Rd ≤ √3·(1 + O(R⁻²)) (1.73200 at R = 10⁴),
  so the whole fan zone lies in Theorem W's window R|d| ≤ 4, where only θ = 2/3 is available (at G = 1) and θ = ½ elsewhere.
- The upper end G → 0 (τ → √3/2) is where the two middles become exactly 1 apart with y on C(w, R); the lower end G = 2 is R4's
  fan, where additionally the K-neighbour is exactly 1 from the near middle.

### 1.4 Consequence: Theorem G becomes uniform outside an O(1/Δ₂) window (PROVED, given D1r + REF_D1)

D1r's Theorem G has a constant C(η, κ) that blows up as κ → 0. Corollary 6.1(1) (for all t) reads Σ_𝓡 v ≤ 6r + 2|F*₄| + ηr + C(η, a₀),
and its constant depends on η and the fixed a₀ only (Δ₂* = max{10⁴, 100ℓ}, no 5/κ term). Fix a₀ := 10⁻². By Corollary EW,
F*₄ = ∅ unless 0 < G ≤ 2. Hence:

**Theorem G′.** For every η > 0 there is C(η) such that every X in the nondegenerate regime with G ∉ (0, 2] (i.e.
τ ∉ [cos(π/6 + arcsin(1/Δ₂)), √3/2)) satisfies Σ_𝓡 v ≤ (6 + η)r + C(η). With the e(S) inputs of D1r §9 (Theorem W in Region III),
**min{μ(Δ₂), μ(δ)} ≤ (9/7 + η)n + C(η) for all such X**, with no dependence on how close t is to √3/2.

So the fan zone is no longer "|t − √3/2| < κ for a small fixed κ", but the explicit window 0 < G ≤ 2, whose width in t is
1/(2Δ₂) + O(Δ₂⁻²). Everything below concerns X with 0 < G ≤ 2.

*Referee flag 1.1.* The derivation of Theorem G′ uses only statements of D1r/REF_D1 as refereed plus Lemma EW; the one point to check
is that Corollary 6.1's constant C(η, a₀) indeed has no κ (D1r §6 says "The condition Δ₂ ≥ 5/κ is dropped from Δ₂*"; REF_D1 §5 confirms).

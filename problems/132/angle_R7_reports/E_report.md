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

## 2. Cost per fan, and the exact structure of a fan

### 2.1 The cost table: confirmed

Cost := contribution to Σ_𝓡 v − 6r, i.e. 2(own(y) − 3) at a non-exceptional point (D1r §6, REF_D1 §5). I re-derived every row
against rules O1–O3 and paper Lemma 9.7 (at tolerance a₀):

| type (deg, m) | v | owned by y | own | cost | remark (new, from §2.2) |
|---|---|---|---|---|---|
| F6 (6,4) | 10 | 4 S-neighbours (the ±150° interior neighbours have cos(ψ − α) < 0 and own their edges) | 4 | **2** | both K-extremes share one centre w and are in Q |
| F5 (5,4) | 9 | 4 S-neighbours | 4 | **2** | as F6 |
| bare fan (4,4) | 8 | 4 S-neighbours | 4 | **2** | as F6 |
| HF2 (6,3), (5,3), (4,3) | 9, 8, 7 | 3 S-neighbours, plus the 𝓡∖D neighbour u near ∓90° iff u − y is n-upward | 3 or 4 | **0 or 2** | its one K-extreme is in Q |
| HF1 (6,3) | 9 | 3 S-neighbours; the 𝓡∩D middle's edge belongs to the D-end (O2) | 3 | **0** | pinned by Lemma EW as well |
| cap (6,3) | 9 | 3 S-neighbours | 3 | **0** | t = ½ + O(ε₀): never in the fan window, so caps and fans never coexist |

**Verdict: the table is correct** (as REF_D1 found); no inequality depends on the type names, only on own(y) ≤ 3 + 1[y ∈ F*₄]
(Lemma S(2)). The HF2 dichotomy cannot be removed locally: in the w-frame of an exact regular HF2 hexagon, u is at angle
ψ_k − 180° with ψ_k ∈ [90°, 90° + arcsin(1/(2R))], so (u − y)·e_rad = −cos ψ_k ∈ [0, 1/(2ρ)]; whether u is upward in the
sector frame n (within θ of n₀(y), which is within O(1/R)… O(ε₀) of e_rad) is decided at scale θ, not by the configuration. So
"0 or 2" is the honest local cost; §3 does not need to resolve it.

### 2.2 New exact facts about a fan (PROVED)

Work in the frame of Lemma EW: w = 0, y = (0, ρ) with ρ ∈ [√(R²−1), R), a neighbour at angle ψ (from the outward radial
direction) is y + (sin ψ, cos ψ); z₂, z₃ at ∓ψ_z on C(w, Δ), the K-extreme k at +ψ_k on C(w, R), 30° ≤ ψ_z ≤ ψ_k − 60°, 90° ≤ ψ_k.
For y ∈ F*, w is any Δ₂-partner of its K-extreme k (§1.2).

**Lemma U (unique partner).** Every Δ₂-partner of k is w. Hence **k ∈ Q** (Δ₂-degree 1). If y has two K-extremes (F6, F5,
bare fan), both have the same unique partner w, and the fan is mirror-symmetric about the line wy.

*Proof.* By §1.2 every Δ₂-partner w″ of k is diametral to both z₂ and z₃ (Lemma S(d) holds for every inward normal (w″ − k)/R at
k, since G5 bounds all normals along γ^Λ_y). C(z₂, Δ) ∩ C(z₃, Δ) = {w, w*} with w* the reflection of w in the line z₂z₃, and
|ww*|² = 4Δ² − |z₂z₃|² ≥ 3Δ² > Δ² (|z₂z₃| ≤ 2 sin(ψ_k − 60°) < Δ). As |ww″| ≤ Δ, w″ = w. For two K-extremes k₊, k₋ the same
argument gives w₊ = w₋. Symmetry: C(y,1) ∩ C(w, R) is a pair of mirror points in the line wy. ∎ (`r7_E_structure.py` (B).)

**Lemma X1 (pendant middle).** The middle z₃ on k's side has w as its **only** diametral partner.

*Proof.* Let w′ ∈ X, w′ ≠ w, |w′ − z₃| = Δ; write w′ = z₃ − Δ(sin β, cos β), and let β₀ be the value for w (sin β₀ = sin ψ_z/Δ).
- |w − w′| ≤ Δ, so |β − β₀| ≤ 60°.
- |z₂ − w′|² = |z₂z₃|² + Δ² − 2Δ|z₂z₃| sin β ≤ Δ² forces sin β ≥ |z₂z₃|/(2Δ) = sin β₀, so β > β₀ (this is Hopf–Pannwitz:
  [z₂, w] and [z₃, w′] must cross).
- |k − w′|² − |k − w|² = 2Δ(k − z₃)·((sin β, cos β) − (sin β₀, cos β₀)) = 4Δ sin((ψ_k − ψ_z)/2)·[sin(β − m) − sin(β₀ − m)],
  m := (ψ_k + ψ_z)/2 ∈ [60°, 60° + O(1/R)]. On β ∈ (β₀, β₀ + 60°], β − m ∈ (−61°, 0°] ⊂ (−90°, 90°), where sin is increasing,
  so the difference is > 0: |k − w′| > R.
- k ∉ D, so |k − w′| ≤ R. Contradiction. ∎

`r7_E_structure.py` (A): 179 996 admissible w′ ≠ w (a 1200-step grid in β, 300 random window fans, R = 10⁴…10⁸, 60 digits) all
give |k − w′| > R. X1 is not needed for §3's bound but it is the obstruction that shapes §4.

**Lemma C2 (at most two fans per centre, and per K-extreme).**
(a) A point k ∈ S∖D is the K-extreme of at most two points of F*. (b) A point w is the centre of at most two points of F*.

*Proof.* (a) Seen from k, a fan y with K-extreme k lies within a₀ + ε₀ of the tangent direction ±u_k^⊥ (its ±90°, measured in y's
frame, whose normal is within ε₀ of k's normals by G5). Two such fans on the same side would be < 60° apart as seen from k, so < 1
apart; hence at most one per side.
(b) The middles of a fan with centre w are two S-points of X ∩ C(w, Δ) at distance 2 sin ψ_z ∈ [1, 1 + O(1/R)], hence
consecutive in the angular order z_1, …, z_N (a point strictly between would be < 1 from one of them). By Lemma AI only
z_1, z_2, z_{N−1}, z_N can be in S, so the possible middle pairs are (z_1,z_2), (z_{N−1},z_N), and (z_2,z_3) only when N ≤ 4.
If two fans with centre w share a middle (pairs (z_1,z_2), (z_2,z_3)), then the K-slot of one on the shared side lies within
0.97/R (< 2/R, checked over the window in `r7_E_structure.py` (C)) of the other fan point, which is in 𝓡; so their K-extremes
are on the outer sides. Three fans (1,2), (2,3), (3,4) (N = 4) would leave the middle one with both ±90° slots occupied by
𝓡-points: impossible. So at most two fans per centre. ∎

(Consequently |F*| ≤ 2·#centres and |F*| ≤ 2|Q_K| ≤ 2|Q|, where Q_K is the set of K-extremes of fans. §3 uses the second.)

### 2.3 What the exact structure says about the D-side

- Each fan has a K-side middle that is a **pendant** of the diameter graph (Lemma X1), attached to the centre w, which has
  diametral degree ≥ 2 (z₂, z₃). The centre w is itself in S∩D (partner of k).
- In a Reuleaux-type chain of D-points in which every D-point has two diametral partners (odd cycle, as for regular Reuleaux
  polygons), no fan can occur: X1 needs a pendant. This is why R4's single-centre chain and the Reuleaux skeleton both fail to
  give many fans in S (§4).

## 3. Upper bound in the fan window

### 3.1 What can and cannot be bounded

The task asked for φ = |F*₄|/r ≤ φ₀ < 1, or φ = o(1). **I cannot prove any bound φ ≤ φ₀ < 1**: a bare fan (4,4) has no 𝓡-neighbour
at all, so nothing local attaches a second 𝓡-point to it, and §4 shows that the obstruction to many fans is global (it concerns the
Δ₂-partners of D-points, not 𝓡). What the structure of §2 does give is a bound of the fans by **Δ₂-degree-1 points**, and that is
enough to beat 4/3, because Q-points lower μ(Δ₂) while fans raise μ(δ).

**Proposition F (PROVED, from Lemmas U and C2(a)).** For every X and a₀ ≤ 10⁻²: |F*₄| ≤ |F*| ≤ 2|Q_K| ≤ 2|Q| = 2p, where Q_K is the
set of K-extremes of points of F*. Together with |F*₄| ≤ r.

(Each y ∈ F* chooses a K-extreme k(y); k(y) ∈ Q by Lemma U; each k is chosen by ≤ 2 points by Lemma C2(a).)

Other bounds that hold but are weaker for the LP: |F*| ≤ 2·#centres (C2(b)); 2|F*| ≤ 3|S∩D| (D1r Cor. 6.1(3)); |F*| ≤ number of
pendant vertices of the diameter graph that lie in S (X1: y ↦ its K-side middle is injective, since a second fan using z as K-side
middle would sit in the first fan's K-slot).

### 3.2 The LP with the Q-information

Inputs (additive constants suppressed; all per unit n = s + r):
- μ(Δ₂) ≤ (3/2)s − ½p (paper Lemma VSQ, p = |Q|);
- μ(δ) = e(S) + ½Σ_𝓡 v ≤ e(S) + 3r + |F*₄| + ηr/2 + C(η) (D1r Corollary 6.1, a₀ = 10⁻² fixed);
- e(S) ≤ s + θ|Q′| + C with Q′ ⊆ Q (Theorem W; θ = 2/3 on all of Region III, θ = ½ off the curve G = 1 by REF_C's shadow remark);
- |F*₄| ≤ r and |F*₄| ≤ 2p (Proposition F).

The adversary maximises min{μ(Δ₂), μ(δ)}. Exact values with primal optimum and dual certificate (`r7_E_lp.py`, Fractions):

| θ | value | optimum (s, r, p = \|Q′\|, \|F*₄\|) | weights (λ on μ(Δ₂), 1 − λ) and multipliers (Q′ ≤ Q, F ≤ r, F ≤ 2p) |
|---|---|---|---|
| 2/3 (Theorem W, every G, incl. G = 1) | **81/61 = 1.327869…** | (55, 6, 3, 6)/61 | (40/61, 21/61); (14/61, 18/61, 3/61) |
| ½ (G ≠ 1, REF_C) | **53/40 = 1.325** | (36, 4, 2, 4)/40 | (13/20, 7/20); (7/40, 11/40, 3/40) |

The certificate for θ = 2/3, written out: (40/61)·μ(Δ₂) + (21/61)·μ(δ) ≤ (40/61)(3s/2 − p/2) + (21/61)(s + (2/3)p + 3r + F)
+ (14/61)(p − |Q′|)·0 … i.e. adding (14/61)(p − |Q′|) ≥ 0, (18/61)(r − F) ≥ 0 and (3/61)(2p − F) ≥ 0 gives every coefficient
≤ 81/61 on s and r and ≤ 0 on p, |Q′|, F. So

**Theorem E (fan window; PROVED given the inputs' statuses).** For every η > 0 there is C(η) such that every X in the
nondegenerate regime with 0 < G ≤ 2 satisfies
  min{μ(Δ₂), μ(δ)} ≤ (81/61 + η)·n + C(η),
and ≤ (53/40 + η)·n + C(η) if moreover G ≠ 1 (using REF_C's θ = ½).

As a function of the fan density (worst case |F*₄| = 2p, θ = 2/3) the value is (9 + 4.5φ)/(7 + 19φ/6) (φ = |F*₄|/r): 9/7 at φ = 0,
1.3107 at φ = ½, 81/61 at φ = 1, against D1r's 3(3 + φ)/(7 + 2φ) (13/10 → 21/16 → 4/3). The improvement comes entirely from the
Q-term: every fan forces at least ½ a Δ₂-degree-1 point.

### 3.3 The overall bound

Combining Theorem G′ (§1.4: 9/7 + η outside the window) with Theorem E (inside):

  **min{μ(Δ₂), μ(δ)} ≤ (81/61 + η)·n + C(η) for every finite X ⊂ ℝ² (all regimes), 81/61 = 1.32787 < 4/3 = 1.33333.**

(Degenerate regime n + 1; Δ₂ < Δ₂*: bounded n; Regions I, II, τ > 1 and Region III off the window: Theorem G′ with D1r §9's
e(S) inputs; the window: Theorem E.) With REF_C's θ = ½ the only X that can exceed 53/40 lie on the curve G = 1.

Status of the inputs (a referee must check each):
- D1r Theorem G / Corollary 6.1: refereed once (REF_D1: correct, cosmetic fixes); a second referee is queued.
- Theorem W (e(S) ≤ s + (2/3)|Q′| + C in Region III, Q′ ⊆ Q): refereed once (REF_C). θ = ½ off G = 1: REF_C's own remark, one pass.
- Lemma VSQ: paper, refereed.
- Lemmas EW, U, X1, C2 and Proposition F: new (this report), unrefereed; exact proofs above, numerical checks in
  `r7_E_window.py`, `r7_E_structure.py`.

**What stays open.** φ ≤ φ₀ < 1 is not proved, and neither is φ = o(1) (which would give 9/7 everywhere by Corollary 6.1). The
LP optimum of Theorem E needs |F*₄| = r = 2p, i.e. every 𝓡-point a fan and one Q-point per two fans; §4 examines whether fans can
be linear at all.

*Referee flags for §3.*
- 3.1: the argument needs Q′ ⊆ Q in Theorem W (Q′ = rung K-ends of Δ₂-degree 1; cf. the `r7_C_q.py` docstring "v+ in Q′").
  Theorem W's own LP needs the same inclusion, since it pairs e(S) ≤ s + θ|Q′| with μ(Δ₂) ≤ 1.5s − ½|Q′| (VSQ on Q′).
- 3.2: Lemma C2(a) uses that the frames of two good points within distance 2 differ by ≤ 2ε₀ (G5 through the common point k).
- 3.3: the additive constant is C(η) = C_Cor6.1(η, 10⁻²) + (constants of Theorem W and VSQ); it does not depend on the window.

## 4. Lower bound: can fans be linear?

**Verdict: I found no configuration with more than O(1) points of F*, and two natural families are killed by exact
obstructions. Whether |F*| = Θ(n) is possible stays OPEN; §3's bound 81/61 does not depend on it.**

What a point of F* needs (all proved in §1–§2): a centre w (a D-point in S with ≥ 2 diametral partners), two consecutive S-points
z₂, z₃ of X ∩ C(w, Δ) at distance 2 sin ψ_z ∈ [1, 1 + O(1/R)], a K-extreme k ∈ C(w, R) ∩ Q, the fan point y ∈ int K within
1/(2R) of C(w, R), τ in the window 0 < G ≤ 2, and — the hard part — **Δ₂-partners for both middles**, one of which (z₃, on k's side)
is a pendant of the diameter graph (Lemma X1).

### 4.1 R4's fan chain (paper Remark rem:sharp, `r6_n3_examples.py` (a))

All middles lie on one circle C(w, Δ) (one centre). By Lemma AI at most 4 of them are in S, and by Lemma C2(b) at most 2 of the chain's
fans can be in F*. The chain sits exactly at the lower end τ = τ_lo of the window (§1). **Obstruction: one centre carries ≤ 2 fans;
linear fans need linearly many centres.**

### 4.2 Reuleaux skeleton with pendants (`r7_E_reuleaux.py`, 50 digits)

The natural way to get many centres is a Reuleaux polygon: vertices v_j (N = 2m + 1), v_j diametral to v_{j+m}, v_{j+m+1}. Every
vertex has two diametral partners, so it can be a centre. X1 demands a pendant middle, so put on each arc of C(v_j, Δ) a pendant a_j at
the fan chord 2 sin ψ_z from v_{j+m}, the fan point y_j and its K-extreme k_j ∈ C(v_j, R) (Lemma EW geometry, ρ in the middle of the
feasible interval). (A second fan at the other end of the arc would be 0.973 from the neighbouring arc's fan at the shared vertex.)

Checked exactly for N = 101, 301, 1001 at G = 1 and N = 301 at G = 0.3, 1.9 (R = 10⁴): the skeleton is valid (min distance ≥ 1,
diameter Δ, each y in int K, each k on ∂K with unique partner v_j, v_j has exactly 3 diametral partners v_{j+m}, v_{j+m+1}, a_j). All
vertices are in S (partner k). But **no pendant a_j can have a Δ₂-partner**: the set of p ∈ C(a_j, R) with |p − x| ≤ R for all x
in the skeleton is empty (exact arc intersection), and no point of C(a_j, R) ∩ C(x, Δ) (x in the skeleton) is compatible with the
other distances. So the pendants are in 𝓡∩D, every "fan" is of HF1 type (cost 0), and F* = ∅.

*Why (the precise obstruction).* a_j lies strictly inside the arc of X ∩ C(v_j, Δ) (between v_{j+m} and v_{j+m+1}). By the cone lemma
(branch C) a Δ₂-partner p of such a point must be diametral to a neighbour on the arc. For a neighbour at distance s from a_j,
|p − z_±| = Δ and |p − a_j| = R give cos∠(p − a_j, a_j − z_±) = (2Rt + t² − s²)/(2Rs) ≈ t/s, so p sits at angle ≈ arcsin(t/s)
from the centre as seen from a_j: about 60° for s = 1. Then p is ≈ R away from v_j, far outside the arc of v_{j+m}'s partners
(which spans π/N), and violates the diameter bound.

### 4.3 General structure (partly proved)

**Lemma ORD (ordering of partners; proved from Hopf–Pannwitz).** If c, c′ are diametral partners of w that each have another
diametral partner, then every diametral partner of w lies on the closed arc of C(w, Δ) between c and c′.

*Proof.* Any two diametral segments of X intersect. Orient the near side (around w's partners) left to right. If [a, b] and [a′, b′]
are diametral with a ≠ a′, b ≠ b′ and a′ right of a, crossing forces b′ left of b on the far side (this is the computation in X1:
sin β ≥ sin β₀). Let z be a partner of w left of c, and w_c ≠ w another partner of c. [c, w_c] must cross [w, z] (z left of c ⇒ w_c
left of w) and [w, c′] (c left of c′ ⇒ w_c right of w). Contradiction. ∎ (Referee flag 4.1: the "left/right" orientation is
exactly X1's inequality; it should be written out once in this generality.)

**Consequence: two cases for a fan with centre w and pendant middle z₃.**
- (i) z₃ is interior to X ∩ C(w, Δ). Then, by the cone lemma, a Δ₂-partner p of z₃ is diametral to its arc-neighbour z_± (z₂, or
  the next point z₄), which must be non-pendant; p sits at angle ≈ arcsin(t/s) about z₃ from w, s = |z₃z_±|. For z_± = z₂ (s ≈ 1)
  this is ≈ 60°: z₂ is then the vertex of a "Reuleaux triangle"-sized diametral arc (its partners w and p are ≈ R apart).
  **Conjecture (not proved):** the angular spans of the partner arcs of different D-points have disjoint interiors in the circle of
  directions (so they sum to ≤ π). Granting it, only O(1) points z₂ can have a 60° span, so this sub-case gives O(1) fans; the
  sub-case z_± = z₄ gives Σ 1/s ≤ π/t together with Σ s ≤ πΔ, hence O(√Δ) fans (Cauchy–Schwarz).
- (ii) z₃ is an end of X ∩ C(w, Δ). By Lemma ORD, w has at most one non-pendant partner, so w's partners are a pendant fan with at
  most one "attached" point. Then z₃'s partner p lies on z₂'s side of the bisector of z₂z₃ (|p − z₂| ≤ R), or is diametral to z₂.
  I could not rule this case out, nor build it globally: each centre w is a sharp spike (X∖{w} ⊂ D(z₃, R), so the hull near w
  falls t below C(z₃, Δ) within distance 1 of w), and each pendant needs its own far partner p ∈ ∂K ∩ C(z₃, R).

### 4.4 The value of the best construction

The only exact configurations with points of F* that I know are the local ones (§1.1 (7), R4's fan with its middles declared in S),
which are not sets with those middles actually in S. **No construction with |F*₄| ≥ 3 is known**; every known global construction
has F* = ∅ and so min{μ(Δ₂), μ(δ)} ≤ (9/7 + η)n + C by Corollary 6.1. The best lower bound for the fan window is therefore not
better than the global 9/7 (ienjoymath, which lies in Region I, t → 0, not in the window). In particular I cannot exhibit
min{μ(Δ₂), μ(δ)}/n > 9/7 anywhere, and the gap between 9/7 and 81/61 in the fan window is open.

*What would close it.* Either (a) prove the case-(ii) obstruction and the arc-span conjecture, which would give |F*| = O(√Δ) + O(1)
and hence φ = o(1) whenever r ≫ √Δ (and then 9/7 in the window, except for sets with r = O(√Δ), which would need separate
treatment); or (b) a global construction of case (ii) with Θ(n) fans, which would show that Corollary 6.1's accounting cannot give 9/7
and that the LP of §3 must be sharpened by a genuinely new inequality.

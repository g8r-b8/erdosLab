# REF_core — hostile referee of `CoreE` and of the visible-path proof (RouteA_visiblepath_report.md)

Referee agent, 2026-09-25. Scripts: `problems/132/scripts/l97R_*.py`. Status: complete.

## 0. Verdicts

- **Task 1 (`CoreE`): TRUE as stated**, given §5.2 (and independently given the visible-path proof). The Lean
  encodings (`Yout`, `Yset`, `Aset`, `defc`, `Normal`) match the paper exactly. One documentation error: the
  docstring's chain "per K > 100h ⇒ r_in ≥ per K/(300π) > h" is false as written (it gives h/(3π)); the correct
  chain is per K ≥ |A| > 1000h > 300πh.
- **Task 2 (visible-path proof): CORRECT WITH GAPS.** Four minor gaps, all fixable in a few lines: G1 a vertex
  can be a corner twice (the "dip"; the report says "at most once", and the author's harness asserts it) — fix
  by counting corner occurrences; G2 missing justification that ν(a)·n_a > 0 at A-points in collapse zones
  (true since D(c, h) ⊆ K; |α_a| ≤ ψ_c alone does not give it, ψ_c can be ≈ 2.69); G3 (N4) monotonicity is
  asserted without proof (easy injectivity proof supplied); G4 a compactness sentence in V3.1. No
  counterexample (304 new exact-construction and sharp-corner stress configurations). The conclusion
  Def(G[Yout]) ≥ 2|A| − (71h + 7) implies `CoreE` with the current `Eh`. The proof is formalisable without
  plane topology: no Jordan-, face- or winding-type fact is used, secretly or openly.

## 1. Task 1 — the reduction behind `CoreE`

Sources read: angle_R6.md §5 (lines 200–466), MAIN97_PLAN.md, E132Main97Defs.lean (`defc`, `Yset`, `Aset`,
`Yout`, `Eh`, `CoreE`), E132MainDefs.lean (`Normal`, `Sset`, `Dset`, `dist2`, `diam`, `minDist`, `KBall`).

### 1(a) |A| > 1000h ⇒ per K > 100h and r_in(K) > h — CORRECT, but the chain as written is too weak

- |A| > 1000h ≥ 1500 ≥ 2. (P7): the |A| gap arcs of ∂K between cyclically consecutive A-points each have
  length ≥ chord ≥ 1, so in fact **per K ≥ |A| > 1000h** (the paper's |A| ≤ per K + 1 is weaker than needed).
- int K ≠ ∅: two A-points a ≠ b lie in K with |a − b| ≤ Δ₂ < 2Δ₂ (neither is in D), and every disc
  D(w, Δ₂) containing a, b contains the lens of radius Δ₂ on the chord ab, which has interior. So Lemma F applies.
- Lemma F (re-checked, steps 1–9): diam K ≤ 100·w(K); Steinhagen w ≤ 3r_in; Cauchy per K ≤ π diam K. Hence
  r_in ≥ diam K/300 ≥ per K/(300π).
- **Wording error (docstring of `CoreE` and MAIN97_PLAN):** "per K > 100h … ⇒ per K/(300π) > h" is false as a
  chain: per K > 100h gives only r_in > h/(3π) ≈ 0.106h. What is true: per K ≥ |A| > 1000h > 300πh
  (300π < 942.5), so r_in > h. Replace "per K ≥ |A| − 1 > 100h" by "per K ≥ |A| > 1000h > 300πh" in the
  docstring. The mathematics is fine; the stated intermediate bound is not the one that does the work.
- Both fallbacks are excluded: (F2) needs r_in ≤ h, (F3) needs per K < 100h.

### 1(b) Given (a) and h < Δ₂/200, §5.2 Steps 2–7 prove Def(G[Yout ρ]) ≥ 2|A| − E(h) — CORRECT (as refereed)

Steps 2–7 use exactly: δ = 1 on all of X (P1, A-spacing ≥ 1, deg ≤ 6), Δ ≤ 1.94Δ₂ (Step 3 ψ_c bound, Lemma F),
h < Δ₂/200 (Step 3, Step 6 window), h ≥ 3/2 (Step 3 "per K′ > 2"), r_in > h (int K′ ≠ ∅), per K ≥ 100h (Step 3).
None uses ρ ∈ ℕ beyond h = ρ + ½, and none uses t or τ. I re-derived the arithmetic:
- case (i): Σ_{outer}(3 + |w_j|) ≥ |A|, |F₀| ≥ per K′ ≥ per K − 2πh − 21h ≥ |A| − 1 − (21 + 2π)h, total
  2|A| − (21 + 2π)h − 4 (the "−3" of Euler, the "−1" of P7);
- case (ii): 2|A| − 2[2πh + 1/200 + 21h(42h + 5)] = 2|A| − 1764h² − (210 + 4π)h − 1/100;
- tan θ*/θ* ≤ 3.26 with θ* = arcsin(194/199) > 1.343: tan θ* = 194/√1965 = 4.3764 ≤ 3.26·1.343 = 4.3782 (tight
  but true); Σ len Z_c ≤ 3.26·2πh = 20.48h ≤ 21h.
Both cases are ≥ 2|A| − E(h), E(h) = 1764h² + 223h + 4 (223 ≥ 210 + 4π = 222.57; 4 ≥ 1/100).
The topological Steps 4–6 (P2, P3, P6, Lemma W) were refereed twice in their earlier form (REF_E, REF2) and
§5.2 says the consolidated write-up "has not itself been re-refereed"; I found no error in them on this reading,
but I did not re-referee the plane topology in depth (Task 2 bypasses it).

### 1(c) Lean encodings vs paper — CORRECT

- `Yout X ρ = {y ∈ X∖D : ∃ w ∈ X, dist y w > Δ₂ − ρ}`. For y ∈ K, depth(y) = dist(y, ℝ²∖K) =
  min_{w∈X}(Δ₂ − |y − w|) (complement of an intersection is the union of complements). So
  ∃w: |y − w| > Δ₂ − ρ ⇔ min_w(Δ₂ − |y − w|) < ρ ⇔ depth y < ρ. Exact (X ≠ ∅).
- `Yset = X ∖ D ⊆ K`: a non-D point has no partner at distance Δ, so all its distances are ≤ Δ₂ (Δ₂ is the
  largest distance < Δ). Correct for `Normal` (Δ₂ ≥ 10⁴ > 0, so `dist2` is not the junk value 0).
- `Aset = S ∖ D = Y ∩ ∂K`: "⊆": a Δ₂-partner w gives |a − w| = Δ₂, so a ∈ K ∩ C(w, Δ₂) ⊆ ∂K.
  "⊇": if y ∈ Y and |y − w| < Δ₂ for all w, y ∈ int K; so y ∈ ∂K gives some w with |y − w| = Δ₂, and w ≠ y.
- `defc Z = 3|Z| − mult Z 1` = 3|V| − e(G[Z]) because `minDist X = 1`.
- `Normal` supplies δ = 1 (`minDist_eq`), Δ ≤ 1.94Δ₂ (`nondeg`), Δ₂ ≥ 10⁴, n ≥ 4. The remaining facts §5.2 uses
  are derived: int K ≠ ∅ and |A| ≥ 2 from |A| > 1000h; h ≥ 3/2 from ρ ≥ 1; h < Δ₂/200 is a hypothesis.
  "Y ⊆ X ∩ K with min distance 1" holds for Y = X ∖ D. No hypothesis of §5.2 is missing from `CoreE`.
- Note (harmless): Theorem E′ is stated for arbitrary Y ⊆ X ∩ K; `CoreE` fixes Y = X ∖ D and A = S ∖ D, which is
  the only instance used downstream.

### 1(d) Verdict on `CoreE`

**`CoreE` is TRUE as stated, given the refereed §5.2** (and independently given the visible-path proof, §2).
Gaps: none mathematical. One documentation fix: the justification "per K > 100h ⇒ r_in > h" in the `CoreE`
docstring and in MAIN97_PLAN.md must read "per K ≥ |A| > 1000h > 300πh ⇒ r_in ≥ per K/(300π) > h".

## 2. Task 2 — hostile referee of the visible-path proof (RouteA_visiblepath_report.md)

Convention below: ν increases counter-clockwise; at a ray pointing "up", increasing ν means moving left; the
path is traversed with ν increasing; ψ = arg d − ν.

### 2.1 Setting and Lemma 0 — CORRECT

- Removing isolated vertices: Def(G[Yout]) = Def(H) + 3·#iso and 3 ≥ 2, so a bound for H in terms of
  |A ∩ V(H)| gives the bound for G[Yout] in terms of |A|. Correct.
- Drawing depth < h: a point of a unit edge is within ½ of an endpoint of depth < ρ, depth is 1-Lipschitz. So
  𝒟 ∩ K′ = ∅. Correct.
- Lemma 0, checked line by line. (2) first-order increase of the min of finitely many smooth functions: correct.
  (3) Carathéodory in ℝ²: 0 in the hull of two unit vectors forces them antipodal: correct. (4)
  D(w, Δ₂) ⊆ {(x − o)·u_w ≤ r} for active w: correct; triangle with incircle radius r has min altitude
  r(a+b+c)/max ≤ 3r: correct. (5) Lemma F steps 1–9 (re-checked in §1(a)) give diam K ≤ 100·w₀ ≤ 300h.
  (6) upper/lower graphs over the long axis: Σ|Δx| ≤ 300h, Σ|Δy| ≤ 2w ≤ 6h per graph, |Δx| + |Δy| ≥ 1: so
  |A| ≤ 2(306h + 1) < 1000h (h ≥ 3/2). Correct. It replaces Steinhagen and perimeter, as claimed.

### 2.2 Step 1 (N1–N6) — CORRECT; N4 needs its (easy) proof written

- (N1) ψ_c bound: |w₁ − w₂| ≤ Δ ≤ 1.94Δ₂, R′ = Δ₂ − h > (199/200)Δ₂: sin(ψ_c/2) ≤ 194/199. Σψ_c ≤ 2π. Correct.
- (N2) nearest-point projection onto the compact convex K′: rays partition ℝ² ∖ K′. Correct.
- (N3) poles: on an arc range r_ν = {w + sν : s > R′}; on N(c), r_ν = {c + tν}; at a range boundary the two
  poles (w_i and c = w_i + R′ν_i) both lie on the line of the common ray, behind every point of the ray. Correct.
- **(N4) is asserted without proof.** A clean proof (arc/corner transitions play no role):
  (i) ν = arg(x − P x) is continuous off K′ (P is 1-Lipschitz);
  (ii) a segment σ not contained in a ray meets each ray at most once (two distinct lines meet once; if σ lies on
  the line of r_ν it lies either inside r_ν or on the far component of that line minus K′, which is transversal to
  every ray it meets) — so ν|σ is injective, hence strictly monotone on a lift;
  (iii) ν(σ) lies in an open half-circle: separate σ from K′ by a line {x·u = s′} with K′ ⊆ {x·u ≤ s′}; then
  x = y + tν with y ∈ K′ and x·u > s′ force ν·u > 0;
  (iv) d = ±ν(x) at some x ∈ σ would put a neighbourhood of x in σ on r_ν(x), contradicting (ii); so ψ ∈ (0, π)
  with constant sign, and the local pole picture (N3) shows ψ ∈ (0, π) ⇔ ν increasing. Only 1-D facts are used
  (continuous injective map on an interval is monotone: `Continuous.strictMono_of_inj`-type).
- (N5) offset points: D(y, h) ⊆ K and touches ∂K at y + hν, so K is smooth there with normal ν. Hence every
  K-corner lies in some Z_c. For a ∈ Z_c, N_K(a) ⊆ N(c) (monotone Gauss map, endpoint normals ν_i at p_i).
  Correct. **Missing sentence (needed in Step 6):** ν(a)·n_a > 0 for every a ∈ A. For a ∉ ∪Z_c it is 1. For
  a ∈ Z_c, ν(a) = (a − c)/|a − c| and D(c, h) ⊆ K gives (c − a)·n_a ≤ −h < 0. Note that |α_a| ≤ ψ_c does NOT
  give this, since ψ_c can be as large as 2θ* ≈ 2.69 > π/2. Consequence: |α_a| < π/2 always.
- (N6) len Z_c = ∫_{N(c)} H dφ with G(ν_i) = (hν_i)·(iν_i) = 0: correct (support-function identity; on each
  circular piece it is an explicit antiderivative, at K-corners a zero-length jump). H ≤ |x − c| ≤ |T − c| =
  h/cos(ψ_c/2) ≤ κh, κ = 199/√1965 = 4.48923 < 4.49. Σ len Z_c ≤ 2πκh = 28.2067h < 28.22h. Correct.

### 2.3 Step 2 (visible path, V1–V4, m ≥ n + J) — CORRECT WITH ONE FALSE SENTENCE (gap G1)

- (V1) constancy of the first-hit edge on I_i: correct (edges meet only at common endpoints — P1 plus
  "no vertex inside a unit edge"; the hit parameter is continuous, so IVT on the difference).
- (V3.1) needs a compactness sentence: if drawing points x_k ∈ r_{ν_k}, ν_k → ν_i, were below e's hit point, a
  subsequence on one edge e′ converges to a point of e′ ∩ r_{ν_i} not beyond B_i, i.e. to B_i, so e′ = e
  (B_i is interior to e). Fine.
- (V3.2)–(V3.4): correct. Feet have κ > 0 (the jump at a foot L_i ≠ B_i is inward, at R_i ≠ B_i outward, and
  ψ ∈ (0, π) strictly on a transversal edge).
- **G1 (V4, false as written): "A vertex lies on exactly one ray, so it is a corner at most once."** Counter-
  example (the "dip"): v with path edges on both sides (L_i = R_i = v) and a pendant vertex B = v − ν(v) joined
  to v by a *radial* unit edge (possible whenever ρ ≥ 2: depth B = depth v + 1 < ρ). Then B_i = B and the
  path is v → B → v: **v is a corner twice**. The author's harness asserts this never happens
  (`assert … 'vertex visited twice'`) and it indeed never arose in the random tests (it is a measure-zero event);
  `l97R_dip.py` builds it exactly (v may even be an A-point) and the author's harness raises the assertion.
  **Fix:** let m count corner *occurrences*. (V4)'s bound m ≥ n + J is unchanged (it only needs one occurrence
  per piece boundary and per hit-arc end). The wedge lemma holds per occurrence, the wedges of different
  occurrences of one vertex are disjoint (they lie below different path pieces on different sides of −ν₀, the
  radial edge direction −ν₀ lying in neither), and Step 5 with k free arcs gives exactly
  Def_v ≥ (3/2π)Σ_occ(2π/3 − κ) (+1 for A-points, with H⁺_a as an extra disjoint free arc). Checked in
  `l97R_dip.py` with the patched harness `l97R_harness.py` (occurrence counting): all checks pass, MI slack ≥ 1.
  (Merging the two occurrences into one corner with κ = κ₁ + κ₂ is NOT correct: the single wedge would contain
  the radial edge.)
- Hit arcs: #hit arcs = J exactly when J ≥ 1 (every escape interval is followed by a hit ray); one-ray hit arcs
  need one vertex corner = p + 1 with p = 0. So m ≥ n + J (J ≥ 1), m ≥ n (J = 0; a single piece cannot close up
  since an edge's ν-arc is < π). Correct.

### 2.4 Step 3 (turning identity) — CORRECT (a definition-level telescoping)

Σ_corners κ = Σ_i [ψ_out(last at ν_i) − ψ_in(first at ν_{i+1})] = Σ_{hit}|I_i| − πJ. The content is only that
ψ along a fixed edge decreases by exactly Δν (d constant), and ψ ≡ π / 0 at virtual arrivals / departures.
No winding number, no lifting beyond ψ ∈ [0, π]. Then Σ_{vertex occ} κ ≤ 2π − |E| − πJ because feet κ ≥ 0.

### 2.5 Step 4 (wedge lemma) — CORRECT

- |W_v| = (ψ_in + π) − ψ_out = π − κ_v; orientation checked (W_v is the K′-side of the path at v).
- Sine rule: distance from the pole = D sin ψ / sin(ψ − δ), ∂/∂ψ = −sin δ / sin²(ψ − δ) < 0: correct.
- Different poles on the two sides (arc/corner transitions): each side is compared with its own pole, both on
  the line of r_{ν₀} behind v. Correct.
- Outward-jump sides (ψ = 0): the path on that side is near R_i, at pole distance D_R > D; pointwise in d as
  s → 0. Correct. −ν₀ ∈ W_v only when v = B_i. Correct.
- Virtual sides: all nearby rays on that side escape. Correct — but note the conclusion there is "on an escaping
  ray", which does NOT put v + sd inside K. Step 6 correctly uses the wedge lemma to get a + s n_a ∈ K only when
  both sides are real (see 2.6).

### 2.6 Steps 5–6 (per-vertex) — CORRECT modulo G1 and the missing sentence of 2.2

- Step 5: points ≥ 60° apart; a closed arc of length μ holds ≤ 3μ/π + 1; with k disjoint open free arcs,
  deg ≤ 3(2π − Σλ)/π + k, so 3 − deg/2 ≥ (3/2π)Σ(λ_j − π/3). Correct (also for touching arcs and λ = 0).
- Interior A-corner: bounding directions of W_a are edge directions from a (strictly inner by the chord
  inequality) or −ν(a) (strictly inner by the missing sentence of 2.2). There is no outward jump from a and no
  inward-jump arrival at a (a is the last point of its ray in K). n_a ∈ W_a would put a + s n_a strictly between
  y(ν) and a first hit, hence in K, but |a + s n_a − w| = Δ₂ + s. So W_a avoids n_a, hence lies in the open inner
  half-circle and is disjoint from H⁺_a. Correct; κ_a = −π is impossible here.
- A-endpoint (start type; end type symmetric): a = B_s = R_s. In coordinates relative to ν₀,
  W_a = (ψ_out, 2π), H⁺_a = [α − π/2, α + π/2], ψ_out − α ∈ (π/2, 3π/2) (inner edge). The overlap is exactly
  [α + 3π/2, 2π), of length π/2 − α ≤ π/2 + |α|. Correct (with |α| < π/2 from 2.2).
- A one-ray hit arc whose vertex is in A is impossible in H (such an a would be isolated). Correct.

### 2.7 Steps 7–8 (summation, counting, assembly) — CORRECT

- MI: Def(H) ≥ |A| + (3/2π)[(2π/3)m − Σκ] − (3/2π)Σ_{endpoints}(π/2 + |α_a|) ≥ |A| + m − 3 + (3/2π)|E| −
  (3/2π)Σ|α_a|, using #endpoints ≤ 2J. Correct.
- α-term: Σ|α_a| ≤ Σ_c ψ_c(1 + len Z_c) ≤ 2π + κh·2θ*·2π; times 3/2π: 3 + 6θ*κh = 3 + 36.26h (θ* = 1.34616,
  exact bound θ* ≤ 1.347 verified by the Taylor lower bound for sin).
- Counting: every A-point is on a hit ray; within a closed hit arc the exit map e is injective and monotone, so
  #A ≤ μ_K(I) + 1 (chord ≤ Σ sub-chords ≤ Σ R·angle). Per piece: two points at distance ≥ R′ from w, angle
  Δν apart, are ≥ 2R′ sin(Δν/2) apart (minimised at s₁ = s₂ = R′); y/sin y ≤ 1 + y², y ≤ 1/R′; so
  μ_K(piece) ≤ 1 + ε′ + col(piece), ε′ = (h + Δ₂/R′²)/R′. Σ col ≤ Σ len Z_c. min(n, |A|) trick correct.
  ε′|A| ≤ 6.457h + 0.022.
- Assembly: m ≥ n + J ≥ |A| − 34.68h − 0.03; Def(H) ≥ 2|A| − 70.96h − 6.03 ≥ 2|A| − (71h + 7). Arithmetic
  re-derived; `l97A_vp_constants.py` (exact Fractions) re-run: passes.

### 2.8 Degenerate cases

| case | status |
|---|---|
| isolated vertices | removed; 3 ≥ 2 per isolated A-point — correct |
| pendant A-points | Def_a ≥ 1 (non-corner) or per-occurrence bound — correct |
| A-points at K-corners | lie in some Z_c; any disc normal n_a ∈ N(c); |α_a| < π/2 — correct (needs 2.2 sentence) |
| several vertices on one ray | path L → B → R — correct; **dip = G1** (vertex twice), fixed by occurrence counting |
| radial edges (on a ray) | never a first-hit edge on an open interval; only appear below the path as "stalactites" — correct |
| edge on the far part of a ray line | transversal to every ray it meets — correct |
| edge tangent to a ray | impossible (segments/lines) |
| vertex on a ray at an arc/corner boundary | two poles, one per side — correct |
| J = 0 | Σκ = 2π, m ≥ n, |A| ≤ μ_K(S¹) — correct |
| one-ray hit arcs | two virtual ends at one corner, κ = −π — correct |
| int K′ = ∅ | excluded by Lemma 0 |

### 2.9 Counterexample searches (all with `.venv/bin/python`, one process, < 100 MB)

- `l97R_dip.py`: exact dip configurations (D2 ∈ {60, 200, 500}, ρ ∈ {2, 3}, one or two radial pendants): the
  author's harness raises `vertex visited twice`; the patched harness (`l97R_harness.py`: occurrence counting,
  per-occurrence per-vertex claims, and an explicit check of |W_a ∩ H⁺_a| ≤ π/2 + |α_a|) passes all checks.
- `l97R_stress.py 300 2`: SHARP corners, which the author's tests did not reach (their lenses had
  |w₁ − w₂| ≤ 1.2Δ₂, i.e. ψ_c ≲ 1.3; here lenses with |w₁ − w₂| ∈ [1.5, 1.94]Δ₂, ψ_c up to ≈ 2.69, and
  three-disc bodies), Δ₂ ≥ 200h (the CoreE regime), ρ ∈ {1..5}, A-chains concentrated on the collapse zones,
  A-points exactly at K-corners, dense apex growth and pendants. **300/300 pass** every check (wedge, ψ, feet,
  turning identity to 1e-20, A-neighbours inner, per-occurrence per-vertex claims, the overlap bound
  |W_a ∩ H⁺_a| ≤ π/2 + |α_a|, MI, and Def ≥ 2|A| − (35h + 4)). Extremes: min Def − 2|A| = 5 (ρ = 1, three
  discs), min MI slack 2.86, max |α_a| = 1.164 rad (< π/2, as G2 predicts; the author's tests only reached
  overlap excess 0.476, here 1.158), max |A| − (n + J) = **+4** (lens, |w₁ − w₂| = 1.88Δ₂, ρ = 3). The last
  number shows that the collapse term of the counting lemma CL is genuinely needed: at sharp corners several
  A-points of Z_c sit over one visible piece. (The author's runs always had |A| − (n + J) ≤ 0.) Both are
  within the proved allowances (34.7h, 36.3h).
- Scope: floats at 40 digits with 1e-25 tolerances (angles are transcendental, so exact rational checks of
  the geometric lemmas are impossible); the constants are checked exactly (`l97A_vp_constants.py`, re-run).
  No counterexample was found, and none is expected: every failure mode I could construct is excluded by a
  proof, not only by the tests.

### 2.10 Verdict, fixes, formalisability

**Verdict: CORRECT WITH GAPS (all minor, all fixable in a few lines).** No counterexample; the final bound
Def(G[Yout]) ≥ 2|A| − (71h + 7) follows, and it implies `CoreE` with the current `Eh` (1764h² + 152h − 3 ≥ 0
for h ≥ 3/2) under exactly CoreE's hypotheses (δ = 1, Δ ≤ 1.94Δ₂, h < Δ₂/200, |A| > 1000h; ρ ∈ ℕ is not used).

Fixes:
1. **G1 (V4).** Replace "a vertex is a corner at most once" by occurrence counting; state the wedge lemma per
   occurrence; note that the wedges of the occurrences of one vertex are disjoint; apply Step 5 with k free
   arcs. (Needed only for dips, which require ρ ≥ 2.)
2. **G2 (N5/Step 6).** Add: ν(a)·n_a ≥ h/|a − c| > 0 for a ∈ Z_c because D(c, h) ⊆ K; hence |α_a| < π/2 and
   −ν(a) is strictly inner. (|α_a| ≤ ψ_c alone does not give it.)
3. **G3 (N4).** Write the injectivity proof (2.2): continuity of P, "a line meets a ray at most once",
   separation ⇒ ν(σ) in an open half-circle.
4. **G4 (V3.1).** Add the compactness sentence (2.3).
5. Cosmetic: "E" is used both for the escape set and for edges; "|W_a ∩ H⁺_a| ≤ π/2 + |α_a|" is in fact
   π/2 ∓ α_a (sign by side).

**Formalisability without plane topology: YES.** No step uses the Jordan curve theorem, faces, Euler, winding
numbers or path lifting. The only topological inputs are 1-D: continuity of the nearest-point map, "continuous
injective on an interval ⇒ monotone", IVT for the order of two edges along rays, a compactness argument in V3.1,
and cyclic telescoping on a finite sorted list of angles. The relative angle ψ ∈ [0, π] is a canonical real value,
so the "lift" is by definition, not by a covering argument. I found no step that secretly uses a Jordan- or
winding-type fact: global information enters only through (a) the cyclic partition of S¹ by Φ (Σ|I_i| + |E| = 2π)
and (b) "A-point = last point of its ray inside K" (convexity). The heavy Lean part is N1–N6 (local structure of
the support map of an intersection of discs, poles at range boundaries) and μ_K (circular arc lengths along ∂K).

Side remark of the report (O(√n) error for E′): plausible (E = O(h) lets ρ₀ ≍ √n; Δ₂ ≳ √n keeps ρ₀ ≤ Δ₂/400
admissible), not checked here.

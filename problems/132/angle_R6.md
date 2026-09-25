# Erdős #132 / CDL Problem 1.6: Angle R6, from 15/11 to 4/3

Date: 2026-09-24. Scratch files are in `scratchpad/R6/`. Scripts are `scripts/r6_*.py`.

**Results.**

| statement | regime | status |
|---|---|---|
| **L ≤ 4/3** (Theorem N3: the average R-weight is ≤ 8) | all | PROVED, refereed (REF_N3: correct, cosmetic fixes applied) |
| **min ≤ 21n/16 + C** (Theorem P4: the average R-weight is ≤ 7) | Region I (τ ≤ √3/2 − 2β) and τ > 1 | PROVED, refereed (REF_B1: correct; two passages rewritten, numeric slips fixed) |
| **min ≤ 9n/7 + O(n^{2/3})**, which matches the global lower bound 9/7 | τ > 1 | PROVED given E′ (REF_E; REF2: correct given E′) |
| Theorem E′: Def(G[X∖D]) ≥ 2\|S∖D\| − 3·10⁴n^{2/3} | all nondegenerate | PROVED. Refereed twice (REF_E, REF2: correct with gaps). The complete corrected proof with G1–G5 is §5.2; that write-up is not yet re-refereed |
| e(S) ≤ s + ½\|Q′\| + C, so the \|Q\| floor at 4/3 disappears | Region II | PROVED by branch B2; **not refereed** |
| e(S) ≤ s + 70/d + C, with d = \|2 sin θ₀ − 1\| | Region III outside a window of width O(1/R) | PROVED by B2; **not refereed** |
| the exact hexagonal strip holds the method at 4/3 | the resonance window τ = √3/2 + O(1/R) | OBSTRUCTION (exact, 60 digits) |

The previous bound was 15/11 ≈ 1.3636 (angle_R4). The lower bound is still 9/7 ≈ 1.2857. The global bound is **4/3**. What prevents going lower is Region III near τ = √3/2, where the |Q| term cannot be removed, together with Region II, where no weight-side improvement (average v < 8) is proved.

The new ingredient is **Theorem N3**: the R-weight v(y) := deg y + m_y is at most 8 *on average* over 𝓡, up to O(1). Theorem N1 bounds it by 10 pointwise. The proof has two ideas.
1. **Pinning.** Suppose a K-row neighbour p and a D-neighbour z of y differ in height by Δc. Then Lemma 3.2(b)/(c) forces t = Δc + O(ε₀). Each heavy configuration (v ≥ 9) therefore fixes t: fans need t ≈ √3/2 and caps need t ≈ ½.
2. **Private lower neighbours.** Every heavy point has one or two neighbours below it, deep inside K. These have weight ≤ 7 (fans) or ≤ 6 (caps), and no two heavy points share one. Each heavy point passes its excess over 8 to them.

With the |Q| term of angle_R4 this gives 4/3 in every τ-regime. That is exactly the floor of the μ(Δ₂) ≤ 1.5s − 0.5|Q| method in Regions II and III (angle_R4 §1 table), and also the Region-I value for average weight 8.


## 1. Theorem N3 and its proof

**Theorem N3.** There is an absolute constant C₃ such that Σ_{y∈𝓡}(deg y + m_y) ≤ 8|𝓡| + C₃. This holds for every τ, in the nondegenerate regime with Δ₂ ≥ 10⁴.

**Corollary (L ≤ 4/3).** μ(δ) ≤ e(S) + 4r + C by identity A.0.1. In every τ-regime e(S) ≤ s + |Q| + C (angle_R4 §§2–3, WRITEUP_A2 §6), and μ(Δ₂) ≤ 1.5s − 0.5|Q| + C_V. Weights 2/3 and 1/3 give min{μ(Δ₂), μ(δ)} ≤ 4n/3 + C. The degenerate regime gives n + 1, and Δ₂ < 10⁴ gives O(1). Hence **L ≤ 4/3**. `r6_n3_checks.py` verifies the LP certificate.

### 1.0 Parameters
ε₀ = 1/50, ε = tan ε₀ < 0.02001. Λ = 464 (half-length of the boundary arc; R4 used 232).

### 1.1 Good points
y ∈ 𝓡∖D with h := dist(y,∂K) ≤ 1 is *good* if (i) per K ≥ 2Λ, (ii) γ_y := arc of ∂K of arc-distance ≤ Λ from a
nearest boundary point p₀ has turning ≤ ε₀, (iii) ∂K ∩ B̄(y,3) ⊂ γ_y.
- (i) fails ⇒ diam K < Λ ⇒ |X∖D| = O(1).
- (ii) fails for O(1) points y: Lemma BT verbatim with Λ = 464 (b ∈ γ_y ⇒ |b−y| ≤ Λ+1, multiplicity ≤ (2Λ+3)²).
- (iii) fails ⇒ Lemma T* below ⇒ |X∖D| = O(1).
Points of 𝓡∩D have v ≤ 6, points with h > 1 have v ≤ 6 (A.0.3). So all but O(1) points y with v(y) ≥ 7 are good.

**Lemma T\*.** If p, b ∈ ∂K with |pb| ≤ 4 and both boundary arcs between them have length > Λ = 464, then K lies in
a box of size 1000 × 21.5, so |X∖D| < 3·10⁴.
Proof = Lemma T of R4 with p in place of y's foot point:
- ν_p = ν_b ⇒ [p,b] ⊂ ∂K, an arc of length ≤ 4. ✗.
- cone case with opening θ: the arc on the apex side has length ≤ |Ap|+|Ab| = |pb|(sin∠p+sin∠b)/sin θ ≤
  |pb|/sin(θ/2) ≤ 4/sin(θ/2); for θ ≥ 1° this is ≤ 458.4 < 464 ✗. So θ < 1° or strip (ν_p = −ν_b, width ≤ 4).
- Fatness step: cross-section width at p's level w₀ = |pb|-projection ≤ 4/cos(θ/2) ≤ 4 + 4 tan(θ/2) < 4.04 (upper bound); W ≤ w₀ + 2 tan(θ/2) L; if L ≥ 1000 then
  tan φ* = 2W/L ≤ 2w₀/1000 + 4 tan(0.5°) < 0.0430 and (2R cos φ* − W)/R ≥ 2cos φ* − w₀/10⁴ − 4 tan(0.5°) > 1.962 > 1.94,
  contradicting |w_bot − w_top| ≤ Δ ≤ 1.94R. So L < 1000 and W < 4.04 + 2000 tan(0.5°) < 21.5, and packing gives |X∖D| < 3·10⁴ (≈ 28 664 with W < 21.49; only the bound < 3·10⁴ is used). ∎
For good-(iii): p₀ ∈ B̄(y,1) and b ∈ B̄(y,3) give |p₀ b| ≤ 4.

### 1.2 Local frame at a good y (Lemma F′)
Coordinates: origin p₀, x along t₀, z along the outer normal n₀ = (p₀−y)/h; y = (0,−h). As in Lemma F:
there is a concave f on [−463, 463], f(0)=0, −ε|x| ≤ f ≤ 0, whose graph ⊂ γ_y, with
 (F′0) ∂K ∩ B̄(y,3) ⊂ graph f; U′ := B̄(y,3) ∩ {z < f(x)} ⊂ int K (connectedness argument of Lemma F; U′ convex).
 (F′1) q ∈ X ∩ B̄(y,3), q ∉ int K ⇒ q_z ≥ f(q_x).
 (F′2) q ∈ (S∖D) ∩ B̄(y,3) ⇒ q_z = f(q_x).
 (F′3) q ∈ D ∩ B̄(y,3) ⇒ q_z ≥ f(q_x) + t  (q is not below the graph, else q ∈ U′ ⊂ K; the graph point under q is in K).
 (F′4) every inward normal of K at a point of γ_y is within ε₀ of −n₀.
For a neighbour q = y + (sin ψ, cos ψ) put c(q) := cos ψ = q_z + h ("height above y").
 K-row neighbour: c ∈ [h − ε, h] and |ψ| < 90° + ε₀. D-neighbour: c ≥ h + t − ε. int-K neighbour: c < h.
 (All three from F′1–F′3; sharp F1 gives |ψ| < 90°+ε₀ for every S-neighbour.)

**Lemma DN (D-normals are nearly vertical).** For z ∈ D ∩ B̄(y,3) with diametral partner x_z, u_z := (x_z − z)/Δ
= (a₁, a₂) satisfies a₂ < 0 and |a₁|/|a₂| ≤ τ₃ := (463ε + 3)/460 < 0.0267. For D-neighbours of y (|z_x| ≤ 1, z_z ≤ 1) the bound improves to τ* := (463ε+1)/462 < 0.0224; Lemma P uses only this case, and the scripts use the weaker 0.0245.
Proof. Every k ∈ K has (k − z)·u_z > 0 (|k − x_z| ≤ R < Δ = |z − x_z|). The graph point below z is in K and lies
strictly below z (F′3), so a₂ < 0. With c := −a₂ > 0, the graph points
g± = (±463, f(±463)) ∈ K give (463 ∓ z_x)(±a₁) > (f(±463) − z_z)c ≥ −(463ε + z_z)c, with |z_x| ≤ 3, z_z ≤ 3. ∎
**Corollary (D–D heights).** For z₁, z₂ ∈ D ∩ B̄(y,3): |z₁,z − z₂,z| < τ*|z₁,x − z₂,x|. (Lemma 3.2(a) both ways.)

### 1.3 Classification of heavy points (v ≥ 9)
Let y be good. Neighbours are pairwise ≥ 60° apart as seen from y.

**Lemma P (pairs).** y has at most two K-row neighbours and at most two D-neighbours (in S or not). Two of the same
kind at ψ₁ < ψ₂ satisfy |sin((ψ₁+ψ₂)/2)| ≤ |Δc|, because |Δc| = |cos ψ₁ − cos ψ₂| = 2|sin((ψ₁+ψ₂)/2)| sin((ψ₂−ψ₁)/2) and sin((ψ₂−ψ₁)/2) ≥ ½. For K, |Δc| ≤ ε by (F′2). For D, |Δc| < τ*|Δx| ≤ 2τ* < 0.049 by DN. So |ψ₁+ψ₂| ≤ 2 arcsin(0.049) < 5.62°
(D) and < 2.30° (K). Three of one kind: ψ₁+ψ₂ ≈ 0 ≈ ψ₂+ψ₃ forces |ψ₃ − ψ₁| < 12° ✗.

**Lemma M (m_y = 4).** The four S-neighbours are at ψ within ε₀ of −90°, −30°, 30°, 90°, of kinds K, D, D, K.
(All in (−90°−ε₀, 90°+ε₀), pairwise ≥ 60°. By Lemma P, two K and two D, each pair mirror-symmetric, so the pairs
are {1,4},{2,3}. K at ±30° forces h ≥ cos(31.2°) > 0.85 and then D at ±90° would need sin ε₀ ≥ h + t − ε ✗.)

**Lemma H (deg 6, m 3).** The six neighbours form an exact regular hexagon. Among 3 S-neighbours two are of the same
kind (Lemma P), a mirror pair; so the hexagon is within 2.81° of {0°,±60°,±120°,180°} or {±30°,±90°,±150°}.
Enumerating (only slots with |ψ| < 90°+ε₀ can be S):
- K pair at ±30°: h > 0.84, third S is D at ±90°: D at ±90° has c ≤ sin 2.81° < 0.05 but needs c ≥ h + t − ε > 0.82 ✗.
- D pair at ±30° + K at +90° or −90°: **half-fan HF2**.
- K pair at ±60° + D at 0°: **cap** (needs t ≤ ½ + O(ε)).
- D pair at ±60° + K at 0°: K at 0° gives h ≥ 0.998, D needs c ≥ 0.978 but c ≤ 0.55 ✗.
- K pair at ±90° + D at +30° or −30°: **half-fan HF1**.
- D pair at ±90° + K at ±30°: D gives h ≤ 0.07, K gives h ≥ 0.84 ✗.

So v(y) ≥ 9 (i.e. (deg,m) ∈ {(6,4),(5,4),(6,3)}) implies y is one of
- **F6** (6,4): K at ±90°, D at ±30°, lower points a± at ±150° (all within 3°), v = 10;
- **F5** (5,4): as F6 with one lower point a at ψ ∈ [147.7°, 212.3°], v = 9;
- **HF1/HF2** (6,3): hexagon ≈ {±30°,±90°,±150°}, lower points a± at ±150°, v = 9;
- **cap** (6,3): K at ±60°, D at 0°, lower points at ±120°, b at 180° (hexagon offset |δ| ≤ arcsin ε < 1.15°), v = 9.
F6/F5/HF are "fan type".

**Lemma Pin (t is pinned).** If y is fan type then t ∈ [0.74, 0.99]; if y is a cap then t ∈ [0.43, 0.57].
Proof. y has a K-row neighbour p and a D-neighbour z with height gap Δc := c(z) − c(p) ≥ 0.78 (fan) or ∈ [0.48,0.52]
(cap). By (F′4) u_p = (sin β′, −cos β′), |β′| ≤ ε₀, so (z−p)·u_p ≤ 2 sin ε₀ − Δc cos ε₀ < 0: z is not normal for p,
so by Lemma 3.2(b) |z − w_p| = Δ, and then exactly (z−p)·u_p = −t + (d² − t²)/(2R), d = |zp| ≤ 2. Hence
|t − Δc| ≤ 2 sin ε₀ + Δc(1−cos ε₀) + 2·10⁻⁴. ∎
(Remark: this corrects R4's claim that the chord-midpoint fan is "admissible throughout Region I". A fan forces
t = √3/2 + O(ε₀), and a cap forces t = ½ + O(ε₀). The referee's exact windows are fans t ∈ [0.751, 0.950] and caps t ∈ [0.442, 0.558]. Outside them there are no heavy *good* points. With ε₀ = 1/50 the fan window still meets Region I (t ≤ 0.846); with ε₀ ≤ 4·10⁻³ it does not (branch B1).)

### 1.4 Charging
- F6 sends 1 unit to each of a₊, a₋; F5 sends 1 to a; HF1/HF2 send 1 to a₊ (the lower point at ≈ +150°); cap sends
  1 to b. Orient t₀ counter-clockwise; the HF2–HF2 argument below makes this orientation irrelevant. The O(1) non-good points send nothing and contribute at most 4·#(non-good) to the excess.
**Receivers.** All receivers lie in U′ (below the graph) ⊂ int K, so they are in 𝓡∖D and are not heavy... check:
- fan receiver a (ψ_a ∈ [147°, 213°]): a_z ≤ −cos 33° < −0.838. Any S-neighbour q of a lies in B̄(y,2) and has
  q_z ≥ f(q_x) ≥ −0.04 (F′1), so q − a has vertical component ≥ 0.79, i.e. q is within 38° of vertical from a. y
  itself is in that window (y − a vertical component ≥ 0.838). Three points pairwise ≥ 60° cannot fit in a 76°
  window, so m_a ≤ 1: **v(a) ≤ 7**.
- cap receiver b (ψ_b = 180° ± 1.2°, h ≥ 0.48): b_z ≤ −1.47, so an S-neighbour would need vertical component ≥ 1.43 > 1:
  m_b = 0, **v(b) ≤ 6**.
**Each receiver gets ≤ 1 unit.**
- Fans and caps never coexist (Lemma Pin, t is global).
- Two good points y, y′ with |y − y′| ≤ 2 have frames with ∠(n₀(y), n₀(y′)) ≤ ε₀ (p₀(y′) ∈ ∂K ∩ B̄(y,3) ⊂ γ_y).
- cap: both owners would be within 1.2° + 1.2° + ε₀ of vertical above b, < 60° apart ✗.
- fan: owners y ≠ y′ of a are both within 34.2° of vertical above a (common frame up to ε₀) and ≥ 60° apart as seen
  from a, so y′ is within ≈ 5° of y's slot ±90° at distance ≤ 1.11, hence equals y's neighbour in that slot (else two
  points < 1 apart). F6, F5, HF1 have K-row (S) points in both ±90° slots ✗ (y′ ∈ 𝓡). So y is HF2 with non-S point y′
  at +90° (say), and symmetrically y′ is HF2 with y at its −90°. Then y's D at +30° and y′'s D at −30° coincide
  (distance < 1), call it z; z has the four exact unit neighbours y, y′, y's D at −30°, y′'s D at +30° (hexagons are
  exact), but every D-point has degree ≤ 3 (all of X in an open half-plane at z) ✗.
Hence Σ_𝓡 v ≤ 8|𝓡| + 4·#(non-good) ≤ 8r + C₃. ∎

### 1.5 Consistency
ienjoymath's construction: τ → 0, all 𝓡 have v ≤ 6. R4's exact fan (t = 0.86598…): y has v = 10 locally with
a± present; in the one-centre model its z's are 𝓡∩D. 4/3 > 9/7 so no conflict with the lower bound.

## 2. Verification scripts (all pass)
- `scripts/r6_n3_checks.py`: 36 exact rational assertions with rigorous Taylor enclosures. They cover the Lemma T* constants (margin 0.0228 over 1.94), the Lemma BT count with Λ = 464, τ*, the pair tolerances, every excluded case of Lemmas M and H, the Lemma Pin intervals (fan t ∈ [0.746, 0.984], cap t ∈ [0.441, 0.558], disjoint), the receiver windows, the owner-uniqueness distances (|y′ − q| ≤ 0.233), and the LP.
- `scripts/r6_n3_search.py`: a floating-point sanity search of the relaxed slot model. It tested about 3·10⁴ type assignments; every configuration with v ≥ 9 is F6, F5, HF or a cap with the pinned t (found: 21 F6, 61 F5, 180 HF, 32 caps; 0 unclassified).
- `scripts/r6_n3_examples.py`: exact geometry in 60-digit Decimal.
  - (a) R4's fan chain: every y has (6,4). Its lower points have m = 1 and unique owners. t = 0.86598…, and Lemma 3.2(c) holds exactly at p–z.
  - (b) A new cap chain on chords of length √3: y has (6,3), b has m = 0, c has m ≤ 1, and t = 0.49996….
  - Byproduct: adjacent caps (and fans) cannot share lower points, because curvature pushes shared lower points to distance 0.99985 < 1.
- `scripts/r6_Eprime_full_checks.py`: 34 exact assertions for Theorem E′ (§5).
- Environment: the scripts that import numpy (`r6_gap_consistency.py`, `ring16.py`) fail under the project `.venv`, which has no numpy. Run them with the system `python3`. `r6_refE_parallel.py` needs mpmath.


## 3. Referee of N3 (REF_N3; `scratchpad/R6/A_ref/REF_N3_report.md`)

**Verdict: CORRECT.** The referee found no mathematical error and no missing configuration. Six textual fixes were applied above:
- the Lemma DN constant;
- the D case of Lemma P;
- the width in Lemma T*;
- the orientation and the constant 4·#(non-good);
- the cap offset < 1.15°;
- the qualified "no heavy good points" remark.

The referee also:
- recomputed every constant exactly (`scripts/r6_ref_constants.py`);
- built a fan and a cap in 60-digit Decimal (`r6_ref_examples.py`);
- ran float hexagon and (y,t) scans that enforce the Lemma 3.2(b) exact-distance rule on flat and cornered boundaries: about 1.4·10⁵ heavy configurations, 0 unclassified (`r6_ref_hexscan*.py`, `r6_ref_search.py`);
- ran a receiver stress test (`r6_ref_receivers.py`) and the ienjoymath ring (`r6_ref_ring.py`: max v = 6).

The exact Pin windows are: fans t ∈ [0.751, 0.950], caps t ∈ [0.442, 0.558].

## 4. Region I and τ > 1: average weight ≤ 7, giving 21/16 (branch B1 plus referee REF_B1)

Reports: `scratchpad/R6/A_below/B1_regionI/B1_report.md` (proof) and `scratchpad/R6/REF_B1/REF_B1_report.md` (referee).

The proof uses the N3 technology with ε₀ = 10⁻⁶, Λ = 10⁹ and radius-6 frames. Good points exist only for R ≥ 2·10¹⁵; smaller R is bounded n in the nondegenerate regime.

1. **Pinning, general form.** Near any K-row point, every D-point sits at height t ± 10⁻⁴ above the boundary. Consequently:
   - no good point has m = 4 in Region I;
   - m = 3 forces the kinds {K, K, D} and t ≥ ½.
2. **Classification (P2) of good points with v ≥ 8.** The types are:
   - A: the lattice row (6,2);
   - B: a pair of S∩D points at ±30°;
   - C_φ: only for t < ½, with t = sin(30° − φ);
   - A′ and cap: t = ½;
   - Dtype (5,3): t ∈ [sin(ψ_K − 30°), 1 − cos ψ_K].

   **So v ≤ 8 in Region I except at caps.**
3. **Radius-1 discharging to deep int-K neighbours**, with one forwarding step through 7-points. A cone lemma (senders lie within ±61° of the receiver's upward normal) and a band analysis (L: t ≤ ½ − κ; Th: |t − ½| ≤ κ; H; T) show that every receiver gets load ≤ 1. Hence Σv ≤ 7r + C.
4. **LP.** Region I and τ > 1 have e(S) ≤ s + C and μ(Δ₂) ≤ 1.5s. So μ(δ) ≤ s + 3.5r + C, and weights 5/8 and 3/8 give **21n/16**.

**Referee corrections** (none changes the result):
- **Band Th.** No receiver ever has three senders: a ±60° sender forces the receiver to depth ≈ 1, and a 0° sender forces depth ≥ 1.49 (margin ≈ 0.47). This replaces B1's muddled case β.
- **Forwarding targets** receive directly only in the slice t ∈ (1, 1 + 2δ₀]. There the load is ≤ ½ + ½ = 1. In the proper band H the target depth 2·depth(a) ≥ 1.769 exceeds every A, B and Dtype receiver depth, so they do not receive directly. There are no chains. (REF2 correction of REF_B1.)
- **Numeric slips:**
  - A's receivers are at depth √3;
  - B's receivers are at depth h + √3/2;
  - the K-angle bound is 30° in the τ > 1 slice.
  - B1's original half-open range [t, √3/2) for B is correct: H = √3/2 would put y on ∂K, hence in S (REF2 correction; an earlier note here wrongly said the range includes √3/2).
- **Lemma T\*** (fatness step) is repaired with the R4/N3 width bound.
- **The δ₀ budget** is written out line by line: < 5·10⁻⁵ against 10⁻⁴.
- **Script coverage.** B1's scripts test less than the report claimed. The referee's exact cap-lattice test at t = ½ (`r6_refB1_caplattice.py`: 3·10⁴ configurations with up to 6 heavy points) gives max final charge 7.0.

**Limit of the method (exact).** In the exact A-row stack and cap lattice (Q(√3), `r6_below_exact_examples.py`), every radius-1 rule leaves some point at 7, although the true average there is 6. So **21/16 is the limit of radius-1 charging**.

**Conjecture C1.** For each component C of G[𝓡], e(C,S) ≤ b(C) + 3 + Σ_inner(|f| − 3). This is equivalent to average ≤ 6, hence 9/7 in Region I. It is proved for |C| ≤ 2, and a search over clusters with |C| ≤ 7 finds max Φ = 0.

## 5. τ > 1: 9n/7 + O(n^{2/3}), matching the global lower bound 9/7, via Theorem E′

Sources: `scratchpad/R6/B_gap/GAP_report.md` §3 (first proof, superseded by §5.2 below), `B_gap/X/X_report.md` (Theorem E, Lemma F), `scratchpad/R6/REF_E/REF_E_report.md` (first referee), `scratchpad/R6/REF2/E/REPORT_FULL.md` and `REFEREE2_R6.md` §2 (second referee). Numerical inequalities: `scripts/r6_Eprime_full_checks.py` (34 exact assertions, Fractions only; run with `.venv/bin/python`).

§5.2 is the **single complete corrected proof** of Theorem E′. It incorporates G1–G5 and I-1 of the second referee:
- G1 is in Step 6;
- G2 is in Step 6 and fallback (F3);
- G3 is in the choice of ρ₀ (Step 0) and fallback (F1);
- G4 is in Step 3;
- G5 is Lemma W.

The written proof has not itself been re-refereed.

**Notation in this section.**
- δ = 1 is the minimum distance.
- G is the unit-distance graph, and Def(H) := 3|V(H)| − |E(H)|.
- n := |X|, and **Δ₂ is written out**. The letter r denotes |𝓡| elsewhere in this file and is not used here.
- **h denotes the shell depth**. The letter t keeps its global meaning t = Δ − Δ₂ (I-1).
- ρ₀ is the shell parameter. It is unrelated to the ρ₀ of WRITEUP_A2 §5.1.
- depth(z) := dist(z, ℝ²∖K) for z ∈ K.

### 5.1 Statement

**Theorem E′.** Let X be finite with minimum distance 1, n = |X| ≥ 1, and diam X = Δ ≤ 1.94Δ₂. Let K := ∩_{w∈X} D(w, Δ₂). Let Y ⊂ X ∩ K and A := Y ∩ ∂K. Then

  Def(G[Y]) ≥ 2|A| − C_E·n^{2/3},  with C_E := 3·10⁴.

**Application.** Take Y = X∖D. By Lemma 3.1(a), X∖D ⊂ K. Also (X∖D) ∩ ∂K = S∖D: "⊂" holds because every point of ∂K lies on some C(w, Δ₂), and "⊃" is Lemma 3.1(b). This gives

  **Def(G[X∖D]) ≥ 2|S∖D| − 3·10⁴·n^{2/3} in every nondegenerate regime (every τ).**

The constants depend only on Δ ≤ 1.94Δ₂. In particular they do not depend on t = Δ − Δ₂.

### 5.2 Proof

**Standard facts used.**
- (P1) G is a plane straight-line graph with maximum degree ≤ 6. If unit segments ab and cd crossed, the diagonals of the convex quadrilateral would give |ac| + |bd| < |ab| + |cd| = 2. That is impossible when all four points are ≥ 1 apart.
- (P2) Euler's formula for a plane graph with c ≥ 1 components is V − E + F = 1 + c. Also Σ_f |f| = 2E, where |f| is the total length of the boundary walks of the face f. Hence

  Def = 3 + 3c + Σ_f (|f| − 3).

  A bounded face of a simple plane graph has a cycle in its boundary, so it has |f| ≥ 3. The outer face has |f_out| = Σ_j |w_j|, summed over the components C_j incident to it, where w_j is the outer boundary walk of C_j.
- (P3) If a compact set Γ ⊂ ℝ² separates a convex body Q from ∞ and Γ ∩ Q = ∅, then H¹(Γ) ≥ per Q. To see this, let P_Q be the nearest-point map. It is 1-Lipschitz, and it maps Γ onto ∂Q: for b ∈ ∂Q with outer normal ν, the ray b + ℝ₊ν meets Γ, and P_Q = b on that ray.
- (P4) Perimeter is monotone under inclusion of convex sets, and per Q ≤ π·diam Q (Cauchy's formula).
- (P5) Steinhagen: every planar convex body has width w ≤ 3·r_in.
- (P6) Let K be a closed topological disk and a, b, a′, b′ points of ∂K in this cyclic order. Then every path in K from a to a′ meets every path in K from b to b′. This is a consequence of the Jordan curve theorem.
- (P7) If |A| ≥ 2, the boundary arcs of ∂K between cyclically consecutive points of A have length ≥ chord ≥ 1. Hence |A| ≤ per K + 1, and an arc of length ℓ contains at most ℓ + 1 points of A. Also per K ≤ 2πΔ₂, because K ⊂ D(w, Δ₂).

**Basic facts about K.**
- For z ∈ K, **depth(z) = min_w (Δ₂ − |z − w|)**. The complement of K is the union of the complements of the disks. So depth is 1-Lipschitz, and depth(z) ≥ h ⇔ D(z, h) ⊂ K.
- ∂K is a finite union of arcs of circles C(w, Δ₂). So K is strictly convex. In particular, a segment between two points of K meets ∂K at most at its endpoints.
- If int K = ∅, then |Y| ≤ 1 and there is nothing to prove. Assume from now on that int K ≠ ∅.

**Lemma F (fatness).** If diam X ≤ 1.94Δ₂ and int K ≠ ∅, then diam K ≤ 100·w(K), and therefore r_in(K) ≥ diam K/300.

*Proof.*
1. Let the minimal width w₀ be attained in direction u₀, and let v₀ ⊥ u₀. Let L be the width in direction v₀. Then diam K ≤ √(w₀² + L²). We may assume L ≥ 3w₀.
2. Let p, q ∈ K be extreme in the directions −v₀ and +v₀, and let m := (p + q)/2. The line m + ℝu₀ meets K in a segment [y₋, y₊] of length ≤ w₀. Write y₊ = m + s u₀ with 0 ≤ s ≤ w₀.
3. Since y₊ ∈ ∂K, we have y₊ ∈ C(x₊, Δ₂) for some x₊ ∈ X. Put n₊ := (y₊ − x₊)/Δ₂. Then every k ∈ K satisfies

   (k − y₊)·n₊ ≤ −|k − y₊|²/(2Δ₂).

4. Add this inequality for k = p and k = q. This gives −2s·u₀·n₊ < 0, so u₀·n₊ > 0.
5. Use the two inequalities separately. This gives |(p − m)·n₊| ≤ s·u₀·n₊ ≤ w₀, so |(q − p)·n₊| ≤ 2w₀.
6. Write q − p = Lv₀ + σu₀ with |σ| ≤ w₀. Then |v₀·n₊| ≤ 3w₀/L, and u₀·n₊ ≥ √(1 − 9w₀²/L²).
7. The same argument at y₋ gives x₋ with u₀·n₋ ≤ −√(1 − 9w₀²/L²). Hence

   1.94Δ₂ ≥ |x₊ − x₋| ≥ (x₋ − x₊)·u₀ ≥ 2Δ₂√(1 − 9w₀²/L²) − w₀.

8. If w₀ ≤ 0.02Δ₂, this gives √(1 − 9w₀²/L²) ≤ 0.98. Then L/w₀ ≤ 3/√0.0396 < 15.1, and diam K < √(1 + 15.1²)·w₀ < 100w₀.
9. Otherwise diam K ≤ 2Δ₂ < 100w₀.
10. The last claim follows from (P5). ∎

The numerical steps are checked in `r6_Eprime_full_checks.py`. The largest aspect ratio found numerically is 8.1035, attained by the lens with d = 1.94Δ₂ (REF2 `ref2_lemmaF.py`).

**Step 0 (parameters; G3).** Put ρ₀ := ⌊min(n^{1/3}, Δ₂/400)⌋.
- **(F1) Case ρ₀ = 0.** Then n = 0 or Δ₂ < 400. In the second case Δ < 776. Disjoint disks of radius ½ give n ≤ (2Δ + 1)² < 1553² < 2.42·10⁶ < 135³. So 2|A| ≤ 2n ≤ 270·n^{2/3}, and Def ≥ 0 proves the claim.
- **Otherwise ρ₀ ≥ 1.** For ρ ∈ {ρ₀, …, 2ρ₀ − 1}, the shells Y_ρ := {y ∈ Y : ρ ≤ depth(y) < ρ + 1} are disjoint. Fix ρ with |Y_ρ| ≤ n/ρ₀, and put **h := ρ + ½**. Then

  3/2 ≤ h ≤ 2ρ₀ − ½ < 2n^{1/3}  and  h < Δ₂/200.

- **(F2) Case r_in(K) ≤ h.** By Lemma F and (P4), |A| ≤ per K + 1 ≤ π·300h + 1. So 2|A| ≤ 1200π·n^{1/3} + 2 ≤ 3772·n^{2/3}.
- **(F3) Case per K < 100h (G2 fallback).** Then 2|A| ≤ 200h + 2 ≤ 402·n^{2/3}.

From now on assume r_in(K) > h and per K ≥ 100h.

**Step 1 (shell removal).**
- Put Y_out := {depth < ρ} and Y_in := {depth ≥ ρ + 1}, and H_out := G[Y_out].
- Depth is 1-Lipschitz and the gap between the two sets exceeds 1, so no edge joins Y_out to Y_in.
- Edges at Y_ρ number ≤ 6|Y_ρ|, and Def(G[Y_in]) ≥ 0 (degree ≤ 6).
- Hence Def(G[Y]) ≥ Def(H_out) − 3|Y_ρ| ≥ Def(H_out) − 3n/ρ₀.
- A ⊂ Y_out, since depth 0 < ρ.
- If A = ∅, the claim is trivial.

**Step 2 (the core K′ and the retraction P).**
- Let K′ := {z ∈ K : depth z ≥ h} = ∩_w D(w, Δ₂ − h). This set is compact and convex, and int K′ ≠ ∅ because the incentre has depth r_in > h.
- Every point of the drawing of H_out has depth < ρ + ½ = h: a point on a unit edge is within ½ of an endpoint. So K′ misses the drawing and lies in a single face F₀ of H_out.
- ∂K′ consists of finitely many open smooth arcs (on circles C(w, Δ₂ − h)) and finitely many corners c.
  - At a corner, N_{K′}(c) is the cone between the unit normals ν_i = (c − w_i)/(Δ₂ − h), i = 1, 2, for two centres w₁, w₂ ∈ X. Its angle is ψ_c ∈ (0, π).
  - Normal cones of distinct corners have disjoint interiors, so **Σ_c ψ_c ≤ 2π**.
- Let P be the nearest-point map onto K′, restricted to ∂K. For x ∈ ∂K with P(x) = y, we have x ∈ y + N_{K′}(y).
  - **(offset points)** Suppose y lies on a smooth arc of C(w, Δ₂ − h), with normal ν = (y − w)/(Δ₂ − h). The open disk B(y, h) lies in int K, and |y + hν − w| = Δ₂. So the ray y + ℝ₊ν leaves K exactly at y + hν. Hence **P⁻¹(y) = {y + hν}**. On each smooth arc, P⁻¹ is the radial dilation about w by the factor Δ₂/(Δ₂ − h).
  - **(collapse arcs)** At a corner, Z_c := P⁻¹(c) = ∂K ∩ (c + N(c)). This is a closed arc of ∂K. The Z_c are pairwise disjoint.
- P: ∂K → ∂K′ is a continuous surjection that preserves the cyclic order and has connected fibres. For surjectivity, the ray from y ∈ ∂K′ along an outer normal leaves K at a point x with P(x) = y. Consequently the preimage of an arc is an arc, and the images of the arcs between cyclically consecutive points of a finite set tile ∂K′. Moreover,

  **per K = (Δ₂/(Δ₂ − h))·per K′ + Σ_c len Z_c**,  i.e.  per K′ = (1 − h/Δ₂)(per K − Σ_c len Z_c).   (2.1)

  For every arc α ⊂ ∂K, let col(α) := len(α ∩ ∪_c Z_c). Then

  len P(α) ≥ (1 − h/Δ₂)(len α − col α).   (2.2)

**Step 3 (collapse length; G4).**
- The points p_i := c + hν_i lie in D(c, h) ⊂ K and on C(w_i, Δ₂). So they lie on ∂K, and they are the endpoints of Z_c.
- The convex set K ∩ (c + N(c)) has perimeter 2h + len Z_c.
- K lies in D(w_i, Δ₂), and so in the half-plane behind the tangent line to C(w_i, Δ₂) at p_i. Hence K ∩ (c + N(c)) lies in the kite with vertices c, p₁, p₂ and the intersection point of the two tangent lines. The kite has right angles at p₁ and p₂ and perimeter 2h + 2h·tan(ψ_c/2).
- By (P4), **len Z_c ≤ 2h·tan(ψ_c/2)**.
- Also |w₁ − w₂| = (Δ₂ − h)|ν₁ − ν₂| = 2(Δ₂ − h)·sin(ψ_c/2), and |w₁ − w₂| ≤ 1.94Δ₂. So

  sin(ψ_c/2) ≤ 0.97/(1 − 1/200) = 194/199 < 1.

- Let θ* := arcsin(194/199). Then θ* > 1.343, and tan θ* = 194/√1965 ≤ 3.26·1.343. Since tan x / x is increasing on (0, π/2), tan(ψ_c/2) ≤ 3.26·(ψ_c/2) = 1.63·ψ_c.
- Hence

  **Σ_c len Z_c ≤ 3.26h·Σ_c ψ_c ≤ 3.26·2π·h < 20.49h ≤ 21h.**   (3.1)

- By (2.1) and per K ≤ 2πΔ₂: per K′ ≥ per K − 2πh − 21h. Also per K′ ≥ (199/200)·79h > 2, by (F3) and h ≥ 3/2.

**Step 4 (case (i): F₀ is bounded).**
- In (P2) keep only the outer face and F₀. Then

  Def(H_out) ≥ Σ_{j outer}(3 + |w_j|) + |F₀| − 3.

- Every A-point lies on the outer face: outer normal directions from it leave K immediately. So it lies on the outer walk of its component. Write A_j := A ∩ C_j.
- If |A_j| ≥ 2, then w_j is a closed curve through A_j. So |w_j| ≥ per conv A_j ≥ |A_j|, because consecutive chords are ≥ 1.
- If |A_j| ≤ 1, then 3 + |w_j| ≥ |A_j|.
- ∂F₀ is a union of unit edges separating K′ from ∞, so (P3) gives |F₀| ≥ per K′.
- Together with Step 3 and per K ≥ |A| − 1:

  **Def(H_out) ≥ 2|A| − (21 + 2π)h − 4.**

**Lemma W (winding/degree lemma, case (ii); G5).** Suppose F₀ is the outer face of H_out. Let C_j be a component with |A_j| ≥ 2. List A_j in cyclic order on ∂K, and let α₁, …, α_k (k = |A_j|) be the arcs of ∂K between consecutive points. Then

  |w_j| ≥ 2·Σ_{i≠i*} len P(α_i),  where α_{i*} is any arc with the largest image.

*Proof.*
1. Fix o ∈ int K′. Let γ: [0, L] → ℝ², with L = |w_j|, be the unit-speed closed polygonal curve tracing w_j.
2. **wind(γ, o) = 0.** The outer face of H_out is contained in the outer face of C_j. That face is a connected unbounded open set disjoint from image(γ) ⊂ drawing(C_j), and it contains o (it contains the connected set K′ ∋ o). So o lies in the unbounded component of ℝ²∖image(γ), where the winding number vanishes.
3. **P∘γ has the same winding number.** For x ∉ int K′, the projection inequality (x − Px)·(o − Px) ≤ 0 gives

   (x − o)·(Px − o) ≥ |Px − o|² > 0.

   So x − o and Px − o are never opposite, and the straight-line homotopy (1 − λ)γ + λP∘γ avoids o. Hence wind(P∘γ, o) = 0. Radial projection from o is a homeomorphism ∂K′ → S¹, so P∘γ has degree 0 as a map into ∂K′ ≅ ℝ/(per K′)ℤ.
4. **The lift is closed.** Let E: ℝ → ∂K′ be the arc-length covering. Degree 0 means that the lift β of P∘γ satisfies β(0) = β(L). E preserves curve length and P is 1-Lipschitz, so length(β) = length(P∘γ) ≤ L.
5. **A closed curve in ℝ with image [m, M] has length ≥ 2(M − m).**
6. Each a ∈ A_j is visited by γ, so E([m, M]) is an arc of ∂K′ (or all of ∂K′) containing every P(a), a ∈ A_j.
   - The arcs P(α_i) tile ∂K′ between consecutive P(a) (Step 2).
   - So the complementary open arc of E([m, M]) lies inside a single P(α_i).
   - Hence M − m ≥ Σ_{i≠i*} len P(α_i). ∎

**Step 5 (case (ii): per-component bound).** Suppose F₀ is the outer face. Every bounded face has |f| ≥ 3, so Def(H_out) ≥ Σ_{j outer}(3 + |w_j|).
- For a gap arc α, put e(α) := max(0, 1 − len P(α)).
- If |A_j| ≥ 2, Lemma W gives

  |w_j| ≥ 2Σ_{i≠i*}(1 − e(α_i)) ≥ 2(|A_j| − 1) − 2Σ_i e(α_i).

  So 3 + |w_j| ≥ 2|A_j| − 2Σ_{α∈gaps(j)} e(α).
- If |A_j| ≤ 1, then 3 + |w_j| ≥ 3 ≥ 2|A_j|.
- Summing over components:

  Def(H_out) ≥ 2|A| − 2Σ_α e(α),  summed over all gap arcs of all components.   (5.1)

- **Bound on e(α).** Since len α ≥ 1, (2.2) gives e(α) ≤ (1 − (1 − h/Δ₂)len α)₊ + col(α) ≤ h/Δ₂ + col(α).
- There are at most |A| gap arcs in total. With (P7), |A|·h/Δ₂ ≤ (2πΔ₂ + 1)h/Δ₂ ≤ 2πh + 1/200. Therefore

  Σ_α e(α) ≤ 2πh + 1/200 + Σ_{α: e(α)>0} col(α).   (5.2)

**Step 6 (corner multiplicity; G1 and G2).** Fix a corner c. Let F_c be the set of gap arcs α, over **all** components, with e(α) > 0 and α ∩ Z_c ≠ ∅.

- **Window.** Let B_c := {y ∈ ∂K′ : arc-distance(y, c) < 1}. Since per K′ > 2 (Step 3), B_c is a proper open arc of length ≤ 2. Let U_c := P⁻¹(B_c). This is a proper open arc of ∂K.
  - If α ∈ F_c, then P(α) is an arc of length < 1 containing c = P(Z_c). So P(α) ⊂ B_c, and **α ⊂ U_c**.
  - (G1) U_c consists of the offset preimage of B_c∖{corners} together with the collapse arcs Z_{c′} of **every** corner c′ ∈ B_c, not only Z_c. Hence

    len U_c ≤ 2Δ₂/(Δ₂ − h) + Σ_{c′} len Z_{c′} ≤ 2.02 + 21h ≤ 21h + 3.

    So U_c contains **N ≤ 21h + 4** points of A (P7).
- **Laminarity (G2; only for err-positive arcs).** U_c is a proper arc, so it is linearly ordered. Each α ∈ F_c is an interval [a, a′] ⊂ U_c with endpoints in A ∩ U_c.
  - Two arcs of F_c from the same component have disjoint interiors: they are distinct gaps of one cyclic list.
  - Two arcs from different components C_j, C_k have four distinct endpoints. If they interleaved (a < b < a′ < b′), then a, b, a′, b′ would be in cyclic order on ∂K. By (P6), a path in C_j from a to a′ and a path in C_k from b to b′ would meet. But distinct components are disjoint as point sets (P1).
  - So F_c is a laminar family of distinct intervals with endpoints in an N-point set. Such a family has **at most 2N − 3 ≤ 42h + 5 members**: map an interval to the set of elementary segments it covers, which gives a laminar family of distinct nonempty subsets of an (N − 1)-set.
  - (Without the restriction e > 0 this is false: a component nested inside a gap of another has a "back" gap arc that wraps around ∂K. Such arcs have image length ≥ 1 and are excluded.)
- Hence

  Σ_{α: e>0} col(α) = Σ_c Σ_{α∈F_c} len(α ∩ Z_c) ≤ (42h + 5)·Σ_c len Z_c ≤ 21h(42h + 5).   (6.1)

**Step 7 (assembly).** From (5.1), (5.2) and (6.1), in case (ii):

  Def(H_out) ≥ 2|A| − 1764h² − (210 + 4π)h − 1/100.

Together with case (i) (Step 4), both cases give

  **Def(H_out) ≥ 2|A| − E(h),  E(h) := 1764h² + 223h + 4.**

With h < 2n^{1/3} this is E(h) ≤ 7506·n^{2/3}.

For the shell cost 3n/ρ₀ there are two cases:
- If ρ₀ = ⌊n^{1/3}⌋ ≥ n^{1/3}/2, the cost is ≤ 6n^{2/3}.
- If ρ₀ = ⌊Δ₂/400⌋ ≥ Δ₂/800, the cost is ≤ 2400n/Δ₂.
  - From n ≤ (2Δ + 1)² and Δ ≤ 1.94Δ₂ we get Δ₂ ≥ (√n − 1)/3.88 ≥ √n/7.76 for n ≥ 4.
  - So the cost is ≤ 18624√n ≤ 18624·n^{2/3}. For n < 4 it is ≤ 12.

Altogether Def(G[Y]) ≥ 2|A| − (7506 + 18636)·n^{2/3} ≥ 2|A| − 3·10⁴·n^{2/3}. The fallbacks (F1)–(F3) cost at most 3772·n^{2/3}. ∎

(Step 1's no-edge claim, Step 2's (2.1), and Step 3's bound len Z_c ≤ 2h·tan(ψ_c/2) were also tested at 40 digits on 897 configurations in `r6_refE_parallel.py`. The bound is attained to 6 digits but never exceeded; max Σ len Z_c / h = 16.7. That script needs mpmath. The topological Steps 4–6 are not machine-tested.)

### 5.3 Corollary (τ > 1)

**Theorem (τ > 1).** In the nondegenerate regime with τ > 1:

  min{μ(Δ₂), μ(δ)} ≤ 9n/7 + O(n^{2/3}).

This **matches the global lower bound 9/7**. The known 9/7 constructions (ienjoymath) have t < 1 (Region I), so the theorem says that configurations with τ > 1 cannot beat 9/7. It does not say that 9/7 is attained with τ > 1.

*Proof.*

1. **Reduction.** τ − t = (t² − 1)/(2Δ₂), so τ > 1 ⇔ t > 1. Lemma 3.1(c) gives dist(D, K) ≥ t > 1, and X∖D ⊂ K. So no δ-edge joins D to X∖D, and

   Def(G) = Def(G[D]) + Def(G[X∖D]).

2. **The D-part, on all of D (I-2/3).** The objects of WRITEUP_A2 §3 and §5.2 are defined there for S∩D. They extend verbatim to **every z ∈ D**:
   - fix a diametral partner x_z (|z − x_z| = Δ) and put u_z := (x_z − z)/Δ;
   - **Lemma 3.2(a)** holds for every z ∈ D, since its proof uses only |y − x_z| ≤ Δ;
   - a δ-edge zz′ inside D is **good** if ∠(u_z, u_{z′}) ≤ β and **bad** otherwise, with a := (z′ − z)·u_z and b := (z − z′)·u_{z′};
   - **DD** means both ends in D;
   - the §5.2 DD-lens count uses only that D-points are vertices of P₁ (arc gaps ≥ 1 on ∂P₁) and the lenses D(x_z, Δ) ∩ D(x_{z′}, Δ).

   On a good DD edge, 3.2(a) at both ends gives a, b > 0, and |a + b| ≤ β then gives a, b ∈ (0, β). So the edge is a T-edge. By (T1) there are at most 2 T-neighbours per point, hence ≤ |D| good DD edges. The bad DD edges number < 3.4·10⁴ (or, if per P₁ ≤ 1202, all edges within D number ≤ 6·1203). So

   Def(G[D]) ≥ 2|D| − 3.4·10⁴ ≥ 2|S∩D| − 3.4·10⁴.

3. **The K-part** is Theorem E′: Def(G[X∖D]) ≥ 2|S∖D| − 3·10⁴·n^{2/3}.
4. **LP.** Steps 1–3 give μ(δ) = 3n − Def ≤ 3n − 2s + 3·10⁴·n^{2/3} + 3.4·10⁴. By (VS), μ(Δ₂) ≤ 1.5s + C_V. Since 1.5s is increasing in s and 3n − 2s is decreasing, max_s min(1.5s, 3n − 2s) = 9n/7, attained at s = 6n/7. ∎

Inputs imported from WRITEUP_A2 and not re-proved here: Lemma 3.1, Lemma 3.2(a), (T1), the DD-lens count of §5.2, and (VS) [Ve87].

### 5.4 Referee history of E′

- **REF_E** (first referee): verified, with three constant-level gaps: the window U_c, laminarity, and small n. It also supplied the winding argument.
- **REF2** (second referee, independent): CORRECT WITH GAPS. It raised G1–G6 and I-1..I-5. It found no fatal error, and its adversarial Def − 2|A| sweep (floats) was always positive.
- **Status now:**
  - G1–G5 and I-1 are incorporated in §5.2.
  - G6 (a single complete write-up) is this section.
  - I-2/3 is §5.3, step 2.
  - I-5 is the wording "matches the global lower bound".
  - I-4: `r6_gap_consistency.py` and `ring16.py` import numpy, which the `.venv` lacks, so run them with the system `python3`.
  - The new write-up has not been re-refereed.

### 5.5 What this does not replace

The first-layer "gap lemma" is false as a local statement. There are two exact obstructions:
- L's curved family loses 1 per T-path (`r6_gap_L_family.py`, 60 digits);
- M's pair-gap row loses |A|/4 even with two layers, and its flat limit has density 1.5 (`r6_gap_M_pairgap.py`).

The missing ½ per K-row point is paid by a second, global closed walk: the hole face in case (i), or the non-winding return walk of Lemma W in case (ii). So Theorem G and hypothesis H of R4 §5.2 are superseded.

**General split (all τ).** Def ≥ 2|S| + ½g_D − e(D, X∖D) − O(n^{2/3}). So 9/7 in any regime reduces to **cross-edge accounting**, e(D, X∖D) ≤ ½g_D + o(n), plus the Δ₂-side sharpening in Regions II and III.
- In ienjoymath's construction the K-part always has surplus. Its 9/7 tightness lives entirely in the Region-I D–K exception edges (`r6_gap_consistency.py`, run with the system python3).

## 6. Regions II and III: the |Q| term (branch B2; not refereed)

Report: `scratchpad/R6/A_below/B2_regionII/B2_report.md`. Scripts: `r6_below_lp.py`, `r6_below_strip.py`, `r6_below_resonance.py`, `r6_below_darc.py`.

- **Exact LP.** With e(S) ≤ s + θ|Q′| and μ(Δ₂) ≤ 1.5s − κ|Q′|, the value is max{3c/(2c+1), 1 + θ/(2(θ+κ))}.
- **Region II.** Theorem BC (break count) and Lemma CONS (same-sign unbroken gaps ≤ 7) give e(S) ≤ s + ½|Q′| + C.
  - So Region II is LP-equivalent to Region I: any average weight below 8 beats 4/3 there.
  - The weight-side charging for Region II (B2's Conjecture C2: weight-8 types are only the lattice row and a {K,K,D} fan) is **not proved**.
- **Region III.** Outside the window: e(S) ≤ s + 70/d + C.
  - Inside the window τ = √3/2 + O(1/R), the exact single-centre hexagonal strip has e(S) − s = |Q′|, so the method is stuck at 4/3 there.
  - Lemma DP bounds each strip below 10Δ^{2/3} D-points. Whether Θ(n) strips with R^{1/3} distinct centres can coexist is OPEN.
- **Flagged for a referee:**
  - Region-III distinctness of singleton-gap versus arc-gap breaks;
  - the inequality 2φ < α₁ (float check only; max ratio 0.888);
  - Lemma Z(a) at end vertices.

## 7. Summary and next steps

- **PROVED (refereed):**
  - L ≤ 4/3;
  - 21/16 in Region I and for τ > 1 (the latter superseded);
  - **9n/7 + O(n^{2/3}) for τ > 1, matching the global lower bound 9/7** (given E′);
  - Theorem E′ in all regimes (complete corrected proof in §5.2, not yet re-refereed).
- **PROVED (not refereed):**
  - Region II has no |Q| floor: e(S) ≤ s + ½|Q′| + C;
  - Region III off the resonance window likewise.
- **CONJECTURED:**
  - C1 (average weight ≤ 6 in Region I, hence 9/7 there);
  - the cross-edge inequality e(D, X∖D) ≤ ½g_D + o(n) in Region I, which would give 9/7 in Region I via Theorem E′.
- **OBSTRUCTIONS:**
  - radius-1 charging stops at 7 (21/16);
  - local gap lemmas fail (L, M families);
  - the Region-III resonance strip (4/3 for the e(S) method).
- **Next steps:**
  1. Referee B2, then prove weight ≤ 7 in Region II (to get 21/16 there).
  2. Attack the resonance window with the D-points' partners (Lemma DP).
  3. Prove the Region-I cross-edge inequality by rerunning the Theorem-E′ shell argument on conv X with the D-row as the boundary.

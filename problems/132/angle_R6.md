# Erdős #132 / CDL Problem 1.6: Angle R6, from 15/11 to 4/3

Date: 2026-09-24. Scratch files are in `scratchpad/R6/`. Scripts are `scripts/r6_*.py`.

**Results.**

| statement | regime | status |
|---|---|---|
| **L ≤ 4/3** (Theorem N3: the average R-weight is ≤ 8) | all | PROVED, refereed (REF_N3: correct, cosmetic fixes applied) |
| **min ≤ 21n/16 + C** (Theorem P4: the average R-weight is ≤ 7) | Region I (τ ≤ √3/2 − 2β) and τ > 1 | PROVED, refereed (REF_B1: correct; two passages rewritten, numeric slips fixed) |
| **min ≤ 9n/7 + O(n^{2/3})**, i.e. **sharp** | τ > 1 | PROVED, refereed (REF_E: correct; three constant-level gaps fixed) |
| Theorem E′: Def(G[X∖D]) ≥ 2\|S∖D\| − O(n^{2/3}) | all nondegenerate | PROVED, refereed (REF_E) |
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
  contradicting |w_bot − w_top| ≤ Δ ≤ 1.94R. So L < 1000 and W < 4.04 + 2000 tan(0.5°) < 21.5, and packing gives |X∖D| ≤ 28 662. ∎
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
- K pair at ±30°: h > 0.84, third S is D at ±90°: needs c ≤ 0.05 ≥ h + t − ε ✗.
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
- `scripts/r6_n3_checks.py`: 34 exact rational assertions with rigorous Taylor enclosures. They cover the Lemma T* constants (margin 0.0228 over 1.94), the Lemma BT count with Λ = 464, τ*, the pair tolerances, every excluded case of Lemmas M and H, the Lemma Pin intervals (fan t ∈ [0.746, 0.984], cap t ∈ [0.441, 0.558], disjoint), the receiver windows, the owner-uniqueness distances (|y′ − q| ≤ 0.233), and the LP.
- `scripts/r6_n3_search.py`: a floating-point sanity search of the relaxed slot model. It tested about 3·10⁴ type assignments; every configuration with v ≥ 9 is F6, F5, HF or a cap with the pinned t (found: 21 F6, 61 F5, 180 HF, 32 caps; 0 unclassified).
- `scripts/r6_n3_examples.py`: exact geometry in 60-digit Decimal.
  - (a) R4's fan chain: every y has (6,4). Its lower points have m = 1 and unique owners. t = 0.86598…, and Lemma 3.2(c) holds exactly at p–z.
  - (b) A new cap chain on chords of length √3: y has (6,3), b has m = 0, c has m ≤ 1, and t = 0.49996….
  - Byproduct: adjacent caps (and fans) cannot share lower points, because curvature pushes shared lower points to distance 0.99985 < 1.


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
- **Forwarding targets** may also receive directly, but their load stays ≤ 1, and there are no chains.
- **Numeric slips:**
  - A's receivers are at depth √3;
  - B's receivers are at depth h + √3/2;
  - the K-angle bound is 30° in the τ > 1 slice;
  - B's range includes H = √3/2.
- **Lemma T\*** (fatness step) is repaired with the R4/N3 width bound.
- **The δ₀ budget** is written out line by line: < 5·10⁻⁵ against 10⁻⁴.
- **Script coverage.** B1's scripts test less than the report claimed. The referee's exact cap-lattice test at t = ½ (`r6_refB1_caplattice.py`: 3·10⁴ configurations with up to 6 heavy points) gives max final charge 7.0.

**Limit of the method (exact).** In the exact A-row stack and cap lattice (Q(√3), `r6_below_exact_examples.py`), every radius-1 rule leaves some point at 7, although the true average there is 6. So **21/16 is the limit of radius-1 charging**.

**Conjecture C1.** For each component C of G[𝓡], e(C,S) ≤ b(C) + 3 + Σ_inner(|f| − 3). This is equivalent to average ≤ 6, hence 9/7 in Region I. It is proved for |C| ≤ 2, and a search over clusters with |C| ≤ 7 finds max Φ = 0.

## 5. τ > 1: 9/7 (sharp), via Theorem E′ (branch B-gap plus referee REF_E)

Reports: `scratchpad/R6/B_gap/GAP_report.md` (synthesis), `B_gap/X/X_report.md` (Theorem E, Lemma F) and `scratchpad/R6/REF_E/REF_E_report.md` (referee).

**Theorem (τ > 1).** min{μ(Δ₂), μ(δ)} ≤ 9n/7 + O(n^{2/3}).

*Proof outline.*
1. For τ > 1 we have dist(D, K) ≥ t > 1, so there are no δ-edges between D and X∖D, and Def = Def(G[D]) + Def(G[X∖D]).
2. **D-part.** deg ≤ 3; good D–D edges are T-edges, with at most one per side; bad edges are O(1). So Def(G[D]) ≥ 2|D| − O(1).
3. **K-part: Theorem E′.** Def(G[X∖D]) ≥ 2|S∖D| − O(n^{2/3}), valid in every nondegenerate regime. The proof is global:
   - Remove a shell X_ρ at depth ρ ∈ [ρ₀, 2ρ₀) with |X_ρ| ≤ n/ρ₀, and use Euler's formula with only two faces kept.
   - Case (i): the core sits in a bounded face. Then perimeter monotonicity for the inner parallel body K′ = ∩_w D(w, r − t) applies.
   - Case (ii): the outer boundary walks have winding number 0. Then the lift of their nearest-point projection onto ∂K′ covers an interval twice.
   - Corners of K′ collapse arcs of total length ≤ 21t, with multiplicity O(t).
   - Lemma F: K is fat in the nondegenerate regime (inradius ≥ diam/300).
   - With ρ₀ = n^{1/3} the error is O(n^{2/3}).
4. (VS) gives μ(Δ₂) ≤ 1.5s, so min ≤ max_s min(1.5s, 3n − 2s) = 9n/7.

**Referee (REF_E): VERIFIED with three constant-level gaps, all fixed.**
- The corner window count becomes N ≤ 21t + 4, because nearby corners must be included.
- Laminarity holds only for gap arcs with err > 0, with the fallback "per K ≤ 100t".
- A small-n clause is needed for t/r ≤ 0.005.

The referee also wrote out the flagged winding lemma in full. They checked the parallel-body identity and the collapse bound at 40 digits on 897 configurations (`r6_refE_parallel.py`, needs mpmath); the collapse bound is tight but never exceeded.

**What this does not replace.** The first-layer "gap lemma" itself is false as a local statement. There are two exact obstructions:
- L's curved family loses 1 per T-path (`r6_gap_L_family.py`, 60 digits);
- M's pair-gap row loses |A|/4 even with two layers, and its flat limit has density 1.5 (`r6_gap_M_pairgap.py`).

The missing ½ per K-row point is paid by a second, global closed walk. So Theorem G and hypothesis H of R4 §5.2 are superseded.

**General split (all τ).** Def ≥ 2|S| + ½g_D − e(D, X∖D) − O(n^{2/3}). So 9/7 in any regime reduces to **cross-edge accounting**, e(D, X∖D) ≤ ½g_D + o(n), plus the Δ₂-side sharpening in Regions II and III.
- In ienjoymath's construction the K-part always has surplus. Its 9/7 tightness lives entirely in the Region-I D–K exception edges (`r6_gap_consistency.py`).

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
  - **9/7 for τ > 1, matching the lower bound**;
  - Theorem E′ in all regimes.
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

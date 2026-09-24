# Erdős #132 / CDL Problem 1.6: Angle R6, from 15/11 to 4/3

Date: 2026-09-24. Scratch files are in `scratchpad/R6/`. Scripts are `scripts/r6_*.py`.

**Result: L ≤ 4/3 ≈ 1.3333.** The previous bound was 15/11 ≈ 1.3636 (angle_R4). The lower bound is still 9/7 ≈ 1.2857.

The new ingredient is **Theorem N3**: the R-weight v(y) := deg y + m_y is at most 8 *on average* over 𝓡, up to O(1). Theorem N1 bounds it by 10 pointwise. The proof has two ideas.
1. **Pinning.** Suppose a K-row neighbour p and a D-neighbour z of y differ in height by Δc. Then Lemma 3.2(b)/(c) forces t = Δc + O(ε₀). Each heavy configuration (v ≥ 9) therefore fixes t: fans need t ≈ √3/2 and caps need t ≈ ½.
2. **Private lower neighbours.** Every heavy point has one or two neighbours below it, deep inside K. These have weight ≤ 7 (fans) or ≤ 6 (caps), and no two heavy points share one. Each heavy point passes its excess over 8 to them.

With the |Q| term of angle_R4 this gives 4/3 in every τ-regime. That is exactly the floor of the μ(Δ₂) ≤ 1.5s − 0.5|Q| method in Regions II and III (angle_R4 §1 table), and also the Region-I value for average weight 8.

STATUS: see §6 (referee) and §7 (branches B and "below 4/3").

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


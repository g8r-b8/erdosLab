# REF_D1: hostile referee report on D1r (Theorem G, Corollary 6.1, Theorem 9.1)

Referee REF_D1 of angle R7 (Erdős #132 / CDL Problem 1.6), 2026-09-25.
Object: `angle_R7_reports/D1_report.md` (D1r, STATUS FINAL, §0–§10) and the scripts `r7_D1r_lemmaS.py`, `r7_D1r_global.py`,
`r7_D1_*.py`. Paper numbering follows `paper/paper.aux` (v3): ball polygon = Lemma 2.1, identities = Lemma 2.2, multiplicity =
Lemma 2.5, identity μ(δ) = Lemma 3.3, structure of R = §6.1, big turning = Lemma 6.4, packing in thin K = Lemma 9.2, frame =
Lemma 9.3, DN = Lemma 9.4, fewbad = Lemma 9.5, Region II e(S) = Theorem 11.3.
My scripts: `scripts/r7_refD1_*.py` (all run under `tools/memcap.sh 4000`).

STATUS: IN PROGRESS (sections are appended and committed one at a time)

## 1. Facts 1.1–1.4, Fact 1.2 (Σv = 2E_𝓡), Lemma O, Lemma E

I checked each item against the definitions (paper §2: D = diametral endpoints, S = points with a Δ₂-partner, 𝓡 = X∖S,
K = ∩_{w∈X} D(w, Δ₂); δ = 1 is the minimum distance).

**Fact 1.1.** Correct.
- X∖D ⊂ K: a non-diametral point has all its distances ≤ Δ₂, because X has no distance in (Δ₂, Δ) (Lemma 2.1(a)).
- 𝓡∖D ⊂ int K: a point of X∖D on ∂K lies on some C(w, Δ₂) with w ∈ X (§6.1(b): a point of K at distance < Δ₂ from all
  finitely many centres is interior). Then w is a Δ₂-partner, so the point is in S. Hence no 𝓡-point lies on ∂K.
  (w ≠ x since Δ₂ > 0.) Hostile check passed: **𝓡-points on ∂K are impossible**.
- Points of D∖S = 𝓡∩D are outside K at distance ≥ t (Lemma 2.1(c)). They are handled only through rule (O2) and
  deg ≤ 3; they never need a foot, a depth or a frame.
- S∖D = (X∖D) ∩ ∂K exactly, and every neighbour of every point is in int K (then in 𝓡∖D), in S∖D, or in D.

**Fact 1.2 (Σ_𝓡 v = 2E_𝓡).** Correct: Σ_𝓡 deg = 2e(𝓡) + e(𝓡,S) and Σ_𝓡 m = e(𝓡,S), so the sum is 2(e(𝓡) + e(𝓡,S)) = 2E_𝓡.
Together with paper Lemma 3.3 this gives μ(δ) = e(S) + E_𝓡, which is the form used in §9.

**Fact 1.3 (deg z ≤ 3 on D).** Correct (paper §6.1(a), via Lemma 2.2(a), valid for every point of D, including 𝓡∩D).

**Fact 1.4.** Correct: if a neighbour q of y ∈ 𝓡∖D is not in int K, the segment [y, q] meets ∂K, so h(y) ≤ 1.

**Lemma O.** Correct: four directions pairwise ≥ 60° apart span ≥ 180°, impossible in a half-open arc of length 180°.

**Lemma E.** Correct: own(y) ≤ deg y ≤ 6 on Exc, so E_𝓡 ≤ 3r + 3|Exc| and Σv ≤ 6r + 6|Exc|.

**Verdict on §1: CORRECT.**

## 2. Lemma S (§3) and Lemma 4.0

I re-derived each step from the paper's statements (Lemma 9.3 with G1–G5, Lemma 9.4, Lemma 2.2(b)). The constants were recomputed
by an independent implementation (`r7_refD1_lemmaS.py`, 60-digit mpmath intervals).

**Hypotheses.**
- Lemma 9.3 needs Λ ≥ 100, 1 ≤ ρ ≤ Λ/2, 0 < ε₀ ≤ 1/50, Λ(1 − cos ε₀) < 1, y ∈ 𝓡∖D with h ≤ 1, perimeter ≥ 2Λ, turn(γ^Λ_y) ≤ ε₀ and
  ∂K ∩ D(y, ρ) ⊂ γ^Λ_y.
- D1r's "good" (Λ = 231, ρ = 1, ε₀ = a ≤ 10⁻²) supplies all of these. There is no τ-hypothesis and only Δ₂ ≥ 10⁴ (through Lemma 9.2 in
  the bad-point count). **Correct.**

**Kinds of neighbours.**
- "K: c ∈ [h − ε|sin ψ|, h]" is G2 with −ε|x| ≤ f ≤ 0.
- "Interior: c < h" is G4 with f ≤ 0.
- "Every S-neighbour has |ψ| < 90° + ε₀" is G1 for all q ∉ int K, D-points included. So this holds even when t < ε (Region I, t → 0),
  where a D-neighbour may have c < 0. I checked this case specifically: G1 gives c ≥ h − ε|sin ψ| > −ε|sin ψ| whatever t is.
- **Correct.**

**Step (a).** 𝓡∖D-neighbours in O_n(y) have ψ − α in a half-open semicircle, with |α| ≤ θ ≤ a. So O_n(y) ⊂ [−90° − a, 90° + a],
which is an arc shorter than 240°, and |O_n| ≤ 4. For four points, ψ₄ − ψ₁ ≥ 180° forces the stated windows. **Correct.**

**Step (b).** Two 𝓡∖D extremes would lie in one half-open semicircle, so ψ₄ − ψ₁ < 180°. **Correct.**

**Step (c)** (D1r's self-flagged point).
- h ≤ sin a + ε holds whether e is a K-point (c_e ≥ h − ε) or a D-point (c_e ≥ h + t − ε > h − ε).
- A middle m has c_m ≥ cos(30° + a) > h. So m is neither interior nor K, hence m ∈ D. Since m ∈ O_n(y) and m ∉ 𝓡∖D, m ∈ S∩D.
- If e were a D-point, then e and m are both in D ∩ D(y, 1) with |z_x| ≤ 1 and z_z = c − h ≤ 1. These are exactly Lemma 9.4's
  hypotheses with ξ = ζ = 1 ≤ ρ = 1. So |c_m − c_e| < κ_D|Δx| ≤ 2κ_D, with κ_D = ((Λ−1)ε + 1)/(Λ − 2) (the DN formula with
  ξ = ζ = 1). This contradicts c_m − c_e ≥ L_c > 2κ_D.
- **Correct.**

**Step (d), pinning.**
- u_k = (w_k − k)/Δ₂ is an inward normal at k ∈ γ^Λ_y. By G5 it is (sin β', −cos β') with |β'| ≤ ε₀.
- (z − k)·u_k ≤ 2 sin ε₀ − L_c cos ε₀ < 0, so z is not normal for k (Lemma 2.2(b), valid for every Δ₂-partner). Hence
  |z − w_k| = Δ. Note that the non-normality needs only (z − k)·u_k < 0 < |z − k|²/(2Δ₂).
- Expanding |z − w_k|² = (Δ₂ + t)² gives t = Δc cos β' − Δx sin β' + (d² − t²)/(2Δ₂) exactly. I re-derived this.
- The bounds t ≤ t_hi (which gives t < 1 by (S3)) and t ≥ t_lo follow.
- **Correct.**

**Constants (independent recomputation).**
- D1's parameters (θ = 10⁻³, ε₀ = 10⁻⁶, Δ₂ ≥ 10⁴): t ∈ [0.8644730, 0.8667280] and **κ₁ < 1.5525·10⁻³ < 1.553·10⁻³**. Confirmed.
- At the Theorem-G worst case (a = ε₀ = 10⁻², Λ = 231, Δ₂ = 10⁴), (S1)–(S4), the frame condition and ε₀ ≤ 1/50 all hold rigorously.
- **Lemma 4.0** (κ(θ) ≤ 1.51a + 3.01ε₀ + 2/Δ₂). I re-proved the two one-line estimates by hand. They also hold on a 5 × 4 × 3 grid that
  includes θ ≠ ε₀ (max ratio 0.9962).
- For the §4.1 choice (a = min(κ/8, 10⁻²), ε₀ = a, Δ₂ ≥ max(10⁴, 5/κ)), κ(θ) < κ at κ = 0.08, 0.02, 10⁻³, 10⁻⁵.

**Verdict on Lemma S and Lemma 4.0: CORRECT.**

**Remark R1 (a sharpening, not a fix): θ-independent pinning.**
- When |O_n(y)| = 4, both middles z₂ ≈ −30° and z₃ ≈ +30° are S∩D, and (S1) makes each of them an exception for the same K-extreme k
  and the same Δ₂-partner w_k.
- Subtracting the two exact identities gives (z₃ − z₂)·u_k = (d₃² − d₂²)/(2Δ₂). So |c₃ − c₂| ≤ ρ := (2 sin ε₀ + 2/Δ₂)/cos ε₀.
- Since |c₃ − c₂| = 2|sin s| sin g ≥ |sin s| (with s = (ψ₂ + ψ₃)/2 and g = (ψ₃ − ψ₂)/2 ≥ 30°), we get |s| ≤ σ := arcsin ρ.
- The K-extreme has |ψ| < 90° + ε₀, and this forces g − 30° < ε₀ + σ.
- Hence t ∈ [(cos(30° + 2σ + ε₀) − sin σ) cos ε₀ − 2 sin ε₀ − 1/(2Δ₂), cos(30° − σ) + tan ε₀ + 2 sin ε₀ + 2/Δ₂]. This window κ'(ε₀, Δ₂) does
  **not depend on θ**.
- Rigorous values: κ'(10⁻⁶, 10⁴) < 4.57·10⁻⁴ (against D1r's 1.55·10⁻³ at θ = 10⁻³), κ'(10⁻⁶, 10⁸) < 6.6·10⁻⁶, and κ' ≤ 7ε₀ + 5/Δ₂ on all
  samples.
- Consequence: in §4.1 the Gauss sector width θ_s can be a fixed absolute constant (e.g. θ_s ≤ 2·10⁻²); only ε₀ and Δ₂* need to depend
  on κ. The seam cost O(M²/θ_s) then no longer grows as κ → 0.
- This does not change any statement. It only removes a factor 1/κ from C(η, κ).

## 3. Global ownership (§4): rules O1–O4, Exc, Lemmas 4.3–4.6, Theorem G assembly (§5)

**Every edge incident to 𝓡 is owned exactly once. Correct, with one cosmetic fix.**
- Take an edge with an 𝓡-end. Its other end is in S, in 𝓡∩D or in 𝓡∖D.
- (O3) and (O4) partition the 𝓡∖D–𝓡∖D edges. For (O3), exactly one of ±w is n-upward.
- **Fix F1 (cosmetic).** (O1) and (O2) *overlap* on edges z–q with z ∈ 𝓡∩D and q ∈ S (z is then "its only 𝓡-end" and also "an 𝓡∩D end").
  Both rules name the same owner z, so ownership is well defined. But the sentence "the cases are disjoint" is false as written.
  Replacement: "(O1) Spoke: y ∈ 𝓡∖D, q ∈ S, owned by y." Then every edge with an end in 𝓡∩D falls under (O2), and the four cases are
  disjoint.
- My exact-adjacency implementation of O1–O4 (`r7_refD1_global.py`, Parts B and C) checks Σ own = E_𝓡 on every run. It also checks
  2E_𝓡 = Σ_𝓡 v on the ienjoymath construction, where 𝓡∩D and S∩D are non-empty.

**Proposition 4.2.**
- (a) Correct.
- (b) Correct. Fact 1.4 leaves only 𝓡∖D-neighbours. Points of X in int K are in 𝓡∖D, since S∖D ⊂ ∂K and D ∩ K = ∅. y ∉ Exc_cr puts
  all of them in y's zone, and Lemma O applies. No frame condition is needed at h > 1, whether the point is shallow (sector frame)
  or deep (frame e).
- (c) Correct. h ≤ 1 ≤ T makes y shallow. The sector rule gives ∠(n_{j(y)}, ν(y)) ≤ θ_s/2 exactly (ν ∈ [φ₀ + jθ_s, φ₀ + (j+1)θ_s)
  and n_j is the midpoint). ν(y) = n₀(y) for the same chosen nearest point. own(y) = |O_n(y)|, because spokes (including those to
  S∩D) are owned by y, (O2)-edges are not, and (O3)-edges are owned iff upward.

**Smooth feet.** The inscribed disc D(y, h(y)) ⊂ K touches ∂K at p₀(y), so every supporting line of K at p₀ supports the disc there.
Hence the outer normal at p₀ is unique. Correct. (This is what makes one-point arcs γ_{yu} have turning 0, and it is used in Lemma 4.5(1).)
A point y on the medial axis has several nearest points. D1r "fixes" one, and all later uses refer to that choice, so this is consistent.

**Lemma 4.3 (N_ng).** Correct. There are three cases.
- (i) Perimeter ≤ 462 ⇒ diam K ≤ 231 ⇒ |X∖D| ≤ 463².
- (ii) The §9.1 variant of Lemma 6.4 with Λ = 231 gives < 2π·465²/ε₀. I checked the variant's count (2Λ + 3)² in the paper.
- (iii) The foot-to-b distance is ≤ h + 1 ≤ 2, and Λ = 231 > 115·2. Lemma 9.2 with ℓ = 2 ≤ Δ₂/100 gives < 501·11.8·4/π < 7528.

None of the cases uses v. D1 flag 2 is resolved as D1r says.

**Lemma 4.4 (random T).** Correct.
- A deep/shallow edge needs h(y) ≤ T < h(u). This has probability ≤ |h(u) − h(y)|/M ≤ 1/M, because h = dist(·, ℝ²∖int K) is
  1-Lipschitz.
- e(𝓡∖D) ≤ 3|𝓡∖D| ≤ 3r.
- D1r's remark on why a *fixed* T fails (all of 𝓡 in a band around depth T) is right. I confirm it numerically: in Part B, runs
  with T < w put ≈ 2·10⁴–9·10⁴ points into Exc_cr, while runs with T > w have ≈ 380–1000. The randomisation is essential and it is
  correctly done.

**Lemma 4.5 (seams).** Correct.
- (1) |p₀(y) − p₀(u)| ≤ h(y) + 1 + h(u) ≤ 2T + 1 ≤ 2M + 3 = ℓ. If K is not ℓ-thin, the shorter arc γ_{yu} has length ≤ Λ₁.
  N(γ_{yu}) is a connected arc of S¹ (the union of the normal cones along a connected boundary arc). It contains the unique normals
  ν(y) and ν(u), so ∠(ν(y), ν(u)) ≤ turn(γ_{yu}). This also holds trivially if the turning is ≥ π.
- (2) Every edge whose arc contains b has *both* ends within Λ₁ + T of b (chord ≤ arc, plus depth ≤ T). There are ≤ (2Λ₁ + 2T + 1)²
  such points and ≤ 6 edges at each, so the multiplicity is ≤ M_seam. Paper Lemma 2.5 applies verbatim. Its proof (a.e. direction ν
  has a unique boundary point y_ν, and ν ∈ N(γ_i) ⇔ y_ν ∈ γ_i) covers closed arcs, one-point arcs and arcs through corners of K.
- (3) With a uniformly random translate of θ_sℤ, the expected number of cuts in an arc of length α is exactly α/θ_s. Markov then
  bounds the probability of a crossing.
- **Corners of K** are handled correctly. A corner is never a foot, but the arcs γ_{yu} may pass through it. Its exterior angle is part
  of the total turning 2π, which the multiplicity lemma charges at most M_seam times. So the corners cost O(M_seam/θ_s) in total,
  independent of their number.

**Lemma 4.6 (ℓ-thin).** Correct. The two feet (or any p, b in the definition) lie on ∂K with |pb| ≤ ℓ = 2M + 3 ≥ 1 and arcs > Λ₁ = 116ℓ
> 115ℓ, and ℓ ≤ Δ₂/100 is part of Δ₂ ≥ Δ₂*. Lemma 9.2's proof is uniform in 1 ≤ ℓ ≤ Δ₂/100: its numeric step uses
w₀/Δ₂ ≤ 1.0001ℓ/Δ₂ ≤ 0.0101 < 0.011. D1 flag 1 is resolved.

**Theorem G assembly (§5).** Correct.
- For each fixed (φ₀, T), Σv = 2E_𝓡 ≤ 6r + 6|Exc(φ₀, T)|, and E_𝓡 does not depend on (φ₀, T).
- Joint averaging gives E|Exc_cr| ≤ 2(3r/M) + 2(2πM_seam/θ_s). Lemma 4.4 holds for every φ₀ and Lemma 4.5 for every T, so the joint
  mean is at most the sum. Choosing a pair at or below the mean is legitimate.
- 6·2·3r/M = 36r/M ≤ ηr, since M ≥ 36/η.
- Small Δ₂: n ≤ (2Δ + 1)² ≤ (3.88Δ₂* + 1)², and Σv ≤ 12r ≤ 6r + 6n.
- I recomputed C(0.1, 0.02) independently:
  - a = 1/400, M = 360, ℓ = 723, Λ₁ = 83 868, N_s = 1257;
  - 24πM_seam/θ_s ≈ 2.568·10¹⁵ (dominant), 6N_ng ≈ 3.3·10⁹, 6N_thin ≈ 5.4·10⁹, 6(3.88Δ₂* + 1)² ≈ 4.7·10¹¹ (Δ₂* = 72 300);
  - so C(0.1, 0.02) < 2.6·10¹⁵. **Confirmed.**
- **Fix F2 (cosmetic).** Theorem G is stated for η ∈ (0,1], but §9 applies it with η' = 14η/3, which exceeds 1 when η > 3/14. Either
  allow any η > 0 in Theorem G (M = ⌈36/η⌉ ≥ 1 still works) or replace η' by min(η', 1).

**Remark 5.2 (O(r^{2/3})).** Correct. With M = ⌈r^{1/3}⌉:
- interface 36r^{2/3};
- seams O_κ(M²);
- N_thin = O(M²);
- small Δ₂ ⇒ n = O_κ(1) + O(r^{2/3}), so r = O_κ(1) there.

**Verdict on §4–§5: CORRECT (fixes F1, F2 cosmetic).**

# REF_D1: hostile referee report on D1r (Theorem G, Corollary 6.1, Theorem 9.1)

Referee REF_D1 of angle R7 (Erdős #132 / CDL Problem 1.6), 2026-09-25.
Object: `angle_R7_reports/D1_report.md` (D1r, STATUS FINAL, §0–§10) and the scripts `r7_D1r_lemmaS.py`, `r7_D1r_global.py`,
`r7_D1_*.py`. Paper numbering follows `paper/paper.aux` (v3): ball polygon = Lemma 2.1, identities = Lemma 2.2, multiplicity =
Lemma 2.5, identity μ(δ) = Lemma 3.3, structure of R = §6.1, big turning = Lemma 6.4, packing in thin K = Lemma 9.2, frame =
Lemma 9.3, DN = Lemma 9.4, fewbad = Lemma 9.5, Region II e(S) = Theorem 11.3.
My scripts: `scripts/r7_refD1_*.py` (all run under `tools/memcap.sh 4000`).

STATUS: FINAL (verdict: CORRECT WITH FIXES, all cosmetic; see §8)

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

## 4. The sanity check: can a curved K force E_𝓡 − 3r linear in r?

**The coordinator's worry.** If X is thin (r ≍ R := Δ₂, e.g. 𝓡 is a band of bounded width along ∂K), then a boundary term of size
Θ(perimeter) = Θ(R) would be Θ(r), not o(r). Lattice rows meet a curved ∂K at every angle, so one might expect a "staircase"
excess per unit length.

**Answer: no, and D1r's proof has no perimeter term.** The only geometry-dependent costs in Theorem G are:
- N_ng, which uses only the total turning 2π;
- the seams, which cost O(M²/θ_s) by the multiplicity lemma (again only the total turning 2π);
- the interface, ≤ 3r/M, proportional to r and not to the perimeter.

Nothing is charged per unit length of ∂K. A point near ∂K owns ≤ 3 edges in *its own* frame whatever the angle between the lattice
and ∂K: Theorem F and Lemma S are local, and the staircase is invisible to them. The frames themselves change only at the O(1/θ_s)
sector cuts.

**Exact bookkeeping identity (toy).** Suppose 𝓡 ∪ S ∪ {absent sites} is a full triangular lattice near 𝓡. Then deg y = 6 − #absent
neighbours, and so

  E_𝓡 − 3r = ½·(e(𝓡, S) − e(𝓡, absent)),

that is, half the difference between the "outer" and "inner" lattice boundary lengths of 𝓡. In a real X, S∖D ⊂ ∂K and D lies
outside K, so **S only ever touches 𝓡 from the outer side**. A band of 𝓡 along ∂K therefore has absent sites on its inner side,
whose count is the parallel curve's length. The difference is a *turning × depth* term (6 per row, the lattice analogue of
"L(outer) − L(inner) = 2π·depth"), not a length term. The one way to put S on both sides of a thin band is a thin K, and that is
the ℓ-thin case, where |X∖D| = O(ℓ²) (Lemma 9.2).

**Tests** (`r7_refD1_global.py` Part B: K = disc of radius R, randomly rotated and shifted lattice with exact adjacency, 𝓡 = the
lattice points at depth 0 < h < w, so r ≈ 7.26·R·w grows linearly in R).
- **Model U** (deliberately unphysical: S = lattice points just outside ∂K at any height):

  | w | R = 100 | 400 | 1600 | 6400 | r at R = 6400 |
  |---|---|---|---|---|---|
  | 1.0 | 7 | 8 | 6 | 6 | 46 344 |
  | 2.5 | 18 | 17 | 17 | 18 | 116 069 |
  | 12 | 81 | 84 | 84 | – | (138 789 at R = 1600) |

  E_𝓡 − 3r ≈ 6 × (number of lattice rows in the band), **independent of R**. This is exactly the flat-hexagon band law "6j"
  (Part A: E_𝓡 − 3r = 6j for a band of j rows, and 6k − 3 for the full hexagon, exact). So even with unphysical S the excess is
  O(width), not O(R).

  The rare own = 4 points (0–6 per configuration) all have an S-neighbour at a height in (0, t) above ∂K. No real X has such a
  point: it is neither on ∂K (a K-point) nor at distance ≥ t from K (a D-point).
- **Model P** (physical heights: S at height ≥ t above ∂K, the layer 0 < height < t emptied; t = 0.5 and 0.1): E_𝓡 − 3r is
  *negative*, about −(0.1 to 1.3)·r. There are **no own = 4 points**, and E_𝓡 − 3r ≤ 3|Exc_cr| holds on every run.

In both models, D1r's rule with 2° Gauss sectors gives, off Exc: exact-once ownership, own ≤ 3 at h > 1, and own ≤ 4 at h ≤ 1.
When T > w (all points shallow), |Exc_cr| stays at 370–390 (w = 1) and about 970–1260 (w = 2.5), independent of R. This is the seam
count, O(w/θ_s).

**D1r's quantitative explanation (§4.5) is correct.**
- The hexagon excess 6k − 3 = Θ(√r) is paid by the interface term 3r/M. The level hexagon has Θ(k) edges, and the random T spreads
  them over r/M.
- The corners cost O(M²/θ_s), since the turning is 2π in total.
- I add the explicit reason why the thin-band case r ≍ R is harmless: the excess is (turning) × (depth), and the depth of a thin
  band is O(1).

One precision for D1r's §4.5 table: in the toy of §4.6, "the true toy excess grows like the perimeter (≍ √r)". That is for K filled
to depth ≍ w ≍ √r. For thin bands the excess is O(w) = O(1) (above), which is the relevant case for r ≍ R.

**Verdict on the sanity check: no counterexample. The coordinator's scenario (curved K, r ≍ R) costs O(1), not Θ(r).**

## 5. Corollary 6.1 and the cost table (F6, F5, bare fan, HF1, HF2, cap)

**Corollary 6.1(1).** Correct.
- Off Exc, h > 1 gives own ≤ 3, 𝓡∩D gives own ≤ 3, and h ≤ 1 gives own ≤ 4.
- own = 4 forces the Lemma S(2) pattern, with S∩D-neighbours within a₀ of ±30° and a K-neighbour within a₀ of ±90°. Such a y is good
  and so lies in F*. Hence own ≤ 3 + 1[y ∈ F*₄], and Σv ≤ 6r + 2|F*₄| + 6|Exc|.
- Exc is bounded exactly as in Theorem G, with Δ₂* not containing 5/κ.

**Corollary 6.1(2).** Correct. Step (d) of Lemma S uses only one K-neighbour k within a₀ of ±90° (so c(k) ∈ (−ε, sin a₀]), one
S∩D-neighbour z within a₀ of ±30°, and the goodness of y (so that k ∈ γ^Λ_y and G5 holds). Remark R1 applies here too: both S∩D-neighbours
are pinned, so F* ≠ ∅ even forces |t − √3/2| ≤ κ'(a₀, Δ₂) = O(a₀ + 1/Δ₂).

**Corollary 6.1(3).** Correct. Each y ∈ F* has two distinct S∩D-neighbours, and each z ∈ D has degree ≤ 3 (Fact 1.3).

**Fix F3 (cosmetic, §0 and §6).** "At every point of F*, own(y) ≤ 4" should read "at every point of F*∖Exc". A point of F* ∩ Exc
(for instance an endpoint of a crossing edge) can own up to deg y ≤ 6. It is charged through 6|Exc|, so no inequality changes.

**Cost table.** I checked each row against paper Lemma 9.7 (at ε₀ = 1/50) and against rules O1–O3. The cost of a non-exceptional point
is 2(own − 3), because Σv = 2Σ own.
- **F6, F5, bare fan: cost 2.** Correct. The interior neighbours near ±150° (F6) or in (150° − ε₀, 210° + ε₀) (F5) have
  cos(ψ − α) < 0 for |α| ≤ a, so they own their edges to y.
- **HF2 and relatives: cost 0 or 2.** Correct. The neighbour u near −90° is not in S (m = 3), and it has c ≤ sin(a + 2.81°) < h + t − ε,
  so it is in 𝓡∖D. It is owned by y iff it is n-upward. Both cases occur, and in an HF2–HF2 pair (paper Lemma 9.10(b)) exactly one
  end owns yy'.
- **HF1: cost 0.** Correct. The neighbour near −30° has c > h and is not in S, so it is in 𝓡∩D, and (O2) gives that edge to the D-end.
- **Cap: cost 0.** Correct (own = the 3 S-neighbours). Caps pin t ≈ ½ anyway.

D1r's own caveat (§10.7) is accurate. The type names transfer Lemma 9.7's classification to tolerance a descriptively. **No
inequality depends on the table**, since Corollary 6.1(1) uses only Lemma S(2).

**Fan-zone value.** 2c ≤ 6 + 2φ + η with φ = |F*₄|/r, and Theorem W's LP gives max{3(3+φ)/(7+2φ), 9/7} = 3(3+φ)/(7+2φ). This is
exact in `r7_refD1_lp.py`: it is increasing in φ, with value 9/7 at φ = 0, 13/10 at ¼, 21/16 at ½ and 4/3 at 1. **Correct.**
(This is a bound in terms of φ. Nothing is claimed about the size of φ, and D1r says so.)

## 6. LP consequences (§9), regime by regime

Exact check with Fractions (`r7_refD1_lp.py`). The weights are 4/7 on μ(Δ₂) ≤ (3/2)s − ½p and 3/7 on μ(δ) = e(S) + E_𝓡 ≤ e(S) + (3 + η/2)r + C.
In every row the coefficient of s is 9/7 and that of r is 9/7 + 3η/14. The p-coefficients are:

| regime | e(S) bound used | p-coefficient | value | status of the e(S) input |
|---|---|---|---|---|
| Region I (τ ≤ √3/2 − 2β) | s + C_bad (paper §5.1; I checked the 58.35° window argument) | −2/7 | 9/7 + 3η/14 | paper v3, formalised chain |
| τ > 1 | s + C_bad (paper §5.2: no rungs, since t > 1; D1r writes "§5.2", correctly) | −2/7 | 9/7 + 3η/14 | paper v3 |
| Region II | s + ½p + C_bad + 87 (paper Theorem 11.3) | −1/14 | 9/7 + 3η/14 | one referee pass (A2) |
| Region III off the fan zone | s + (2/3)\|Q′\| + C (Theorem W) with μ(Δ₂) ≤ (3/2)s − ½\|Q′\| + C_V | 0 | 9/7 + 3η/14 | refereed once (REF_C), not in the paper |

- The automatic fan-zone exclusion for κ ≤ 0.019 is correct.
  - Region I: t ≤ τ + 1/(2Δ₂) ≤ √3/2 − 0.02 + 5·10⁻⁵.
  - Region II: t ≥ τ ≥ √3/2 + 0.03 when t ≤ 1.
  - τ > 1 ⇔ t > 1.
  - The fan zone |t − √3/2| < 0.019 lies inside Region III, since τ = t + O(1/Δ₂).
- Theorem 9.1's η' = 14η/3 scaling is exact. See fix F2 for η > 3/14.
- **Verdict: CORRECT**, conditional exactly as D1r states. The Region III row inherits Theorem W's status. If W failed, only that row
  would drop, to max{3c/(2c+1), 4/3} = 4/3.

## 7. Consistency with ienjoymath's 9/7 construction

- `r7_D1_ring.py` (rerun) gives Σ_𝓡 v ≤ 6r with max v = 6, min/n = 1.183, 1.200, 1.240, 1.248 for n = 60, 120, 250, 400, increasing
  towards 9/7 from below, and t/δ = 0.131 → 0.019 (Region I).
- My Part C applies D1r's rule **verbatim with the real K** (h(y) = min_w (Δ₂ − |y − w|), which is exact for a ball polygon; ν from the
  minimising centre). For n = 120, 250, 400, 700 it gives Σv = 2E_𝓡, **own ≤ 3 at every 𝓡-point**, and |Exc_cr| = 0 (the patch is deep
  and uses the single deep frame).
- **Theorem 9.1 is consistent with the construction.** The bound 9/7 + η is ≥ 9/7 and is approached by the construction, so it is
  tight and not violated. Theorem G's 6r is attained up to o(r) by the same construction: r ≈ n/7 and E_𝓡 ≈ 3r, as the LP equality
  case requires (s = 6n/7, μ(Δ₂) ≈ (3/2)s, e(S) ≈ s).
- (A first version of my Part C reported own = 4. That was a floating-point tie artefact, ±10⁻¹⁶ on horizontal edges, which made both
  horizontal neighbours "upward". A 10⁻⁹ tie tolerance removed it. It is not a mathematical issue.)

## 8. Verdict

**CORRECT WITH FIXES (all cosmetic; no statement changes).**

Theorem G, Corollary 6.1 and Theorem 9.1 (conditional on Theorem W in Region III, exactly as D1r states) stand. I found no
mathematical error. The fan-zone value 3(3+φ)/(7+2φ) is correct as a bound in terms of φ = |F*₄|/r.

**Replacement text.**
- **F1 (§4.2, rule O1).** Replace "(O1) *Spoke:* y ∈ 𝓡, q ∈ S. Owned by y, its only 𝓡-end." by "(O1) *Spoke:* y ∈ 𝓡∖D, q ∈ S. Owned by y."
  Rule (O2) then covers every edge with an end in 𝓡∩D, including 𝓡∩D–S edges, and the four cases are disjoint as claimed.
- **F2 (§4.1/§5, range of η).** Replace "For every η ∈ (0,1]" by "For every η > 0", with M := ⌈36/η⌉ ≥ 1 (nothing else uses η ≤ 1).
  Alternatively, in §9 use η' := min(14η/3, 1).
- **F3 (§0 and §6).** Replace "At every point of F*, own(y) ≤ 4; elsewhere off Exc, own ≤ 3" by "At every point of F*∖Exc, own(y) ≤ 4;
  at every other point off Exc, own(y) ≤ 3."
- **F4 (§4.6, wording).** After "The true toy excess Σv − 6r also grows like the perimeter (≍ √r)", add: "for K filled to depth ≍ √r.
  For a band of fixed width w along ∂K, E_𝓡 − 3r ≈ 6·(number of rows) = O(w), independent of the perimeter (REF_D1 §4)."

**Optional improvements (not needed).**
- **R1.** The pinning window is θ-independent: κ' ≤ 7ε₀ + 5/Δ₂ on all samples (§2). So θ_s can be an absolute constant, and C(η, κ)
  loses a factor 1/κ in the seam term.
- **R2.** The toy identity E_𝓡 − 3r = ½(e(𝓡,S) − e(𝓡, absent)), together with "S touches 𝓡 only from outside K", explains the
  corner/turning law directly (§4).

**D1r's self-critique list (§10), item by item.**
- Item 2 (Lemma S step (c)): checked, correct.
- Item 3 (normal image, smooth feet): correct.
- Item 4 (multiplicity): correct.
- Item 5 (ℓ-thin): correct.
- Item 6 (random T): correct and essential.
- Item 7 (table): descriptive only; accounting rigorous.
- Item 8 (Remark 5.2): correct.
- Item 9 (inherited statuses): accurately stated.
- Item 10 (non-uniformity in κ): true. R1 removes the θ part of it, but N_ng = O(1/ε₀) and Δ₂* ≥ 5/κ remain. Nothing uniform on the
  fan zone follows.
- Item 11 (tests): the tests are evidence; my additional tests are listed below.

**What I did not re-referee.** I took these as given, in the form in which they are stated:
- the paper lemmas cited, which are part of the refereed N3 chain: 2.1, 2.2, 2.5, 3.1–3.3, §6.1, 6.4, 9.2–9.5;
- Theorem 11.3 (Region II, one referee pass);
- Theorem W (Region III, REF_C).

For the lemmas that carry the load, I re-checked the statements' hypotheses against their use (§2, §3).

**Scripts** (all pass under `tools/memcap.sh 4000`):
- `r7_refD1_lemmaS.py` (`.venv/bin/python`): 60-digit interval re-implementation of κ(θ), (S1)–(S4), Lemma 4.0, and the R1 window κ'.
- `r7_refD1_global.py` (`python3`, numpy for Part C):
  - A: exact hexagon/band counts;
  - B: curved-band adversary, models U and P, R up to 6400, r up to 1.4·10⁵;
  - C: D1r's rule with the real K on ienjoymath's construction.
- `r7_refD1_lp.py` (`.venv/bin/python`): exact LP certificates, the fan-zone value and the η' scaling.
- D1r's `r7_D1r_lemmaS.py`, `r7_D1r_global.py` and `r7_D1_ring.py` were rerun and pass.

STATUS: FINAL

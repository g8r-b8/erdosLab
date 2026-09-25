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

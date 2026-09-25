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

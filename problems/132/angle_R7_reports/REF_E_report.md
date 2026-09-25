# REF_E: hostile referee report on branch E (R7) — fan window, Theorem G′, Proposition F, Theorem E (81/61)

Referee REF_E of angle R7 (Erdős #132 / CDL Problem 1.6), 2026-09-25. Written incrementally; committed per section.
Object: `angle_R7_reports/E_report.md` (STATUS FINAL) and `scripts/r7_E_{window,structure,lp,reuleaux}.py`.
Inputs read: angle_R7.md (all), D1_report.md (+ Errata), REF_D1_report.md, paper/paper.tex v3 (§2 setup, Lemma 2.2, Lemma VS/VSQ,
Lemma 9.3 frame incl. (G5), Lemma 9.4 DN, Lemma pin, Remark rem:sharp), WRITEUP_A2.md (Lemma 4.2), scripts r7_C_*, r7_refC_*.
New scripts: `scripts/r7_refE7_*.py` (run as `tools/memcap.sh 4000 .venv/bin/python problems/132/scripts/<name>`).

E's own scripts rerun under memcap: `r7_E_window.py`, `r7_E_lp.py`, `r7_E_structure.py` all pass (outputs as in E §5.5).

## 0. Plan of the audit

1. Definitions: is Q in VSQ, Q′ in Theorem W, and Q_K in Proposition F one consistent family? (flag 4)
2. Lemma EW and its applicability to every F* point (flags 1, 5), exactly.
3. Theorem G′ uniformity (flag 2).
4. Lemma U, C2(a) (flag 3), Proposition F.
5. The LP: exact vertex enumeration and certificates; what survives if an input fails.
6. X1, C2(b), ORD (flag 6), §4.
7. Consistency with ienjoymath (9/7). Verdict.

## 1. The three "Q" sets are consistent (flag 4) — CORRECT, one wording fix

- **Paper VSQ (Lemma 3.2, `lem:VSQ`)**: Q is defined in paper §2 as "the set of points [of S] with exactly one partner at distance
  Δ₂", i.e. **all** Δ₂-degree-1 points of S, p = |Q|, and μ(Δ₂) ≤ p + (3/2)(s − p) = (3/2)s − ½p (no additive constant). Paper
  line 1104 says this explicitly ("Q is, by definition, the set of all points of S of Δ₂-degree exactly 1").
- **WRITEUP_A2 Lemma 4.2**: P₁ := points of S of Δ₂-degree exactly 1 — the same set as the paper's Q.
- **Theorem W's Q′** (branch C; report lost, summary in angle_R7 §4 and the docstring of `r7_C_q.py`): rung K-ends shown to have
  Δ₂-degree 1 by Lemma Q, "unless its normal cone is wider than 0.44 (≤ 15 points)". So **Q′ ⊆ Q up to O(1) points**, and
  e(S) ≤ s + θ|Q′| + C ≤ s + θ|Q| + C′. Theorem W's own LP (value max{3c/(2c+1), 9/7}) already needs this, via
  μ(Δ₂) ≤ (3/2)s − ½|Q′| + C.
- **E's Q_K** (K-extremes of F* points): Lemma U puts each in Q (checked in §3 below).

So VSQ is applied once, to the full set Q ⊇ Q′ ∪ Q_K, and the LP variables p = |Q| ≥ q′ = |Q′| and F ≤ 2p are consistent. The LP
allows complete overlap Q′ = Q_K = Q, so it is conservative. **F*₄ ⊆ F* ⊆ 𝓡∖D** (D1r §6 definition), r = |𝓡|, and
μ(δ) = e(S) + ½Σ_𝓡 v ≤ e(S) + 3r + |F*₄| + ηr/2 + C is exactly Corollary 6.1(1) inserted in paper Lemma 3.3. Consistent.

*Fix E1 (wording).* In E §3.2, write "e(S) ≤ s + θ|Q′| + C with |Q′ ∖ Q| = O(1) (Lemma Q's wide-cone exceptions)", or simply use
e(S) ≤ s + θp + C, which removes the q′ variable; the table column "p = |Q′|" should read "p = |Q| (= |Q′| at the optimum)".

## 2. Lemma EW and its hypotheses at every F* point (flags 1, 5) — CORRECT

**EW proof, line by line.** Law of cosines in the w-frame gives cos ψ_z, cos ψ_k exactly; C(y,1) ∩ C(w,Δ) has at most two points,
mirror images in the line wy, so z₂ ≠ z₃ forces them to be ±ψ_z. Δ > R gives ψ_z < ψ_k. |z₂z₃| = 2 sin ψ_z ≥ 1 with
ψ_z < ψ_k − 60° ≤ 120° gives ψ_z ≥ 30°; |z₃k| = 2 sin((ψ_k − ψ_z)/2) ≥ 1 gives ψ_k − ψ_z ≥ 60° (the angle is in [0, π]). Since cos is
decreasing on [0, π], Δ² = ρ² + 1 + 2ρ cos ψ_z lies in [L(ρ), U(ρ)]. ψ_k ≥ 90° ⇔ ρ ≥ ρ₀ = √(R² − 1). L is increasing (sympy identity in
`r7_E_window.py`, re-verified), L(ρ₀) = U(ρ₀) = R² + √3ρ₀, U(ρ) < U(R) because ρ < R. Translating Δ² = R² + 2Rτ + 1 (identity checked:
R² + 2Rτ + 1 = (R + t)² with τ = t − (1 − t²)/(2R)) gives τ ∈ [(√3ρ₀ − 1)/(2R), √3/2) and (√3ρ₀ − 1)/(2R) = cos(π/6 + arcsin(1/R)),
i.e. 0 < G ≤ 2. **Correct.** Only exact distance relations enter; no tolerance.

**Hypotheses at an arbitrary y ∈ F*(a₀)** (not only exact fans):
- *k*: F* gives a K-neighbour k (so k ∈ S∖D ⊂ ∂K, Fact 1.1) within a₀ of ±90° in y's frame; c(k) ∈ [h − ε, sin a₀] ⊂ [−ε, sin a₀].
- *Both middles are exceptions for k, for every Δ₂-partner w of k.* Paper Lemma 2.2(b) holds for every Δ₂-partner w of k (the remark after
  its proof: "(b), (c) hold for every Δ₂-partner w of p in place of w_p"). Paper Lemma 9.3 **(G5)** reads "*every* outer normal of K at a
  point of γ^Λ_y makes an angle at most ε₀ with n₀", and k ∈ ∂K ∩ D(y,1) ⊂ γ^Λ_y (goodness). For any partner w, K ⊆ D(w, R) and
  k ∈ C(w, R), so −(w − k)/R is an outer normal at k. Hence Lemma S(d) applies to each middle z ∈ {z₂, z₃} separately (each has
  c(z) ≥ cos(30° + a₀); |Δx| ≤ 2; (S1): 2 sin ε₀ − L_c cos ε₀ < 0), giving (z − k)·(w − k) < 0, so z is not normal and |z − w| = Δ.
  (E's list "c(m) ≥ cos(30°+a₀), |Δx| ≤ 2, (S1)" should also name c(k) ≤ sin a₀ and the first sentence of (G5) — cosmetic.)
- *|y − w| < R*: y ∈ 𝓡∖D ⊂ int K ⊂ int D(w, R).
- *Every F*₄ point*: F*₄ ⊆ F*, so EW applies; by Lemma S(2) each own = 4 point has a K-extreme and two S∩D middles within a of ±30°,
  and is in F* (REF_D1 §5 confirms own = 4 ⇒ y ∈ F*). Its cost is 2(own − 3) = 2. **Flag 5: correct.**

**Adversarial tests (`r7_refE7_geom.py`).**
- (1) Brute force in the w-frame, independent of E's code: 25 646 admissible (ρ, τ) samples (R = 10⁴…10⁶, ρ = R − 10^u,
  u ∈ [−9, 0.5], plus ρ ≤ R − 3; τ in a 3/R band around √3/2), 90 digits. In all 814 samples where k, z₂, z₃ are pairwise ≥ 1,
  τ ∈ [τ_lo, √3/2). No counterexample.
- (2) The lower end is exact in Q(√3, √(R² − 1)) (sympy, R = 10⁴): y = (0, ρ₀), k = (1, ρ₀), z± = (±½, ρ₀ + √3/2) have |wk| = R,
  |wz±|² = R² + √3ρ₀, |yk| = |yz±| = |z₊z₋| = |z₊k| = 1 exactly. This is paper Remark rem:sharp's configuration.

**Verdict on EW and Corollary EW: correct as stated**, including "the window does not depend on ε₀, θ or a₀".

## 3. Theorem G′ uniformity (flag 2) — CORRECT, with one inherited assumption made explicit

- D1r Corollary 6.1(1) runs Theorem G's proof with a := a₀ fixed (ε₀ = a₀, θ_s ≤ 2a₀, Λ = 231, M = ⌈36/η⌉, ℓ = 2M + 3) and
  Δ₂* = max{10⁴, 100ℓ}: the only κ-dependent item of Theorem G (Δ₂ ≥ 5/κ, used solely for κ(θ) < κ in Lemma 4.0) is dropped.
  N_ng = O(1/a₀), the seam term O(M²/a₀), N_thin = O(M²): all depend on (η, a₀) only. REF_D1 §5 states the same
  ("Exc is bounded exactly as in Theorem G, with Δ₂* not containing 5/κ"). With a₀ := 10⁻² fixed, C = C(η).
- Off the window F* = ∅ by Corollary EW, so F*₄ = ∅ and Σ_𝓡 v ≤ (6 + η)r + C(η). Nothing needs κ bounded below. **Correct.**
- *Inherited assumption (make explicit).* The step "min ≤ (9/7 + η)n + C(η)" also needs the e(S) inputs with absolute constants:
  Region I/τ > 1 (paper, C_bad absolute), Region II (paper Thm 11.3, + 87), Region III (Theorem W: e(S) ≤ s + (2/3)|Q′| + C). A3's
  earlier Region III bound had a 70/d term that blows up at d → 0; Theorem W is stated with an absolute C "in all of Region III", and the
  d = 0 case is covered by C's charging argument. The C report is lost, so I cannot re-verify that its C is d-independent; E's
  "uniform" claim (and D1r §9) inherit this. *Fix E2:* add "Theorem W's constant C is absolute (independent of d)" to the list of
  inputs in E §3.3.

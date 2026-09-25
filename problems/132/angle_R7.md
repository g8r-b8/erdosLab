# Erdős #132 / CDL Problem 1.6: Angle R7 — beyond 4/3 (CHECKPOINT, in progress)

Date started: 2026-09-24. Scratch: `scratchpad/R7/` (common context `R7/COMMON_R7.md`). Scripts: `scripts/r7_*.py`.
Starting point: angle_R6.md — L ≤ 4/3 overall (N3, refereed); 21/16 in Region I and τ > 1; 9/7 sharp for τ > 1 (E′).

## Branches
| branch | task | status |
|---|---|---|
| A2 | referee Region II: e(S) ≤ s + ½\|Q′\| + C (B2) | **DONE: CORRECT WITH FIXES** (§1) |
| A3 | referee Region III off-window e(S) ≤ s + 70/d + C, resonance strip, Lemma DP | pending |
| B | average R-weight ≤ 7 in Region II (⇒ 21/16 there, given A2) | pending |
| C | break the Region III resonance window via diametral partners (Lemma DP) | pending |
| D1 | Region I: average weight ≤ 6 (Conjecture C1) ⇒ 9/7 | pending |
| D2 | Region I: cross-edge e(D, X∖D) ≤ ½g_D + o(n) via E′ on conv X ⇒ 9/7 | pending |

Process: after a usage-limit outage killed all six first-launch agents (no output produced), branches run staggered,
at most two at a time; this file is checkpointed and committed after each branch reports.

## Established so far
Overall bound still **4/3** (refereed). New refereed input for Region II: see §1.

## 1. Branch A2: referee of B2's Region II theorem (report `scratchpad/R7/A2_ref/A2_report.md`)

**Verdict: CORRECT WITH FIXES.** Theorem BC, Lemma CONS and Theorem II are correct: **e(S) ≤ s + ½|Q′| + C** for
√3/2 + 3β ≤ τ ≤ 1. With μ(Δ₂) ≤ 1.5s − ½|Q′| + C_V (WRITEUP_A2 Lemma 4.2 applied to Q′), the LP gives
**min{μ(Δ₂), μ(δ)} ≤ max{5/4, 3c/(2c+1)}·n + C** in Region II, where 2c is the average R-weight. The referee checked the LP certificate
(it needs only q ≥ 0), L0, Lemma Z, ORD, the gap definition, BC, CONS and Theorem II line by line against WRITEUP_A2 §§3–7
and angle_R4 §§2–3. So Region II is now LP-equivalent to Region I: N3 (c = 4) gives 4/3, and **any c < 4 beats 4/3**.

Fixes (replacement text is in A2 §4; none changes a statement):
- F1 (BC step 3, different Z with the same centre): R4's argument does not transfer verbatim, because a K-end sits up to φ outside its D-range. The
  D-ranges are ≥ α₁ apart, and **2φ < α₁** (rational certificate 2φ/α₁ ≤ 2s_τ(1 + 1/(2R²)) < 0.8881), so the K-ranges
  are disjoint.
- F2 (Theorem II step 5): a shared endpoint v_B = v_A′ means B = A′, which is consecutive gaps, the CONS(b) case (≤ 24 rungs).
- F3 (ORD): each rung is a monotone radius-graph in the annulus (L0), so reversed orders cross (by the IVT), which is impossible for unit
  segments.
- F4: constants. CONS(a) true bound 6, CONS(b) = 24, 2U ≤ |Q′| + 34 + C.
- B2's flagged Lemma Z(a) at end vertices needs no fix: the induction never starts at an end vertex.

**Adversarial tests (60 digits, `r7_A2_configs.py`).** Config A is a realisable radial strip with e − s = U − 1 and |Q′| = 2U,
so **θ = ½ is locally sharp** in Region II. Configs A2 and C are not realisable (a D-point sits in a K-point's radial "shadow"). Config B is
realisable and consistent. No violation was found.

**New (PROVED by the referee, not yet second-refereed): Shadow lemma and Theorem II-sharp.** If v ∈ C(w,R) and z ∈ C(w,Δ)
have angular offset |o| < φ about w, then |z − v|² = R² + Δ² − 2RΔ cos o < 1, the rung length. Hence no point of X
sits there. Consequently, in Region II the number of unbroken gaps satisfies U = O(1) unless **α₂ − α₁ = 2φ exactly**, i.e. on a single
curve τ = τ*(R) with 1 − τ* = 1/(8R²) + O(R⁻⁴). So **e(S) ≤ s + C in all of Region II off that curve**, and the value there is 3c/(2c+1). On the curve, Theorem II
holds and is locally sharp. (Coordinator check: the shadow inequality follows from the law of cosines with the rung itself as the
equality case. It is correct.)

Scripts (copied to `scripts/`, all pass with `.venv/bin/python`): `r7_A2_constants.py` (L0 identity, 2φ/α₁ certificate,
CONS counts, LP values), `r7_A2_configs.py` (configs A, A2, B, C), `r7_A2_shadow.py` (τ*(R), rational bounds).

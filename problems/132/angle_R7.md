# Erdős #132 / CDL Problem 1.6: Angle R7 — beyond 4/3 (CHECKPOINT, in progress)

Date started: 2026-09-24. Scratch: `scratchpad/R7/` (common context `R7/COMMON_R7.md`). Scripts: `scripts/r7_*.py`.
Starting point: angle_R6.md — L ≤ 4/3 overall (N3, refereed); 21/16 in Region I and τ > 1; 9/7 sharp for τ > 1 (E′).

## Branches
| branch | task | status |
|---|---|---|
| A2 | referee Region II: e(S) ≤ s + ½\|Q′\| + C (B2) | **DONE: CORRECT WITH FIXES** (§1) |
| A3 | referee Region III off-window e(S) ≤ s + 70/d + C, resonance strip, Lemma DP | **DONE: CORRECT WITH FIXES** (§2) |
| B | average R-weight ≤ 7 in Region II (⇒ 21/16 there, given A2) | **DONE: PROVED, unrefereed** (§3); referee REF_B pending |
| C | break the Region III resonance window via diametral partners (Lemma DP) | pending |
| D1 | Region I: average weight ≤ 6 (Conjecture C1) ⇒ 9/7 | pending |
| E | Region III off the fan pin (\|t − √3/2\| ≥ O(ε₀)): weight ≤ 7 and the \|Q\| term there | queued |
| D2 | Region I: cross-edge e(D, X∖D) ≤ ½g_D + o(n) via E′ on conv X ⇒ 9/7 | pending |

Process: after a usage-limit outage killed all six first-launch agents (no output produced), branches run staggered,
at most two at a time; this file is checkpointed and committed after each branch reports.

## Established so far
Overall bound still **4/3** (refereed). After A2 and A3, the |Q| term is removed (refereed) everywhere except the Region III
resonance window τ = √3/2 + O(1/R). Off that window, every regime has value max{5/4, 3c/(2c+1)}, so the bound drops below 4/3
as soon as the average R-weight 2c is < 8 there (branch B). The window itself is branch C.
Branch B (unrefereed) gives 2c = 7 in Region II, so **21/16 in Regions I, II and τ > 1** (Region II pending the referee).
Only Region III (√3/2 − 2β < τ < √3/2 + 3β) remains at 4/3.

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

## 2. Branch A3: referee of B2's Region III results (report `scratchpad/R7/A3_ref/A3_report.md`)

| item | verdict |
|---|---|
| Theorem III: e(S) ≤ s + 70/d + C for Rd ≥ 5, where d = \|2 sin θ₀ − 1\| | **CORRECT WITH FIXES**; the statement and the constant 70 stand |
| BC step 3, distinctness of singleton-gap vs arc-gap breaks | the sketch was incomplete but the claim is true; A3 gives a full proof (D1–D4) as replacement text |
| Lemma RES | **fix**: ℓ ∈ {−1,0,1} needs the span bound kα₁ ≤ π/3 to exclude ℓ = −2 (margin 0.0475). Sharpened to d ≤ (k+1)/R, so U < 47/d + 1 |
| Lemma CONS(a) in Region III | the count is 0: there are no same-sign unbroken gaps |
| Lemma Z(a) at end vertices; KB; the count | CORRECT |
| resonance strip, e(S) − s = \|Q′\| | **CORRECT, exact, LOCAL only** |
| Lemma DP / Corollary DP (< 10Δ^{2/3} D-points per strip) | **CORRECT WITH MINOR FIXES** |

**New exact identity.** sin φ = s_τ/Δ, because the rung positions are 2s_τ apart on C(w,Δ). Hence:
- **2φ < α₁ ⇔ τ > √3/2.** This proves B2's float observation, and A2's Region II certificate becomes 2φ/α₁ ≤ 2s_τ < 0.8881 for every R.
- **2φ < α₁ + α₂ always**, with R(α₁ + α₂ − 2φ) ≥ 0.93 on Region III. This inequality is all Region III needs.

**Resonance strip.** Closed forms:
- Δ = (√(4R²−1) + √3)/2;
- τ = cos(π/6 + α₂/2);
- s_τ = Δ/(2R), so d = t/R exactly and Rd ≈ 0.866, which is inside the window.

A 60-digit interval check at R = 10⁴, 10⁵ and 10⁶ confirms:
- the unit pairs are exactly the T-edges and the rungs;
- only w–v_j are at distance R and only w–z_j are at distance Δ.

The strip is local only. In X₀ = {w} ∪ V ∪ Z the z_j have no Δ₂-partner (they are 𝓡∩D, and e(S) = s − 2). The obstruction needs each z_j ∈ S through a far partner y_j. Lemma DP puts those partners in D(w, 5Δ/N + 3), so one strip has < 10Δ^{2/3} points and **#centres ≥ U/(10Δ^{2/3})**.

**DP fixes.**
- Step 2: replace the step-2 bound on B by B ≥ −(c₀/(2Δ)) cot b.
- Corollary DP needs t ≤ 1, which holds wherever rungs exist, and N ≥ 5√Δ.
- The numerical monotonicity claim is replaced by the exact inequality 3x² − 28x − 100 > 0 for x = Δ^{1/3} ≥ 13.
- The DP bound is nearly sharp: worst ratio 0.99995 over 3696 extremal partners.

Scripts (in `scripts/`, all pass): `r7_A3_phi.py` (the identity and interval covers), `r7_A3_strip.py` (the strip, closed forms and
60-digit check), `r7_A3_dp.py` (DP extremal test), `r7_A3_distinct.py` (distinctness D1–D4).

## 3. Branch B: average R-weight ≤ 7 in Region II (report `scratchpad/R7/B_weight7/B_report.md`; UNREFEREED)

**Claim (PROVED by B, not yet refereed).** In Region II, Σ_{y∈𝓡} v(y) ≤ 7|𝓡| + C. With Theorem II (A2) and the LP,
**min{μ(Δ₂), μ(δ)} ≤ 21n/16 + C in Region II.**

The key observation is that there are no fans in Region II. N3's fan window t ∈ [0.751, 0.950] is an artefact of ε₀ = 1/50. B1's refereed
Lemma P1.2 works at ε₀ = 10⁻⁶, where every F6, F5 or HF point forces |t − √3/2| ≤ 5ε₀ + δ₀ < 2·10⁻⁴. But Region II has t ≥ τ ≥ √3/2 + 0.03.
Caps need t = ½ ± δ₀. So the heavy good points are only A (6,2) and D_II (5,3), both with v = 8. B1's band-H radius-1
discharging carries over:
- the cone is [−36°, 36°], so each receiver has ≤ 2 senders at ½ each;
- D_II receivers (v ≤ 7) forward one level deeper, to depth ≥ √3 where m = 0;
- the final charge is ≤ 7.

**Tests (all pass):**
- `r7_B_margins.py`: rigorous 60-digit intervals for margins M1–M11.
- `r7_B_classify.py`: a slot scan over t ∈ [0.896, 1]. Only A and D_II occur, and max v = 8.
- `r7_B_rules.py`: a beam search over 1.8·10⁵ configurations. The max final charge is 7.000.
- `r7_B_lattice_t1.py`: an exact Fraction model at t = 1, 2·10⁴ random dense configurations. The max final charge is exactly 7.
- R4's exact fan chain has τ = 0.865975 < √3/2, so it lies in Region III, consistent with the claim.

**Limit.** B1's A-row stack E1 is t-independent, so radius-1 charging stops at 7 here too. The true average is plausibly 6, which would give 9/7.

**Referee flags:**
1. P1.3 is stated for Region I; Region II uses the independent M2 step.
2. Forwarders need not be good, so frame agreement goes through the sender (B1 P0.2).
3. M7 safety factors.

**Coordinator remark (new sub-question, Region III).** The fan pin |t − √3/2| < 2·10⁻⁴ (or O(ε₀) for any fixed ε₀) also
applies inside Region III. So the part of Region III with |t − √3/2| ≥ 5ε₀ + δ₀ has no fans either, and plausibly also has
weight ≤ 7. The genuinely hard zone is then |t − √3/2| = O(ε₀), which contains the resonance window. This is open and has been queued as branch E.

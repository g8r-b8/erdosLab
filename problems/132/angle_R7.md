# Erdős #132 / CDL Problem 1.6: Angle R7 — beyond 4/3 (CHECKPOINT, in progress)

Date started: 2026-09-24. Scratch: `scratchpad/R7/` (common context `R7/COMMON_R7.md`). Scripts: `scripts/r7_*.py`.
Starting point: angle_R6.md — L ≤ 4/3 overall (N3, refereed); 21/16 in Region I and τ > 1; 9/7 sharp for τ > 1 (E′).

## Branches
| branch | task | status |
|---|---|---|
| A2 | referee Region II: e(S) ≤ s + ½\|Q′\| + C (B2) | **DONE: CORRECT WITH FIXES** (§1) |
| A3 | referee Region III off-window e(S) ≤ s + 70/d + C, resonance strip, Lemma DP | **DONE: CORRECT WITH FIXES** (§2) |
| B | average R-weight ≤ 7 in Region II (⇒ 21/16 there, given A2) | **DONE: PROVED, REFEREED (REF_B: correct with fixes)** (§3) |
| C | break the Region III resonance window via diametral partners (Lemma DP) | **DONE: Theorem W PROVED, REFEREED (REF_C: correct with minor fixes)** (§4) |
| D1 | Region I: average weight ≤ 6 (Conjecture C1) ⇒ 9/7 | **DONE: Theorem G PROVED, unrefereed** (§5). Reconstructed by D1r (`angle_R7_reports/D1_report.md`); **REFEREED ONCE (REF_D1: correct with cosmetic fixes)**; a second independent referee is queued |
| E | Region III fan zone \|t − √3/2\| ≤ κ₁: bound \|F*\| or the average weight (off the fan zone, D1 covers it) | running (relaunched after the panics) |
| D2 | Region I: cross-edge e(D, X∖D) ≤ ½g_D + o(n) via E′ on conv X ⇒ 9/7 | pending |

**Data loss (2026-09-25).** Two kernel panics caused by memory exhaustion in another session wiped the scratchpad, including all R6/R7 scratch reports.
What survives is the summaries in this file and angle_R6.md, all committed scripts, and `angle_R7_reports/`. From now on, reports are written
directly to `problems/132/angle_R7_reports/` and committed. Jobs are wrapped in the `memcap.sh` RSS watchdog.

Process: after a usage-limit outage killed all six first-launch agents (no output produced), branches run staggered,
at most two at a time; this file is checkpointed and committed after each branch reports.

## Established so far
Overall bound still **4/3** (refereed). **Off the fan zone: 9/7 + η, refereed once (D1r + REF_D1).** After A2 and A3, the |Q| term is removed (refereed) everywhere except the Region III
resonance window τ = √3/2 + O(1/R). Off that window, every regime has value max{5/4, 3c/(2c+1)}, so the bound drops below 4/3
as soon as the average R-weight 2c is < 8 there (branch B). The window itself is branch C.
Branch B, refereed by REF_B, gives 2c = 7 in Region II, so **21/16 is REFEREED in Regions I, II and τ > 1**.
Branch C (refereed by REF_C) removes the resonance obstruction: in all of Region III e(S) ≤ s + (2/3)|Q′| + C, so the Region III value is
max{3c/(2c+1), 9/7}. **Only the R-weight in Region III now stands between 4/3 and a better overall bound.** In Region III fans exist
at |t − √3/2| = O(ε₀), and N3 gives only c = 4 there. That weight question is branch E.

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

**Referee REF_B (`scratchpad/R7/REF_B/REF_B_report.md`): CORRECT WITH FIXES.** No counterexample was found, and every margin
M1–M11 was re-verified rigorously (`r7_refB_margins.py`). The referee also:
- confirmed the classification is complete with their own slot classifier (`r7_refB_classify.py`);
- ran an exact Q(√3) search with up to 11 heavy points (`r7_refB_exact.py`, `r7_refB_search.py`). The final charge is ≤ 7, with 0 anomalies.

Fixes (expository; replacement text in REF_B §7):
- F1: replace Theorem 1 step 1 by a direct argument. D-type neighbours lie within 26.36° of vertical, which with Lemma P gives m ≤ 3 and the kinds {K,K,D}. The fan exclusion via P1.2 is not needed.
- F2: an optional shorter M7, with about 30° of slack.
- F3: ψ_K ≈ 90° occurs for every t in Region II (fix the attribution).
- F4: the frame-agreement distance is ≤ 4, since two forwarders are possible. Use P0.2 with ρ = 6.
- F5: 𝓡∩D points never receive.
- F6: the evidence gap is closed.

**So Region II: min ≤ 21n/16 + C, REFEREED.**

**Coordinator remark (new sub-question, Region III).** The fan pin |t − √3/2| < 2·10⁻⁴ (or O(ε₀) for any fixed ε₀) also
applies inside Region III. So the part of Region III with |t − √3/2| ≥ 5ε₀ + δ₀ has no fans either, and plausibly also has
weight ≤ 7. The genuinely hard zone is then |t − √3/2| = O(ε₀), which contains the resonance window. This is open and has been queued as branch E.

## 4. Branch C: the resonance window (report `scratchpad/R7/C_window/C_report.md`; UNREFEREED)

**Theorem W.** In all of Region III, e(S) ≤ s + (2/3)|Q′| + C. For R|d| > 4 this improves to s + ½|Q′| + C, and for Rd < −4 to s + C.
With κ = ½ the LP value is max{3c/(2c+1), 1 + (2/3)/(2·(7/6))} = **max{3c/(2c+1), 9/7}**. Hence:
- c = 4 gives 4/3;
- c = 4 − η gives < 4/3;
- c = 7/2 gives 21/16.

There is also a fallback that uses only AI, SG and NC: θ = 4/5 with value max{3c/(2c+1), 17/13}. It gives the same conclusions for c ≤ 7/2.

Ingredients (exact checks). Write G := 2R sin(θ₀ − π/6); G = 1 is exactly B2's strip.
1. **Cone lemma and Lemma AI** (`r7_C_cone.py`, `r7_C_cone_ring.py`). Take z_i strictly between z_k and z_l on C(w,Δ). Then any Δ₂-partner of z_i would be
   diametral to z_k or z_l. So only the two end points at each end of an arc of D-points can be in S. A rung-carrying D-component has ≤ 4
   S-points, and arc gaps need R|d| ≤ 4. **This kills B2's single-centre strip**: at most 4 of its D-points are in S.
2. **Lemma SG** (`r7_C_sg.py`). A singleton gap forces |ww′| = |1 − G|. Singleton gaps therefore exist only at G = 1 (same centre) or G ≥ 2, and never for τ ≥ √3/2.
3. **Lemma NC** (`r7_C_nc.py`). Two consecutive singleton gaps with G ≥ 2 are impossible. This uses the identity |z₀w₂|² = Δ² − 4br sin ψ sin(ψ/2) ∈ (R², Δ²).
4. **Lemma P4** (`r7_C_p4.py`). At G = 1, same-centre runs of ≥ 3 gaps are impossible. The eliminant polynomials have no real root ≥ 10⁴, and a 60-digit
   interval evaluation at R = 10⁴ fixes the sign.
5. **Lemma Q** (`r7_C_q.py`). A K-point with two points of X outward of its whole normal cone has Δ₂-degree 1. This handles d = 0.
6. The run ratios (gaps per Q′-point) are:
   - d < 0: ≤ ½;
   - d > 0 with G ∉ {1} ∪ [2,∞): ≤ 4/9;
   - G = 1: ≤ 2/3;
   - G ≥ 2: < 2/3;
   - d = 0: ≤ 2/3 (charging).

   The LP is checked in `r7_C_lp.py`.

Confidence: high for AI, SG, NC, P4, Q and the LP. Medium-high for the run framework (A3's D1–D4 extended to the closed arcs of unbroken gaps) and the d = 0
charging argument. Both need a referee. Consistency: ienjoymath's construction lies in Region I with Q = ∅, so AI holds there vacuously. AI also held on 11 991 interior arc points in
random adversarial sets. Nothing below 9/7 is claimed. Open: whether θ ≤ ½ holds everywhere. This does not matter for the LP.

**Referee REF_C (`scratchpad/R7/REF_C/REF_C_report.md`): CORRECT WITH MINOR FIXES.** The referee made independent checks at 80 digits in
`r7_refC_{geom,adv,d0,shadow,res}.py`. Theorem W stands, and so does the LP value max{3c/(2c+1), 9/7}. Fixes:
- F1: "each K-vertex is v_A of at most one gap" is false at d = 0. Count only unbroken gaps (v_A ≠ v_B) and restate ψ-injectivity.
- F2: replace "D2/D3 apply verbatim" by the full five-case list for closed arcs. D3 applies to both K-ends of a singleton gap, and a run closing into a cycle
  changes the count by ≤ 1.
- Minor: P4 should read "a run of ≥ 3 gaps at G = 1".

Adversarial tests:
- The G = 1 two-gap run is locally realisable, so 2/3 is locally sharp there.
- Double runs, double triangles and alternating G ≥ 2 runs are impossible.

**New (REF_C, exact).** A shadow obstruction rules out any unbroken inward arc gap (ℓ = +1, k ≥ 1), so C's case 2 is vacuous. Hence θ = ½ in all of Region III
except on the curve G = 1, where 2/3 is sharp, and at d = 0, where 2/3 is proved and ½ holds numerically.

## 5. Branch D1: average R-weight ≤ 6 away from the fan zone (report `scratchpad/R7/D1_weight6/D1_report.md`; UNREFEREED)

**This is potentially the headline result. It is under hostile referee (REF_D1).** Orientation replaces discharging.
- **Fact 1.2.** Σ_𝓡 v = 2E_𝓡 exactly, where E_𝓡 counts the unit edges with at least one end in 𝓡.
- **Lemma O.** If y owns only edges pointing into a half-open half-circle, then y owns ≤ 3 edges.
- **Fact 1.1.** 𝓡∖D ⊂ int K, and X ∩ ∂K∖D ⊂ S.
- **Fact 1.3.** 𝓡∩D has degree ≤ 3.
- **Theorem F (flat model).** Orienting by "height" gives Σv ≤ 6r exactly. This is tight on the A-row stack and the cap lattice, where radius-1 charging was stuck at 7.
- **Lemma S (tilted frames, 60 digits).** A good point owns ≤ 3 edges unless |t − √3/2| ≤ κ₁ = 2.1·10⁻³.
- **Theorem G.** For every η > 0: **Σ_𝓡 v ≤ 6|𝓡| + ηn + C_η for all X with |t − √3/2| ≥ κ₁.** The proof uses sector frames and averages over random cut positions.

⇒ min ≤ (9/7 + η)n + C_η in **Region I (sharp; ienjoymath's construction), Region II, τ > 1, and Region III off the fan zone**. In Region III the
bound uses Theorem W's value max{3c/(2c+1), 9/7} with c = 3.

**Corollary 6.1.** For all t, Σv ≤ 6r + 2|F*| + ηn + C_η, where F* is the set of fans and half-fans with both ±30° neighbours in S∩D. Only the fan zone
|t − √3/2| ≤ κ₁ remains, and there only |F*| matters (branch E).

D1's referee flags:
1. Lemma T* rescaled to |pb| ≤ 4D₁ + 1 is not rewritten line by line.
2. The count of non-good points in B1 P0.1 is independent of v.
3. The expected cut count ℓ/Λ_s for perimeters that are not multiples.

Scripts (`scripts/`, all pass): `r7_D1_flat_orient.py`, `r7_D1_tilt.py`, `r7_D1_global_hex.py`, `r7_D1_ring.py`.

### 5.1 D1r: reconstruction and repair (`angle_R7_reports/D1_report.md`, STATUS FINAL; UNREFEREED)

- **Theorem G.** For every η, κ > 0: if |t − √3/2| ≥ κ, then Σ_𝓡 v ≤ (6+η)r + C(η,κ). C is explicit, and there is no hypothesis on τ.
  D1's constant is rigorously κ₁ < 1.553·10⁻³.
- **Corollary 6.1.** For all t, Σ_𝓡 v ≤ 6r + 2|F*₄| + ηr + C, where each F*₄ point owns exactly 4 edges.
- **Theorem 9.1.** min{μ(Δ₂), μ(δ)} ≤ (9/7 + η)n + C(η,κ) off the fan zone. The Region III row uses Theorem W.
- **Fan-zone value.** 3(3+φ)/(7+2φ), where φ = |F*₄|/r. This equals 9/7 at φ = 0 and 4/3 at φ = 1.

Repairs relative to D1:
1. Edges at 𝓡∩D points are owned by the 𝓡∩D end.
2. The deep zone uses a single frame with a random depth threshold T; the interface costs ≤ 3r/M.
3. Lemma S is proved directly from paper Lemmas 9.3, 9.4 and 2.2(b).

D1's flags are resolved. The random-configuration test `r7_D1r_global.py` passes: each edge is owned exactly once, and Σv ≤ 6r + 2#fans + 6|Exc|.

D1r's self-critique names the weakest points:
- the Gauss-map/seam argument (Lemma 4.5);
- the Remark 5.2 constants;
- that C(η,κ) → ∞ as κ → 0, so nothing uniform holds on the fan zone.

### 5.2 REF_D1: hostile referee of D1r (`angle_R7_reports/REF_D1_report.md`, FINAL)

**Verdict: CORRECT WITH FIXES.** The fixes are cosmetic and no statement changes. The following stand:
- Theorem G;
- Corollary 6.1;
- Theorem 9.1 (in Region III it is conditional on Theorem W, which has been refereed once);
- the fan-zone value 3(3+φ)/(7+2φ).

Checks:
- κ₁ < 1.5525·10⁻³ (60-digit intervals).
- The random threshold T is essential.
- The constant is huge: C(0.1, 0.02) ≈ 2.57·10¹⁵.
- On the curved-K / r ~ R stress test, the excess is O(width) and no counterexample was found. This settles the flat-hexagon worry: E_𝓡 = 3r + 6k − 3 comes from the 60° corners, and K has none.
- The LP is exact, and ienjoymath's construction is consistent.

Fixes (appended to D1_report.md as Errata):
- F1: restrict rule (O1) to 𝓡∖D.
- F2: allow any η > 0, with M = ⌈36/η⌉.
- F3: "own ≤ 4 on F*∖Exc".
- F4: §4.6 wording.

Optional sharpening R1: the pinning window is θ-independent, κ′ ≤ 7ε₀ + 5/Δ₂ (e.g. < 4.57·10⁻⁴).

Scripts: `r7_refD1_{lemmaS,global,lp}.py`.

**Status of the headline.** min ≤ (9/7 + η)n + C(η,κ) holds off the fan zone |t − √3/2| < κ, refereed once. It is sharp (ienjoymath). The overall rigorous bound stays 4/3
until the fan-zone density φ = |F*₄|/r is bounded (branch E). A second independent referee of D1r is required before this goes in the paper.

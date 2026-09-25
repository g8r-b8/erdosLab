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

## 4. Lemma U, Lemma C2(a) (flag 3), Proposition F — CORRECT (C2(a) needs a one-line rewording)

**Lemma U.** By §2, every Δ₂-partner w″ of k has |z₂ − w″| = |z₃ − w″| = Δ, so w″ ∈ C(z₂,Δ) ∩ C(z₃,Δ) = {w, w*}. w* is the reflection
of w in the line z₂z₃, so |ww*| = 2√(Δ² − |z₂z₃|²/4), |ww*|² = 4Δ² − |z₂z₃|² ≥ 3Δ² (|z₂z₃| ≤ Δ trivially). As w″ ∈ X, |ww″| ≤ Δ, so
w″ = w. k has exactly one Δ₂-partner: **k ∈ Q** (paper's Q, all Δ₂-degree-1 points). Two K-extremes of one fan share w. **Correct.**
(It uses only that the middles are in D, not that they are in S.)

**Lemma C2(a).** E's flag 3 describes the argument as "frames of good points within 2 differ by ≤ 2ε₀". As a citation this is
imprecise: the second sentence of (G5) needs |y − y′| ≤ ρ − 1, and D1r's goodness uses ρ = 1, so it gives nothing for |y − y′| ≤ 2.
The argument is nevertheless right, through the **first** sentence of (G5) at the common point k:
by Lemma U, u_k = (w − k)/R is the unique inward normal defined by a partner, and −u_k is an outer normal of K at k ∈ γ^Λ_y ∩ γ^Λ_{y′};
so n₀(y) and n₀(y′) are both within ε₀ of −u_k. In y's frame y − k = −(sin ψ_k, cos ψ_k) with |ψ_k ∓ 90°| ≤ a₀, so the direction of
y − k is within a₀ + ε₀ of ∓(tangent at k); the same holds for y′. If both have k on the same side (+90° or −90°), the directions of
y − k and y′ − k differ by ≤ 2(a₀ + ε₀) ≤ 0.04 rad, so |y − y′| ≤ 2 sin 0.02 < 1, contradicting y ≠ y′. Hence ≤ 1 per side, ≤ 2 in all.

*Fix E3 (replacement text for C2(a)'s proof).* "Let y, y′ ∈ F* have K-extreme k. By Lemma U, −u_k = (k − w)/R is an outer normal of K at k,
and k ∈ γ^Λ_y ∩ γ^Λ_{y′}; by the first sentence of (G5) at y and at y′, n₀(y) and n₀(y′) are within ε₀ of −u_k. As k is within a₀ of ±90°
in each frame, y − k and y′ − k are within a₀ + ε₀ of ∓u_k^⊥. If k has the same sign in both frames, then ∠(y − k, y′ − k) ≤ 2(a₀ + ε₀)
< 60°, so |y − y′| < 1, which is impossible. So k is the K-extreme of at most one point of F* on each side."

**The factor 2 is locally sharp (new).** `r7_refE7_geom.py` (3): two fans y, y′ on opposite sides of one K-extreme k, both with centre w,
are locally realisable at **every** τ in the window (40/40 grid points, R = 10⁴ and 10⁶, 90 digits; all 8 points w, k, y, y′, z₂, z₃,
z₂′, z₃′ pairwise ≥ 1; at G = 2, |z₃z₃′| = 1 + √3/R + O(R⁻²)). So F ≤ 2p cannot be improved to F ≤ p (which would give 45/34) by the
local geometry around one K-extreme; any such improvement must be global.

**Proposition F.** y ↦ k(y) (a chosen K-extreme) maps F* into Q_K ⊆ Q with fibres of size ≤ 2. So |F*₄| ≤ |F*| ≤ 2|Q_K| ≤ 2p,
and |F*₄| ≤ r. **Correct.**

## 5. The LP (Theorem E) — CORRECT; exact vertex enumeration and "what survives"

`r7_refE7_lp.py`: variables (s, p, q′, F, z), r = 1 − s; maximise z subject to z ≤ (3/2)s − ½p, z ≤ s + θq′ + 3r + F, 0 ≤ q′ ≤ p ≤ s,
0 ≤ F ≤ r, F ≤ 2p (optionally p ≤ 2s/3); **all** 5-subsets of the constraints solved exactly in Fractions, feasible vertices kept.

| θ | V (exact) | optimal vertex (s, p, q′, F) | p ≤ 2s/3 cap |
|---|---|---|---|
| 2/3 | **81/61** = 1.327869 | (55, 3, 3, 6)/61 | inactive (same value) |
| ½ | **53/40** = 1.325 | (36, 2, 2, 4)/40 | inactive |

E's dual certificates were re-checked independently: for θ = 2/3, weights (40/61, 21/61) and multipliers (14/61, 18/61, 3/61) on
(p − q′, r − F, 2p − F) give coefficients exactly (81/61, 81/61, 0, 0, 0) on (s, r, p, q′, F); for θ = ½, (13/20, 7/20) and
(7/40, 11/40, 3/40) give (53/40, 53/40, 0, 0, 0). E's closed form V(φ) = (9 + 4.5φ)/(7 + 19φ/6) (θ = 2/3, F = 2p) was re-derived by hand.

**What survives if an input fails** (same enumeration):

| scenario | value |
|---|---|
| all inputs as claimed (θ = 2/3) | 81/61 = 1.32787 |
| Proposition F fails (only F ≤ r), any θ ≤ 2/3 | 4/3 |
| Theorem W fails (R4's e(S) ≤ s + p, θ = 1), even with Proposition F | 4/3 |
| C's fallback θ = 4/5 (AI, SG, NC only) with Proposition F | 137/103 = 1.33010 |
| C2 weakened to ≤ 3 (resp. 4) fans per K-extreme | 117/88 = 1.32955 (resp. 153/115 = 1.33043) |
| hypothetical F ≤ p (θ = 2/3; θ = ½) | 45/34 = 1.32353; 29/22 = 1.31818 |

So the improvement below 4/3 needs **both** Theorem W (θ < 1) and Proposition F; either alone gives exactly 4/3. With only C's fallback
θ = 4/5, the bound is still below 4/3 (137/103).

## 6. X1, C2(b), ORD (flag 6), the 53/40 scope, and §4 (lower bound)

**Lemma X1 — correct** (not used by Theorem E). The step "β − m ∈ (−61°, 0°]" should read "(−61°, O(1/R)]" (β₀ ≈ 1/(2Δ) can exceed
m − 60°); only β − m ∈ (−90°, 90°) is used, so nothing changes. Independent brute force (`r7_refE7_geom.py` (4)): 108 window fans ×
4000 positions of w′ on C(z₃, Δ) with |w′ − w| ≥ 1; no w′ satisfies X1's three constraints |w′w| ≤ Δ, |w′z₂| ≤ Δ, |w′k| ≤ R.

**Lemma C2(b) — plausible, not fully written** (not used by Theorem E): the O(1/R) slot estimate is numerical (as E says).

**Lemma ORD — correct; replace the proof** (flag 6). Cleaner proof by cyclic order: diametral endpoints are vertices of P = conv X, and
any two diametral segments intersect (Hopf–Pannwitz), so for points in convex position their endpoints interleave in the cyclic order of
∂P or share an endpoint. *Replacement text:* "The partners of w lie on C(w, Δ) ∩ ∂P, and their cyclic order along ∂P is their angular
order about w. Let z, c, c′ be partners of w in this order (z before c before c′, going around ∂P from w), and let w_c ≠ w be another
partner of c. The chord cw_c meets wz, so w_c lies on the open arc of ∂P from w to z not containing c (it cannot be z: then [c, z] and
[w, c′] would be disjoint); it also meets wc′, so w_c lies on the open arc from c′ to w not containing c. These arcs are disjoint:
contradiction. Symmetrically on the other side, using c′'s second partner." This removes the left/right orientation bookkeeping.

**The 53/40 scope.** 53/40 uses REF_C's remark (θ = ½ in Region III except on G = 1 and at d = 0), which had one pass and whose report
is lost. The window includes its endpoint G = 2, where C's Lemma SG allows singleton gaps with distinct centres (|ww′| = |1 − G| = 1)
and C's run table lists "G ≥ 2: ratio < 2/3". The reduction to ½ there presumably uses NC (no two consecutive singleton gaps at G ≥ 2)
plus REF_C's shadow obstruction (no l = +1 arc gaps), leaving runs of one singleton gap. *Fix E4:* state 53/40 as conditional on REF_C's
remark **including G = 2**, and note that if G = 2 is not covered, that single curve falls back to 81/61. The headline 81/61 is unaffected.

**§4 (lower bound).** Claims are correctly hedged: no construction with more than O(1) points of F* is known; R4's single-centre chain
gives ≤ 2 (via Lemma AI + C2(b)); the Reuleaux-with-pendants family has F* = ∅ (`r7_E_reuleaux.py` rerun: passes for N = 101, 301, 1001
at G = 1 and N = 301 at G = 0.3, 1.9; the obstruction is robust to adding points, since supersets only add constraints and keep Δ).
§4.3's case analysis is a sketch and the arc-span statement is labelled a conjecture. The lower bound in the window stays the global 9/7.

## 7. Consistency

- ienjoymath's construction (Region I, t → 0) lies outside the window, so F* = ∅ there by Corollary EW, consistent with its measured
  Σ_𝓡 v ≤ 6r. No bound below 9/7 is claimed anywhere (81/61 > 53/40 > 9/7).
- The local examples: R4's fan (paper rem:sharp) is exactly the lower end τ_lo (exact, §2 (2)); the two-fans-per-K-extreme
  configuration is locally realisable across the window (§4), consistent with Proposition F's factor 2.
- All earlier windows (N3 [0.751, 0.950], B's 5ε₀ + δ₀, D1r's κ(θ), REF_D1's κ′ ≤ 7ε₀ + 5/Δ₂) contain EW's window
  t ∈ [√3/2 − 0.3751/Δ₂, √3/2 + 0.1251/Δ₂): consistent.

## 8. Verdict

**CORRECT WITH FIXES.** I found no error in any inequality used by Theorem E or Theorem G′. The fixes are expository, and none changes a
statement:
- E1: the Q-sets (Q′ ⊆ Q up to O(1); table label).
- E2: list "Theorem W's C is absolute in Region III" among the inputs of the uniform claim.
- E3: C2(a) must go through the first sentence of (G5) at k, not through "frames within 2" (unavailable at ρ = 1). Replacement text in §4.
- E4: 53/40 must explicitly include G = 2 in REF_C's θ = ½ remark (otherwise that curve is 81/61).
- Cosmetic: Lemma S(d)'s ingredient list (§2), X1's interval (§6), and the ORD proof replaced by cyclic interleaving (§6).

**What stands (conditional on the inputs' statuses: D1r Corollary 6.1 refereed once; Theorem W refereed once, report lost):**
- Lemma EW (exact window 0 < G ≤ 2, sharp at the lower end exactly, upper end not attained): proved.
- Theorem G′: 9/7 + η with C = C(η) outside the window.
- Lemma U, C2(a), Proposition F |F*₄| ≤ 2|Q|; the factor 2 is locally sharp.
- **Theorem E and the overall bound min{μ(Δ₂), μ(δ)} ≤ (81/61 + η)n + C(η)**; 53/40 + η off G = 1 (conditional, E4).
- Sensitivity: losing Proposition F or Theorem W returns exactly 4/3; with C's fallback θ = 4/5 the bound is 137/103 < 4/3.

**Recommendation.** 81/61 now rests on D1r (one referee) and Theorem W (one referee; the C/REF_C reports were lost in the wipe). The
most useful next step is a reconstruction and second referee of Theorem W (Q′ ⊆ Q, the d-independence of C, the G = 2 case), since the
sub-4/3 bound fails without it.

STATUS: FINAL

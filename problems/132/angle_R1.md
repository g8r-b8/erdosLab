# Erdős #132, angle R1: a third rare distance for odd n (n = 15, 17 certified; geometric route partial)

(2026-09-23. Continues `angle_B2.md` and `angle_B3.md`, with the same notation. P is a strictly convex n-set,
n = 2m+1, m = ⌊n/2⌋. D = D(P) is the number of distinct distances and μ(d) the multiplicity of d. A distance is
*rare* if 1 ≤ μ ≤ n and *frequent* if μ ≥ n+1. k = #rare. R_M is the regular M-gon.)

## 0. Summary

| # | Statement | Status |
|---|---|---|
| 1 | **Thm 15.** Every strictly convex 15-set has k ≥ 3. | **proved (computer-assisted), fully certified.** Every case is refuted from Lemma Q alone, and every refutation is checked by drat-trim (§1). |
| 2 | **Thm 17.** Every strictly convex 17-set has k ≥ 3. | **proved (computer-assisted), fully certified**, same pipeline (§1). |
| 3 | Q-ORD (angle_B3 §5) holds for all odd 7 ≤ n ≤ 17. | certified (B3 for n ≤ 13, here for 15 and 17) |
| 4 | Geometric route A: a case tree for the odd K = 1 configuration (Prop B of angle_B2). Closed branches: A1 (conditional on Fishburn 1995 Lemma 6), B1b (unconditional), and several B2 sub-cases. | partial (§2) |
| 5 | New tools: **Lipschitz lemma** (a point inside a circle sees vertices of R_M at chord indices that change by less than the step), **arc rigidity**, **arc extension for R_{2m+1}**. | **proved** (§2.2) |

**Net effect on #132 (b), convex case.** k ≥ 3 holds for **every convex n-set with 6 ≤ n ≤ 18**:
- even n: angle_B2 Thm A;
- odd n ≤ 13: angle_B2/B3;
- n = 15, 17: this note.

For odd n ≥ 19 the open case is still exactly Prop B's configuration: D = m+1, with m−1 frequent classes.

## 1. Theorems 15 and 17 (ordinal SAT, drat-trim-certified)

### 1.1 Reduction

This is Lemma R of angle_B3.
- If k ≤ 2, then at least D−2 colour classes have ≥ n+1 pairs, and D ≤ m+1.
- So it suffices to refute:
  - every (n, D, 0) with D ≤ m−1, i.e. no colouring by exactly D colours satisfies Lemma Q (an "ordinal Altman");
  - every (n, D, D−2) with D ∈ {m, m+1}.

  For n = 15 that means (15,2..6,0), (15,7,5), (15,8,6). For n = 17 it means (17,2..7,0), (17,8,6), (17,9,7).
- The only geometric input is **Lemma Q**, the ordinal quadrilateral inequality, in the order encoding of
  `b3_sat.build(order_Q=True)`. Lemma T is not used.

### 1.2 Case split by the rare pair (`scripts/r1_sat_split.py`)

The split is assumption-free.
- Choose the D−2 frequent colours; the other two colours {r1, r2} form the case.
- In case (r1, r2):
  - every other colour gets a cardinality constraint "≥ n+1";
  - r1 and r2 must each be used;
  - the implied constraint |r1| + |r2| ≤ C(n,2) − (D−2)(n+1) is added as a redundant clause.
- Every counterexample falls under at least one of the C(D,2) cases. This includes colourings with more than D−2
  frequent classes.

### 1.3 Symmetry breaking (`sb=Dmax`)

The Q clauses and the case profile are invariant under the dihedral group. Reversing the cyclic order maps
diagonals to diagonals and opposite-side pairs to opposite-side pairs. Colour reversal is **not** a symmetry and is
not used.

Let L* be the largest cyclic length min(j−i, n−j+i) of a D-coloured pair.
- **Rotation.** We may assume {0, L*} is a D-edge. The encoding uses a selector s_L for each L:
  - s_L implies c(0, L) = D;
  - s_L implies no D-edge has cyclic length > L;
  - at least one s_L holds.
- **Reflection.** The reflection i ↦ L−i (mod n) fixes {0, L}, preserves cyclic lengths, and swaps {0, L+1} with
  {L, n−1}. So we may also add s_L ⇒ c(0, L+1) ≤ c(L, n−1).

Empirical soundness test (`scripts/r1_sb_test.py`). It enumerates all solutions of SAT instances with a lowered
threshold, groups them into dihedral orbits, and checks that every orbit meets the SB formula:
- (7,4,{3,4}), threshold 7: 392 solutions in 42 orbits, 0 orbits missed;
- (9,5,{4,5}), threshold 8: 21,348 solutions in 1,280 orbits, 0 orbits missed.

These are also positive controls: the encoding is not vacuous.

### 1.4 Runs

Pipeline (`scripts/r1_run.py`, `r1_batch.py`, `r1_lowD.py`):
1. Build the CNF.
2. Solve with kissat 4 and write a binary DRAT proof.
3. Check the proof with **drat-trim**, the standard backward checker (built from github.com/marijnheule/drat-trim).
4. Delete the CNF and proof. They are regenerated deterministically by the scripts.

A case counts as done only on `s VERIFIED`. Every case is UNSAT and VERIFIED:

| instance | cases | solve time per case | proof size per case | drat-trim |
|---|---|---|---|---|
| (15,2..6,0) | 5 | ≤ 10 s | ≤ 3.7 MB | all VERIFIED |
| (15,7,5) | 21 rare pairs, SB | 7–15 s | 4–7 MB | all VERIFIED |
| (15,8,6) | 28 rare pairs | 8–56 s with SB (pairs containing 8 are the slow ones); {7,8} without SB: 282 s | 5–85 MB | all VERIFIED |
| (17,2..7,0) | 6 | ≤ 14 s | ≤ 18 MB | all VERIFIED |
| (17,8,6) | 28 rare pairs, SB | 7–12 s | 16–25 MB | all VERIFIED |
| (17,9,7) | 36 rare pairs, SB | 6–9 s, except pairs {r,9}: 179–739 s | 16–124 MB | all VERIFIED |

Independent re-run with a second solver: CaDiCaL instead of kissat, then drat-trim, on (15,8,{1,2}), (17,9,{2,3})
and (15,7,{3,7}). All UNSAT and VERIFIED (`scratchpad/R1/sat/reverify`).

Re-certification of n ≤ 13 through the same split pipeline (all UNSAT and VERIFIED):
- (7,4,·) and (9,5,·): all rare pairs;
- (11,6,·): 15 pairs;
- (13,7,·): 21 pairs.

This agrees with B3.

**Theorem 15/17.** For n ∈ {15, 17}, every strictly convex n-set has at least three distances occurring at most n
times. *Proof:* §1.1 together with the table. ∎

**Trust base.** We trust the CNF encoder, which is short: the Q part is identical to B3's order encoding, which B3
cross-validated against exhaustive enumeration and exact regular-polygon subsets. We also trust drat-trim, but not
the solver.

**Scaling.** The hard cases are always the rare pairs that contain the diameter colour: {r, m+1}.
- n = 13: about 30 s. n = 15: about 50 s. n = 17: 180–740 s.
- n = 19 looks feasible (hours per case). It still cannot reach all n.

## 2. Route A: geometry of the odd K = 1 configuration

**Setting (Prop B of angle_B2).**
- n = 2m+1 and D = m+1, with distances d_1 > … > d_{m+1}; d_1 is the diameter.
- Exactly two classes are rare: d_1 (a pairs) and one other (b pairs).
- The m−1 frequent classes have μ = 2m+2+e_d, and a + b + Σe_d = m+2.
- Hence a, b ≥ 2 (angle_B2 C1) and **a ≤ m**.

**Tools** (black boxes from Fishburn, Comput. Geom. 5 (1995), p. 69):
- Altman's Lemmas 1–3 on a convex q-gon with a maximal side.
- Fishburn's Lemma 6 (pp. 73–77).

### 2.1 Diameters and the case tree

**L1 (rank span, proved).** Suppose |ij| = d_s is maximal in its closed side S (the consecutive vertices from i to
j). Then |S| ≤ m+4−s, and |S| ≤ m+3−s if it is uniquely maximal.

*Proof.* Altman L1 gives D(S) ≥ |S|−2, or ≥ |S|−1 in the unique case. S only uses the distances d_s, …, d_{m+1},
which are m+2−s values. ∎

**L2 (diameters).**
- Every diameter has short span in {m−1, m}. This is angle_B2 C4, which rests on Altman 1972.
- Two diameters cross or share an endpoint.
- The halving chords {j, j+m} form the "star cycle".

**Case tree:**
- **A:** some diameter (1,q) has span m−1. Then the larger side Q = (1..q) has q = m+3 and D(Q) = q−2, so Altman
  L3 applies. Put C2 = (2..q) and C3 = (1..q−1).
  - **A1:** (2,q) is the unique d_1 in C2, and (1,q−1) is the unique d_1 in C3.
  - **A2:** otherwise. Then (3,q) = d_1 or (1,q−2) = d_1.
- **B:** all diameters are halving.
  - **B1:** some diameter g = (1,q), q = m+2, has no diameter star-neighbour. Then g is the unique maximum of Q,
    D(Q) = q−1, and Altman L2 gives |ij| = f(j−i) on the levels q..q+2.
    - **B1b:** the star-neighbour sides Q1 = (1..q−1) and Q2 = (2..q) have a unique maximum.
    - **B1a:** otherwise. By Lemma B1.4 below, this means |1k| = d_2 for some 2 ≤ k ≤ q−2, or the mirror
      statement.
  - **B2:** every diameter has a diameter star-neighbour, so the diameters form runs.

`scripts/r1_geo_cases.py` places the known (cocircular) D = m+1 sets R_{n+1}−1 and R_{n+2}−2 in this tree, with
exact chord indices.

### 2.2 Proved lemmas

**Lipschitz lemma (new).**
- Statement: let w lie strictly inside a circle G of radius R, and let B(α) = 2 arcsin(|w p(α)|/2R) be the
  "chord angle" of the point p(α) ∈ G. Then |B(α) − B(α′)| < |α − α′| for α ≠ α′.
- Proof:
  - With ρ = |Ow| and γ = α − arg w, B′ = ρ sin γ / (f √(1 − f²/4R²)).
  - The identity 4R²f² − f⁴ − 4R²ρ² sin²γ = (R² − ρ²)(3R² + ρ² − 4Rρ cos γ) holds (verified by sympy).
  - Its right-hand side is ≥ (R² − ρ²)(3R − ρ)(R − ρ) > 0, so |B′| < 1. ∎
- **Corollary.** Suppose w is inside G and sees two R_M vertices k steps apart at chord indices i, j. Then
  |i − j| < k. In particular, adjacent vertices at chord distance from w have equal chord index.
- Check: `scripts/r1_geo_lipschitz.py` (symbolic identity, and 2·10⁵ float trials with maximum ratio 0.9994).

**Arc rigidity (proved).**
- Statement: let V be s consecutive vertices on a circle G at step θ, with chord values c(1) < … < c(s−1) distinct.
  Let w ∉ V, with V ∪ {w} strictly convex, and suppose every distance from w to V is some c(j). Then one of the
  following holds:
  - w ∈ G;
  - w is the centre (a "fan");
  - s is even and w is on the axis through the middle edge, with the ranks running c(s−1), c(s−3), … or
    c(1), c(3), … outwards.
- Proof ingredients:
  - For two adjacent x, y ∈ V, the circle point with the same pair of chord distances lies on the same side of
    line xy, so a pair of consecutive ranks forces w onto G.
  - Otherwise the ranks jump by ≥ 2 along each monotone half.
- For s ≥ 6 both axis patterns are impossible:
  - pattern A: a quadratic in cos φ would need s/2 ≥ 3 roots;
  - pattern B: |w,1| ≥ sin((s−1)θ/2) > 2 sin(θ/2).

  (B1 sub-report. Scans: `scripts/r1_geo_arc.py`, `r1_geo_b1step.py`, `r1_geo_b1patternB.py`.)
- **Consequence.** If P contains s ≥ m+2 consecutive vertices of R_{2m+2} or R_{2m+3} as a contiguous block, then
  P is cocircular, so F = 0. This contradicts the configuration.

**Arc extension for R_{2m+1} (proved, m ≥ 4; frequency not used).** No convex P with D(P) = m+1 contains a contiguous
block U of m+2 consecutive R_{2m+1} vertices.
- U realises c_1..c_m, so there is one extra value x.
- Points beyond the end chord of U and outside G see some u ∈ U at distance > c_m = d_1.
- Off-vertex points on G would need all m+2 distances equal to x.
- Points inside G: f is unimodal along U, and the Lipschitz corollary allows ≤ 4 chord positions against the m
  needed.
- At m = 4 the one symmetric pattern is excluded exactly (residuals 0.63, −0.50, −1.98; `r1_geo_lipschitz.py` part 3).
- Check: `scripts/r1_geo_arcext.py`, m = 4..7.

**A1 (closed, conditional on Fishburn 1995 Lemma 6).**
- Altman L2 applies in C2 and C3.
- Fishburn L6 then makes Q = m+3 consecutive vertices of R_{2m+3}.
- Arc rigidity makes P cocircular, a contradiction.

L6's hypotheses are internal to Q, so it applies verbatim. **Gap:** L6's proof (pp. 75–77) has not been re-derived
here.

**B1b (closed, unconditional, all m ≥ 3; the "double ladder").**
1. Altman L2 holds on Q, Q1 and Q2 with the same f, so |ij| = f(j−i) on all levels q−1..q+3 except (1,q).
2. Induction from the middle outward: the block [a,b] lies equally spaced on a circle O, with f(w) = c(w).
   - The next pair x = a−1, y = b+1 are mirror images in the block axis.
   - Either the direction of x points into the block arc, which gives a contradiction by position (inside, on, or
     outside O),
   - or the distances from x along the block are strictly monotone. Then they are forced to be f(1..W), and x is
     the circle point.
3. So Q is a regular arc of q = m+2 points.
4. Arc rigidity with s = m+2 then puts P \ Q on O ∪ {centre}:
   - cocircular gives F = 0;
   - with the centre in P, only the radius class can be frequent, but m−1 ≥ 2 classes are frequent.
5. A 4·10⁵-point scan of the step finds only the circle point (`r1_geo_b1step.py`). Least squares at q = 7 finds
   only regular solutions (`r1_geo_b1ladder.py`).

   Remark: this re-proves Fishburn L6-type rigidity without Fishburn's L9. It also fills in a step Fishburn asserts
   without proof ("|x,b−2| > |a,b−2|").

**Lemma B1.4 (B1a normal form).** D(Q1) = q−3 is impossible: Altman L3 on Q1 and L2 on Q would give (2,q−1) both d_2
and d_3. So in B1a some d_2 pair of Q1 is (1,k), 2 ≤ k ≤ q−2, or the mirror statement holds at q.

**B2 partial results:**
- *B2-1 (proved).* The small side T_h of a halving diameter contains no other halving chord. Hence h is its unique
  maximum and D(T_h) ∈ {m, m+1}. For an interior run diameter, the uniqueness hypotheses of Fishburn L6 hold
  automatically.
- *B2-4 (conditional on L6).* No interior run diameter has D(U_h) = m: L6 plus arc extension. So in Case B every
  large side U_h realises all m+1 distances, and contains a pair of the second rare distance ρ.
- *B2-5 (conditional on Fishburn Thm 2, the D = m classification for 2m ≥ 8): a = 2 is impossible in B2.*
  - **⚠ GAP (found 2026-09-24 by the paper-v2 odd-n drafter, scratchpad/R4/v2/oddn/REPORT.md):** the case where the apex is outside the circle and the missing vertex is not under it is unjustified; the count then only gives m ≤ 5. Fishburn Thm 2 is published, so the label "conditional on Fishburn Thm 2" hides a real gap. Treat B2-5 as UNPROVED.
  - Deleting the apex leaves R_{2m} or R_{2m+1}−1.
  - The apex, inside G, is killed by the Lipschitz corollary; outside G, by rank jumps ≥ 2.
  - Checks: `r1_geo_apex.py`, and the positive control `r1_geo_apex_ctrl.py`.
- *B2-6 (conditional on the Erdős–Fishburn conjecture one level down; the adding-one-point step is proved for
  m ≥ 6).* When the diameters have a 2-vertex cover (a = 3, 4), B2 reduces to "a convex (2m−1)-gon with m distances
  is R_{2m}−1 or R_{2m+1}−2". That statement is known only up to 9 points.
- The true example R_{2m+3}−2, with m vertices between the holes, satisfies every local B2 condition, but it has
  a = 2m (`r1_geo_true_ex.py`). So **B2 cannot be closed locally; it must use a ≤ m**, i.e. the frequency
  hypothesis.

### 2.3 Remaining gap (route A)

1. **A2:** one or both of (3,q), (1,q−2) is a diameter. Erdős–Fishburn 1996 cases IB and IC kill this at m = 4
   only.
2. **B1a:** |1k| = d_2 inside Q1. Conjecture: every tight Altman-L2 ladder with q ≥ 6 is a regular arc.
   - Evidence: E–F 1996 Part II effectively does q = 6; a numerical search at q = 7 finds only regular solutions.
   - The q = 8 search had too little power.
3. **B2** with 3 ≤ a ≤ m and all runs of length ≥ 2. This needs a global argument that uses a ≤ m (and 3-fans), not
   more local rigidity.
4. Re-derive Fishburn L6, so that A1 and B2-4 become unconditional.

## 3. Route B (human proof of Q-ORD)

An ordinal sub-agent explored a human proof. It tried an ordinal Altman argument, top-class structure, cores and
profiles (`scripts/r1_ord_*.py`, not committed). It was lost to an outage before reporting, and **no ordinal lemma
from it is claimed here.**

Observations that stand on their own:
- the hard rare pair is always {r, m+1}, i.e. the diameter colour together with any other colour (§1.4);
- angle_B3's deletion-minimal cores (25 of 35 quadrilaterals at n = 7) suggest the argument must be global.

## 4. Next steps

1. **n = 19 by SAT:** 45 hard-ish cases (D = 10). The 9 pairs {r,10} probably take about an hour each on one core,
   with drat-trim proofs of about 0.5 GB each. They must be deleted as they go; watch disk.
2. **Route A:** re-derive Fishburn L6 by the double-ladder method of B1b, which already handles the analogous
   L2/L2 situation. That would make A1 and B2-4 unconditional. Then attack B1a (the ladder conjecture) and the
   global B2 argument using a ≤ m.
3. **Route B:** mine the {r, m+1} refutations, i.e. what the diameter colour forces, for an inductive ordinal
   lemma.

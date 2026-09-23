# Second independent referee report: WRITEUP_A2.md (min{μ(Δ₂), μ(δ)} ≤ (54/37)n + C₀)

Date: 2026-09-23. I read WRITEUP_A2.md in full and formed my verdict before opening REFEREE_A2.md. I did not use angle_A*.md or the earlier scripts. Every step of §7.2 and §8 was rebuilt by hand. New scripts:

- `scripts/ref2_ownership.py`: exhaustive exact check of the §7.2 bookkeeping, in the abstract model the argument uses. Includes mutation tests.
- `scripts/ref2_numeric.py`: 40 assertions, all in exact rationals or one-sided rational bounds (√3, π, sin, cos, arcsin). Covers the LP, every Region I/II/III threshold, the §5 constants and the §8 constants. It also runs an adversarial float search on (R1), (R2) and (R2-sym); that search is reported only, never asserted.
- `scripts/ref2_degen.py`: adversarial search on §8 Step 4. It builds star sets in which ≥ 3 W-circles pass through one vertex of ∂K, so the degenerate-arc case is really tested.

## Verdict: **CORRECT** (minor cosmetic points only)

- I found no counterexample, no false lemma and no case split that misses a case.
- The two parts flagged as least standard, the §7.2 ownership/pairing and the §8 Step 4 incidence count, are both correct as written.
- The only external dependency is [Ve87]. A second source confirms its statement (see below).

## §7.2 ownership/pairing, rebuilt line by line

**Inputs.** The counting argument uses only these facts:
1. Each row (K-row = S∖D, D-row = S∩D) with its pure T-edges is a disjoint union of directed paths and cycles, and every cycle has length ≥ 3. This follows from (T1), (T2) and the absence of 2-cycles: a T-neighbour is never on the line ℝu_p, so v₀ cannot be both the left and the right neighbour of v₁.
2. (R1): the rungs form a matching.
3. (R2) and (R2-sym).
4. A rhombus forces parallel rungs, so there are no rhombi when τ < cos(β/2). There are never three parallel rungs, so two consecutive rhombi cannot occur.

**Geometric inputs, re-derived.**
- *Offsets.* o_σ(u) is linear in u and τ² + s² = 1, so it is a rotation. For σ ≠ σ′: |o_σ(u) − o_σ′(u′)| ≤ 2s + |u − u′|.
- *(R2).* The decomposition z′ − z₁ = (e₁ − e₂) + (o_{σ₁}(u_{v₁}) − o_{σ₀}(u_{v₀})) is correct. The bound is 2s + 2β + arcsin β.
- *(R2-sym).* The decomposition v′ − v₁ = (e₂ − e₁) − (o_{σ′}(u_{v′}) − o_{σ₀}(u_{v₀})) is correct. The angle chain v′ → z₁ → z₀ → v₀ gives ≤ 3β. The bound is 2s + 4β + arcsin β.
- *Exact check.* At τ ≥ √3/2 + 3β we have s² ≤ 0.19714. [numeric §II] then verifies exactly: 2s + 2β + arcsin β < 1, 2s + 4β + arcsin β < 1, and the stated 2s + 6β < 1.
- *Adversarial maxima.* R2 = 0.897, R2-sym = 0.914, R1-at-z = 0.906. All are below 1 and below the stated bounds.
- *Rhombus ⇒ parallel.* v₁ and z₀ lie in different rows, so they are distinct points of C(v₀,1) ∩ C(z₁,1). Hence v₀ + z₁ = v₁ + z₀.
- *Parallel rungs.* Parallel rungs force c·u = −τ for both K-ends. Lemma 3.3 makes the normals distinct, so the angle between them is exactly 2θ₀. A good T-edge then forces 2θ₀ ≤ β, i.e. τ ≥ cos(β/2).
- *No three parallel rungs.* This follows from Lemma 3.3 again: only two unit u solve c·u = −τ.

**Bookkeeping.**
- Ownership is well defined. A vertex belongs to the nearest rung vertex at or to its left on its path or cycle. Since rungs form a matching, that rung vertex belongs to exactly one rung.
- edges(r) = 1 + k + d − [K-walk stops] − [D-walk stops].
- Each unowned vertex carries only its right T-edge.
- A both-reach gap cannot be (1, ≥2): by (R2) it would be (1,1).
- A both-reach gap cannot be (≥2, 1): by (R2-sym) it would be (1,1).
- A cycle with a single rung vertex is a both-reach gap with k equal to the cycle length, which is ≥ 3. That case is handled correctly.
- Pairing:
  - A rhombus rung's successor always exists (v₁ is a rung vertex).
  - The successor is never a rhombus rung. Otherwise r₀, r₁, r₂ would be parallel; v₂ ≠ v₀ because there are no 2-cycles.
  - The pairing is injective, since v₀ is the unique left neighbour of v₁.
  - Pair ratio ≤ max{8/6, 5/4} = 4/3.

**Exhaustive check** (`ref2_ownership.py 6`). All row structures up to isomorphism with |K-row|, |D-row| ≤ 6, all partial rung matchings, exact Fractions.
- 2,365,426 admissible configurations in the generic mode (no rhombi): max e/|S| = 5/4.
- 2,741,183 admissible configurations in the resonant mode: max e/|S| = **4/3**, reached by two 3-cycles with a rhombus and a (2,2) successor.
- The script also recomputes the write-up's charging and asserts the other claims: the gap dichotomy, that charged edges sum exactly to E, that a successor is never a rhombus, the injectivity, and the per-rung and per-pair ratios. There is no additive constant.

**Mutation tests** (to check that the hypotheses are load-bearing).
- Drop the no-two-consecutive-rhombi rule: two 3-cycles with 3 rungs give 9 edges on 6 vertices (3/2 > 4/3).
- Drop (R2-sym): a both-reach (2,1) gap appears.

Both rules are therefore needed, and the write-up proves both. To reproduce, run `ref2_ownership.py 4` after one of these edits:
- replace `if mode == 'resonant' and any` with `if False and any`;
- replace the R2-sym line `if z1 in Minv and Minv[z1] != v1: ok = False; break` with `pass`.

**Verdict for §7.2: CORRECT.**

## §8 Step 4 (and Steps 1–3), rebuilt

**Step 1.**
- The parallelogram identity Σ|a−b|² = 2Δ² + 4|m−m′|² is correct.
- "At least two cross distances are Δ" splits into two cases: the two cross pairs are disjoint, or they share a point. The split is exhaustive.
- *Disjoint pairs.* Given x and z′, the points z and x′ are the two points of C(x,Δ) ∩ C(z′,Δ). So the four points form a genuine rhombus, and the parallelogram law applies.
- *Shared point.* The fourth point is confined to the 60° arc. The margin 2 − √3 = 0.26795 > 1/1.94² = 0.26570 is thin but verified exactly.

**Step 2.**
- A graph with no two disjoint edges is a star or a triangle.
- A triangle plus a 4th point would need Δ₂ ≥ circumradius Δ/√3. This fails because q < 1/3.

**Step 3.**
- Lens bounding box: diagonal² < 0.0036 + 0.2364 < 1 (exact). So diam K < Δ₂.
- A-chords subtend < 30° at y, so A lies in a short arc, and a Δ₂-pair inside A must be the unique extreme pair.

**Step 4.**
- *Single arc.* For x ≠ w, C(w,Δ₂) ∩ D(x,Δ₂) is an arc of length ≤ π, or empty. It is the whole circle when x = w; this is harmless and not mentioned. An arc of length ≤ π that contains two non-antipodal points contains the minor arc between them. So J_w is minor-arc-convex with spread < 60°, hence a single closed arc.
- *No point interior to two arcs.* f(θ) = |w−w′|² + 2Δ₂ e(θ)·(w−w′) has an interior local maximum 0 at b. A local maximum of a cosine is its global maximum |w−w′|² + 2Δ₂|w−w′|, which is > 0. Contradiction. This is a cleaner form of the tangency argument.
- *Nondegenerate arcs are interior-disjoint subarcs of ∂K.* So at most two meet at a point, one on each side.
- *Where K has nonempty interior.* An open chord between two points of K lies in the interior of every disc. So K is a point, or empty, or has nonempty interior; in the first two cases |B| ≤ 1 and the bound is trivial.
- *Injective map.* "b ↦ the arc starting at b clockwise" is injective, because each arc has one clockwise start.
- *Totals.* Degenerate arcs contribute ≤ 1 incidence each. So I ≤ |B| + |W|, and μ(Δ₂) ≤ 1 + I ≤ n + 1.

**Adversarial search** (`ref2_degen.py`). New A-points are placed on C(y,1) ∩ C(b,Δ₂) for current vertices b, which forces many concurrent W-circles and so exercises the degenerate-arc case.
- 4000 + 1500 configurations; 1477 of the 1500 had a vertex on ≥ 3 W-circles.
- Max μ(Δ₂) − n = **0**, against the claimed ≤ 1.
- The equality classification is unambiguous: the smallest non-coincidence gap was 3.7·10⁻⁵ against a tolerance of 10⁻⁹.

**Verdict for §8: CORRECT.**

## Per-item table

| item | verdict | notes |
|---|---|---|
| Lemma 3.1, 3.2 (a)(b)(c), 3.3 | VERIFIED | (c) identity re-derived: a = (1 − t² − 2Δ₂t)/(2Δ₂) = −τ |
| Good-edge dichotomy (τ > 2β) | VERIFIED | exhaustive: an exception target is in D, and D-points see everything as normal |
| (T1), (T2), no 2-cycles | VERIFIED | |
| Lemma 3.4 (multiplicity) | VERIFIED | |
| (VS) via Ve87 / Hopf–Pannwitz, and for S′ ⊂ S | VERIFIED | |
| (E), Lemma 4.1 (LP → 9/(7.5−k)) | VERIFIED exactly | k = 4/3 → 54/37. The LP is tight for these inputs: the adversary takes s = 36n/37 |
| Lemma 4.2 (7/5) | VERIFIED exactly | 1.4s + 0·p + 1.2r |
| Small cases, N₀ < 1.51·10⁹ | VERIFIED | |
| Lemma 5.1 (lens), 5.2 (≤ 2ρ₀) | VERIFIED | Proof re-derived: MVT with ξ ∈ (φ₀/2, φ₀); opposite signs give ≥ 2 > 1; perimeter monotonicity. *Cosmetic:* the KK threshold is 89.001, which the write-up rounds to "89.0". It is irrelevant because R = Δ₂ ≥ 10⁴ |
| KK, DD, (c1), (c2) counts; total < 1.83·10⁷ | VERIFIED | Exact total ≈ 1.8280·10⁷. (c2) α ≤ 151.9° re-derived (cos α ≥ −0.88199) |
| Region I (18/13) | VERIFIED exactly | cos(A+B) > 1/2 certified in rationals |
| Lemma 7.1, #mixed-T < 71 | VERIFIED | Needs Θ < π/3, which holds because t ≤ 1 wherever rungs exist |
| (R1), (R2), (R2-sym), (R3) | VERIFIED | Exact bounds < 1. Adversarial maxima: 0.906, 0.897, 0.914 |
| §7.2 ownership / pairing → 4/3 and 5/4 | VERIFIED | Exhaustive check up to 6+6 (5.1M configs), with mutation tests |
| §7.3 corner lemma, ≤ 6 corners, 7/5 | VERIFIED | Case split \|zw′\| ∈ {Δ} ∪ [0,Δ₂] is exhaustive. 2θ₀ > 52.7° and 90° − θ₀ > 57.7°, both > 51.43° |
| §8 Steps 1–4, μ(Δ₂) ≤ n + 1 | VERIFIED | Adversarial max μ(Δ₂) − n = 0 |
| Regime coverage | VERIFIED | τ-intervals partition ℝ; degenerate/nondegenerate split exhaustive; n ≤ 3 trivial |
| [Ve87] statement | CORROBORATED | see below |

## [Ve87]

- **ScienceDirect** (pii 0012365X87900276) was not readable.
- **CDL.** arXiv 2505.04283 v5 (local copy `novelty_sources/a2_cdl_v5_html_20260923.txt`, line 284) cites ref. [23] for the claim that the second-largest distance among any n points in the plane occurs at most 3n/2 times. Its [22] is the convex 4n/3 paper. The write-up's §10 item 6 is therefore right, and REFEREE_A2's "citation mismatch" is mistaken, at least for v5.
- **Independent second source.** J. Pach, "Finite point configurations", *Handbook of Discrete and Computational Geometry*, 3rd ed., ch. 1 (csun.edu/~ctoth/Handbook/chap1.pdf). It lists the maximum number of occurrences of the second-largest distance as 3n/2 (if n is even), citing Vesztergombi, *On large distances in planar sets*, Discrete Math. 67:191–198. The bibliography misprints the year as 1978. This phrasing states the exact maximum (⌊3n/2⌋, sharp), with no n₀ and no additive term.
- The write-up's usage (3m/2 + C_V, for any m) is therefore plausible and safe.

## Comparison with REFEREE_A2.md (read only after the above)

- **Agreement.** REFEREE_A2 also found no counterexample, and I agree on every VERIFIED item. The write-up closes all of its GAP items, and I checked each closure:
  - symmetric (R2);
  - (c2) α ≤ 151.9° and the corner cone;
  - KK constant;
  - Lemma 7.1 restricted to Region II;
  - Δ ≤ 1.94Δ₂;
  - lens-corner length.
- **Differences.**
  1. REFEREE_A2's citation-mismatch item is wrong for CDL v5; the write-up is right.
  2. Its degenerate search reached max μ(Δ₂) − n = −3. My concurrency-forcing search reaches 0. This is still within the claimed n + 1, but the bound is closer to tight than the first report suggested.
  3. I add an exhaustive exact check of the ownership combinatorics, plus mutation tests showing that (R2-sym) and the no-three-parallel-rungs fact are both necessary. The first referee checked this by hand only.

## Residual caveats (none affects correctness)

- Nobody has seen [Ve87] itself. It is corroborated by two independent secondary sources, and any additive constant or threshold on m is absorbed anyway.
- Cosmetic points in the write-up:
  - "89.0" should be 89.01.
  - The (R1)-at-z bound is written as "2βτ + 2s"; 2s + 2β is cleaner.
  - §8 "arc of length ≤ π" silently excludes x = w.
- The argument is a hand proof. It has not been formalised.

# Erdős #885 — factor-difference sets, case k = 5

**Question (open).** D(n) = {b − a : n = ab, 1 ≤ a ≤ b}. For every k, do there exist N₁ < … < N_k with
\|D(N₁) ∩ … ∩ D(N_k)\| ≥ k? Known for k ≤ 4 (ErRo97, Ji99, Bremner IJNT 2019). A k = 5 witness would be a finite,
Lean-decidable **partial result** (a new case), not a resolution.

**Status:** IN PROGRESS (un-parked 2026-09-25 at the user's request).

## Openness evidence
- 2026-09-23: erdosproblems.com/885 OPEN, 0 claims; formal-conjectures 885.lean main thm `research open`,
  k = 2, 3, 4 variants solved; not on Tao's AI wiki. (Full notes in ../../NOTES.md, "Triage batch 700–949".)
- 2026-09-25 thread recheck: still no k = 5. Aleksanndr_NFA (23 Sep, AI-assisted, Claude) searched the genus-1
  quartics y² = t⁴ + (2A−4B)t² + A² (row heights ≤ 2000, fourth-column heights ≤ 800): many k = 4, no k = 5.
  Their small k = 4: N = 515504, 3542528, 6010004, 19523504; d = 872, 4328, 5003, 11672. Lean k = 4: FC PR #6509.

## Reformulation
d ∈ D(N) ⇔ x + d² = s² with x = 4N. So we need a 5 × 5 array: x₁…x₅ and d₁…d₅ with every x_i + d_j² a
square. Any integer solution x gives a witness N_i = x_i with differences 2d_j.
For two differences d_a < d_b sharing x: s_b² − s_a² = d_b² − d_a² =: Δ, so the shared x are **finitely many**
and come from factorisations Δ = uv. For fixed d₁…d₅ the admissible x lie on a genus-17 curve
(4 quadrics in P⁵). For fixed x the admissible t (d = (x/t − t)/2) form the genus-1 curve y² = t⁴ + (4x−2)t² + 1
(with x₁ normalised to 1).

## Searches
| script | method | range | result |
|---|---|---|---|
| scripts/s885.c, s885l.c (2026-09-23) | pivot N₁, columns D(N₁), rows N = b(b+d), b ≤ B | N₁ ≤ 2e6 (τ-rich), B = 2e4; 1600 smooth N₁ ∈ [5e7, 1.4e9] | 15 k = 4, 0 k = 5 |
| scripts/dpair.c (2026-09-25) | pivot = smallest common d; all shared x from factorising Δ; N unbounded | see logs/ | see below |

`dpair g M part nparts`: candidate differences d = g·m, m ≤ M. With **g = 1 it is complete**: every k = 5 witness
whose five common differences are all ≤ M (in the x = 4N normalisation) is found, for any N.
With g > 1 it searches rational x with denominator dividing g².
Validation: g = 168, M = 1000 recovers Bremner's k = 4 example (d/168 = 30, 165, 410, 982;
x = 4·65984625, …) in 17 s.

**⚠ 2026-09-25 incident:** the first M = 50000 launch (8 parallel `dpair` jobs) crashed the Mac twice (kernel
panics 11:02 and 11:07, 17–22 GB RSS on 16 GB). Cause: `dpair` enumerated every 4-subset of each row's partners
(C(c,4) keys; rows with c ~ 100+ at M = 50000). Fix: `dpair2.c` finds row-sets by inverted-index intersection
(memory O(pairs); measured 48 MB peak at the heaviest pivots of M = 50000), in-process cap DPAIR_MEMCAP_MB,
`watchdog.sh` RSS kill, `run_g1.sh` runs ≤ 2 jobs at once. **Never run old `dpair` with large M.**

## Results
Near-miss counters (added 2026-09-25): K₅,₄ = 5 N's sharing a k=4 difference set; K₄,₅ = 4 N's sharing 5 differences.

| run | pairs | K₄,₄ | K₅,₄ | K₄,₅ | K₅,₅ |
|---|---|---|---|---|---|
| g = 1, all d ≤ 12000 (**complete**, 33 min × 8 cores) | 1.26e9 | 13 (10 up to scaling) | 0 | not counted | **0** |
| g = 1, all d ≤ 50000 (**complete**, dpair2, 2 jobs at a time, ~3.5 h) | 2.9e10 | 181 row-sets* | **1** | 0 | **0** |
| g = 2520, m ≤ 1000 | 4.1e8 | 11 | 0 | 0 | 0 |
| g = 5040, m ≤ 1000 | 5.4e8 | 12 | 0 | 0 | 0 |
| g = 10080, m ≤ 1000 | 6.7e8 | 12 | 0 | 0 | 0 |
| g = 27720, m ≤ 1000 | 1.1e9 | 14 | 0 | 0 | 0 |
| g = 55440, m ≤ 700 | 6.8e8 | 5 | 0 | 0 | 0 |
| g = 720720, m ≤ 250 | 1.9e8 | 0 | 0 | 0 | 0 |

(g = 1 run predates the near-miss counters; its K₄,₄ lines all have rows = 4, so K₅,₄ = 0 there too.)

\* dpair2 counts 4-row sets (a K₅,₄ contributes 5), not distinct 3-subset keys.

**Theorem (computational, 2026-09-25):** no k = 5 witness has all five common differences ≤ 50000
(in the x = 4N normalisation; N unrestricted). Not Lean-checked; the search is exhaustive by the factorisation argument above.

**★ Near miss K₅,₄ (found 2026-09-25, verified in gp from the definition of D):** five numbers whose
difference sets share four elements:

    N = 10046592, 24561225, 115706752, 281637972, 564578560
    D(N_1) ∩ … ∩ D(N_5) = {5976, 10104, 24216, 69624}   (exactly these four)

(x-form: x_i = N_i, d = 2988, 5052, 12108, 34812 = 12·{249, 421, 1009, 2901}.) Aleksanndr_NFA's search (forum,
23 Sep 2026) reported *no* five numbers sharing four differences within their height bounds. In sumset-of-squares
language this is a 6 × 4 array; Choudhry (arXiv 2508.07806) lists parametric (3,3), (5,3), (4,4) only.
Novelty not yet audited. Rational 5th-column search for it (q ≤ 1e6): logs/ext54/.

**Rational extension of the 32 distinct 4×4 configurations (ext.c, q ≤ 1e5, all 32):** 6.9e9 divisor
candidates, 223 filter survivors, **0 genuine** after exact gp verification (verify_ext.py).

**Observation:** besides the one K₅,₄, none of the ~80 K₄,₄ configurations extends by a row or column.
Height heuristic: #K_{m,n} of height ≤ H ≈ H^{m+n−1−mn/2}, i.e. H^{−3.5} for 5 × 5 (and H^{−1} already for 4 × 4,
which nevertheless exist only sporadically, with no known parametric family). Blind search for K₅,₅ looks hopeless. A witness would need a structured family: curves with extra
automorphisms, or a parametric K₄,₄ family whose genus-5 extension curve has a rational point.

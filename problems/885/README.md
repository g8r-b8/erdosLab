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

## Results
(filled in as runs finish)

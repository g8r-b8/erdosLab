# Erdős #132 / CDL Problem 1.6 — Angle R4: improving L ≤ 54/37

Date: 2026-09-23. Status: IN PROGRESS (skeleton; sections marked TODO are being filled).
Scratch: `scratchpad/R4/`. Scripts: `scripts/r4_*.py`.

Notation and numbering follow `WRITEUP_A2.md` (δ = 1, β = 1/100, t = Δ − Δ₂, τ = t − (1−t²)/(2Δ₂),
θ₀ = arccos τ, s = sin θ₀, K = ∩_{w∈X} D(w,Δ₂), D = diametral endpoints, S = points with a Δ₂-partner,
R = X∖S, r = |R|, u_p, K-row = S∖D, D-row = S∩D, T-edges, rungs, ownership).

## 1. Where 54/37 loses (diagnosis)

| regime | e(S) bound used | LP | value |
|---|---|---|---|
| I: τ ≤ √3/2 − 2β | \|S\| + C | Lemma 4.1, k = 1 | 18/13 |
| III: √3/2 − 2β < τ < √3/2 + 3β | \|S\| + 2\|P₁\| + C | Lemma 4.2 | 7/5 |
| II-rest: √3/2 + 3β ≤ τ < cos(β/2) | (5/4)\|S\| + C | Lemma 4.1 | 36/25 |
| II-near-resonant: cos(β/2) ≤ τ ≤ 1 | (4/3)\|S\| + C | Lemma 4.1 | **54/37** |
| II-high: τ > 1 | \|S\| + C | Lemma 4.1 | 18/13 |

Two separate losses:
1. **Rungs are charged without their Δ₂ cost.** In Region II every "extra" δ-edge (a both-reach rung,
   ratio 5/4 or 4/3) sits at a K-vertex whose Δ₂-degree is 1 (Lemmas A–C below), so it is paid for on the
   μ(Δ₂) side exactly as in Lemma 4.2. Fixing this removes 54/37, 36/25 and (almost all of) 7/5.
2. **The term 6r** in (E) μ(δ) ≤ e(S) + 6r. This is the whole gap between 18/13 and 9/7: in ienjoymath's
   construction e(S) = |S| and the patch points contribute 3 each, not 6. Exact identity:
   μ(δ) = e(S) + Σ_{y∈R}(deg y + m_y)/2, m_y := #δ-neighbours of y in S.
   With e(S) ≤ |S| + |P₁|, a bound deg y + m_y ≤ 2c (all but o(n) y) gives 1.5c/(c + 1/2):
   2c = 12 → 18/13, 10 → 15/11, 9 → 27/20, 8 → 4/3, 6 → 9/7.

## 2. Region II gives 18/13 (PROVED; referee-verified)

TODO: final text.

## 3. Region III gives 18/13 for τ ≠ √3/2 (PROVED, pending referee); τ = √3/2 exactly

TODO.

## 4. Consequence

TODO.

## 5. Beyond 18/13: the 6r term (local R-neighbour lemma; global Euler route)

TODO.

## 6. Tests on ienjoymath's construction

TODO.

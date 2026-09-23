# Referee report on angle_A2.md (Theorem A2: min{μ(Δ₂), μ(δ)} ≤ (54/37)n + C₀)

Date: 2026-09-23. Adversarial referee pass. I read angle_A.md and angle_A2.md in full, re-derived each step by hand, and wrote independent scripts:
- `scripts/ref_checks.py`: rung identity, independent LPs, lens lemma, R1/R2 bounds, corner lemma, (c2) angle, exact single-centre strip.
- `scripts/ref_degen.py`: degenerate regime.

## Overall verdict: **CORRECT WITH FIXABLE GAPS**

I found no false lemma and no counterexample. Every inequality I checked holds, often with room to spare. The gaps are all expository or arithmetic: missing symmetric cases, a threshold that is used silently, and one wrong constant that does not affect the conclusion. None threatens 54/37. The argument is still at the level of careful notes. A full write-up must spell out the items marked GAP below.

## Black box [Ve87] and how it is applied to S

- **Source.** K. Vesztergombi, *On large distances in planar sets*, Discrete Math. 67 (1987) 191–198. As quoted in the introduction of arXiv:1103.0412: "In 1987 Vesztergombi showed that the second-largest distance d₂ can occur at most 3/2·n times". The statement is for arbitrary n-point planar sets. Her 1985 paper (Discrete Math. 57) is the convex-position 4n/3 result.
- **Citation mismatch.** CDL (arXiv 2505.04283) attributes the 3n/2 bound to its ref. [22], which is the 1985 paper. The notes say "[23]". Fix the citation. The mathematics is unaffected.
- **I could not read the original.** If its exact form is 3m/2 + O(1), that is absorbed into C₀.
- **The application to S is sound (VERIFIED).** All Δ₂-pairs lie in S, by definition.
  - If S contains a diametral pair of X, then diam S = Δ. Because X has no distances in (Δ₂, Δ), Δ₂ is the second-largest distance of S, and Ve87 applies.
  - Otherwise every distance in S is ≤ Δ₂, so Δ₂ is the largest distance of S, and Hopf–Pannwitz gives ≤ |S|.
  - Both cases are covered, and each gives ≤ 3|S|/2.
  - The same argument applied to S∖P₁ (Region III) is also valid.
  - The definitions are used consistently: no Δ₂-pair ever leaves S, and edges with an endpoint in R are charged to 6r.

## Per-item verdicts

| item | verdict | notes |
|---|---|---|
| (E) μ(δ) ≤ e_δ(S)+6r | VERIFIED | |
| Lemma 1.1, 9n/(7.5−k) | VERIFIED | Exact rational recomputation and scipy agree: k=1 → 18/13, 5/4 → 36/25, **4/3 → 54/37**, 7/5 → 90/61. |
| Region III LP → 7/5 | VERIFIED | Exact computation and scipy agree: optimum at s=1, p=1/5. |
| Lemma 2.1, rung identity | VERIFIED | Hand derivation: (z−v)·u = (1+Δ₂²−Δ²)/(2Δ₂) = (1−2Δ₂t−t²)/(2Δ₂) = −τ. Also checked with exact rationals, and numerically to 1e−12. |
| Lemma 2.2 (no common normal) | VERIFIED | Exception targets lie in D, so two points of S∖D are mutually "normal". |
| Good/bad dichotomy (T-edge vs rung) | VERIFIED | Uses \|a+b\| ≤ \|u_p−u_q\| ≤ β. Exception sources are in S∖D and exception targets in D. |
| (T1), (T2) | VERIFIED | |
| Lens lemma | VERIFIED | Proof checked (the x-coordinate bound gives cos φ − cos φ₀ ≤ 1/Δ₂). Tested on 3000 lenses including tiny centre distance d ∈ [1,5]: worst ratio 0.66, no violation. |
| KK bad-edge count | GAP (arithmetic) | 12π(4ρ₀+5)/β with ρ₀ = 8.2 is ≈ **1.4·10⁵**, not 4.4·10⁴. Still far below C_bad ≤ 10⁸. |
| DD bad-edge count, (c1) | VERIFIED | Corner angle φ₀ ≥ 60°, ρ₀ = 2. For (c1), the normal cone at z is > β/2 wide. |
| (c2) | GAP (fixable) | (i) It needs \|e₀·g\| = sin α ≥ sin(β/2), so α = ∠(u_v, g) must stay away from π. This follows from \|x_z w_v\| ≤ Δ ≤ 1.94Δ₂, which gives α ≤ 151.9° (ref_checks §6), but the notes do not say so. (ii) At a corner v, the "turning" must include the part of v's normal cone beyond u_v, because the one-sided tangent need not be ⊥ u_v. State this. |
| Turning-measure bookkeeping (§3, §5.1) | VERIFIED | Endpoint atoms included. Multiplicity ≤ (#points within arc-distance L) × degree. Mixed-T count 2·2·3·2π/0.886 ≈ 85 < 90. |
| §5.1 threshold "t ≥ 0.87" | GAP (cosmetic) | §5 is headed "Regions II and III", but Region III only has t > 0.846. Region III never uses §5.1 (T1 alone bounds all T-edges by \|S\|), so nothing breaks. Restrict the statement to Region II. |
| Region I | VERIFIED | One-side arcs are 58.35° and 58.87°, both < 60°. The τ ≤ 0 case also works. |
| (R1) | VERIFIED | Adversarial maximum 0.914 against the claimed bound 0.918. |
| (R2) | VERIFIED | Adversarial maximum 0.897, bound 0.933. |
| Symmetric (R2) (d=1 ⇒ k=1) | GAP (fixable) | "Symmetrically" is asserted but not proved. The analogue is \|v′ − v₁\| ≤ 2s + 6β = 0.948 < 1, and the adversarial maximum is 0.914. Write it out. |
| (R3): rhombus ⇒ parallel rungs ⇒ 2θ₀ ≤ β; no 3 parallel rungs | VERIFIED | |
| Ownership / pairing → (4/3)\|S\| | VERIFIED | Both-reach gaps are (1,1) or (≥2,≥2). A rhombus successor is never a rhombus rung (else 3 parallel rungs). The worst pair is a rhombus rung (3 edges, 2 vertices) plus a (2,2) successor (5 edges, 4 vertices), giving 8/6 = 4/3. Non-both-reach gaps have ratio ≤ 1. Rungs whose D-end lies in R are correctly excluded. A T-cycle cannot have length 2. |
| Near-resonant regime | VERIFIED + example | An exact single-centre strip at Δ₂ = 10³ and 10⁴ has 2θ₀ = α exactly, rhombi at every other rung, and unit edges 99/80 → 5/4 ≤ 4/3. Rung dot products are exact. I found no configuration with e(S) > (4/3)\|S\| + C. |
| Region III corner lemma, 7/5 | VERIFIED | Minimum angle 52.72° > 51.43°, so ≤ 6 exceptional corners. ≤ 2 rungs per K-vertex. |
| Degenerate regime, μ(Δ₂) ≤ n+1 | VERIFIED | Parallelogram identity checked. 2Δ sin 15° = 0.5176Δ > Δ/1.94 = 0.5155Δ: the margin is thin but valid. Star or triangle argument OK. The spindle-convexity "one arc" claim and the incidence count Σdeg ≤ \|B\| + \|W\| both check. 2403 adversarial star sets (all corners of K plus arc points): max μ(Δ₂) − n = −3. |
| Regime coverage | VERIFIED | τ is global and the τ-intervals partition ℝ. τ > 1 ⟺ t > 1. The nondegenerate/degenerate split at Δ = 1.94Δ₂ is exhaustive. |
| Small cases | VERIFIED | Nondegenerate with Δ₂ < 10⁴ gives Δ < 1.94·10⁴, so n = O(1) by packing. Degenerate needs only n ≥ 4. |
| Table cosmetics | GAP (cosmetic) | "all τ > 1" is listed under "II rest" but is also inside "τ ≥ cos(β/2)". There are no rungs there anyway, so e(S) ≤ \|S\| + C. |

## Caveat on the "Δ ≤ 2Δ₂" remark

The notes say that "If Δ₂ < Δ₀ then Δ ≤ 2Δ₂ is bounded." That is false for general sets. A point plus a short arc of its diametral partners has Δ ≫ Δ₂. It is true in the nondegenerate regime, which is where the remark is used, so reword it to "Δ ≤ 1.94Δ₂".

## What would still be needed for publication

1. Write out the symmetric (R2).
2. State the α ≤ 152° bound in (c2), with the treatment of the corner cone.
3. Correct the KK constant.
4. Fix the Vesztergombi citation, and ideally check the original 1987 statement for any n₀ or additive term.
5. Write the lens-corner curvilinear-triangle length bound (≤ 2ρ₀ + 1) explicitly.

# Paper v2: branches considered (2026-09-24)

Paper v2 upgrades the main theorem from 54/37 to 15/11 (4/3 in Region II), extends convex position to
6 ≤ n ≤ 18, and adds the almost-cocircular theorem. At each presentation crossroad one draft per branch was
written, and the drafts were compared. The drafts are kept in `v2_branches/`.

## Crossroad 1: how to present the proof of Theorem 1
| branch | file | outcome |
|---|---|---|
| **restructured** (chosen) | `v2_branches/paper_v2_restructured.tex` | §§2–8 rebuilt around 15/11: reductions (exact identity, LP), bad edges, nondegenerate regime (Region I; common facts; Region II via Lemmas B, C; Region III incl. τ = √3/2), points without a Δ₂-partner (Theorems N1, N2), degenerate regime, assembly. The 54/37 ownership/pairing argument, which is what Lean formalises, moves to Appendix B. 33 pp as drafted. |
| warmup | `v2_branches/paper_v2_warmup.tex` | keeps the 54/37 proof intact as Theorem 1′ (§§2–7), then "From 54/37 to 15/11" (§§8–11). Also 33 pp. |

**Why restructured:** it matches the requested restructuring and states the headline theorem first. Every 54/37-only
component (R2, R2-sym, rhombi, ownership, the 7/5 Region III count) is isolated in an appendix labelled as the
formalised argument, so the Lean section still has an exact written counterpart.

**Merged in from warmup:** in the flat-case lemma and Theorem N2 the parameter range is narrowed to
0 < ε₀ ≤ 1/50. The source's range ε₀ < π/6 is too wide: the step 232 cos ε₀ > 231 needs ε₀ < 5.3°. Only
ε₀ = 1/50 is used, so no result changes.

**Not merged:** warmup drops step (R) ("rows are cyclic orders") at τ = √3/2 and counts breaks by left ends instead.
This is a valid simplification, but it has had no referee pass, whereas (R) is the refereed route.

**Drafter-flagged steps (new wording, not seen by a referee):** in the chosen text, "Small rows" and
"Rotational sense" in Region III (c), and the Lemma C angle condition 3θ₀ + ε < π/2. The script
r4_regionII_checks.py asserts the source's equivalent-purpose condition instead, and the appendix says so. The
coordinator checked all three.

## Crossroad 2: odd-n partial geometric results (angle_R1 §2)
| branch | file | outcome |
|---|---|---|
| exclude (chosen) | — | the paper keeps only the certified n = 15, 17 and the (existing) reduction to the configuration D = m+1, k = 2 |
| include | `v2_branches/paper_v2_oddn_fragment.tex` (~6 pp) | Lipschitz lemma, arc rigidity, arc extension (needs an added hypothesis the source omitted), B1b "double ladder"; conditional A1/B2-4 in a labelled remark |

**Why exclude:** these lemmas rule out special sub-configurations of one branch of an unpublished case tree. Its
other branches (A2, B1a, B2) are open, so the lemmas prove nothing about k for any n. They have had only the drafter's
own check, and they would add about 6 pages.

**Found by the include drafter:** B2-5 in angle_R1.md has a real gap (apex outside the circle, with the missing
vertex not under it). It is mislabelled there as "conditional on Fishburn Thm 2". Fix angle_R1.md accordingly; this
commit does not touch it.

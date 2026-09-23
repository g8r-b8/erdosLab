# Lean plan: the 54/37 theorem (WRITEUP_A2)

Goal: formalise `problems/132/WRITEUP_A2.md` (paper §§2–7):

```lean
theorem Erdos132Main.erdos132_main :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      ((min (mult X (dist2 X)) (mult X (minDist X)) : ℕ) : ℝ) ≤ 54 / 37 * X.card + C₀
```

Conventions (in `E132MainDefs.lean`):
- `mult X d = multS X d` counts unordered pairs of distinct points.
- `diam`, `dist2` and `minDist` are the largest, second-largest and smallest distances. Each is `0` when it does not exist. Since `mult X 0 = 0`, small or degenerate sets need no side conditions.
- The only hypothesis is `2 ≤ X.card`.

## ✅ COMPLETE (2026-09-23, integration)

`erdos132_main` is proved with **no `sorry`**; `#print axioms Erdos132Main.erdos132_main` = `[propext, Classical.choice, Quot.sound]`.
Full `lake build` (all E132 modules imported from `Erdos.lean`) succeeds. Deviations from the plan below:
- `vesztergombi87` is proved (`E132Ve87.lean`, 2-core double counting), not cited; `hopf_pannwitz` proved in Defs.
- Bad-edge bounds KK/DD/C2 proved by direction-measure counting (`E132ConvexCurve.lean`), not arc length; Lemma 5.2
  `lens_arc_length` was unused and deleted.
- `turning_sum_le` needed a closedness hypothesis (old form false: Bernstein-set counterexample); `turning_sum_le_closure` added.
- `lemma71` restated with support points (no boundary path); `card_mixedT_le` bound 1200 instead of 71 (constant only).

## Status at skeleton time (historical)

| file | theorems | proved | `sorry` |
|---|---|---|---|
| `Erdos/Erdos/E132MainDefs.lean` | 19 | 8 | 11 (1 cited) |
| `Erdos/Erdos/E132MainLocal.lean` | 37 | 11 | 26 |
| `Erdos/Erdos/E132MainRegions.lean` | 34 | 16 | 18 |
| `Erdos/Erdos/E132MainDegen.lean` | 9 | 3 | 6 |
| `Erdos/Erdos/E132Main.lean` | 3 | 3 | 0 |
| **total** | **102** | **41** | **61** (60 to prove + cited `vesztergombi87`) |

Count again with `grep -c '^  sorry' Erdos/Erdos/E132Main*.lean`.

- `erdos132_main` is **proved from the lemma statements**. Also proved: the assembly, `main_normalized`, the region wiring (`regionI`, `regionII_high/_rest/_res`, `regionIII`), `card_bad_le`, `degenerate` and `VS`. The statements therefore fit together.
- `#print axioms erdos132_main` gives `[propext, sorryAx, Classical.choice, Quot.sound]`. The **`sorryAx` comes from the lemma sorries.**
- **Cited black box:** `vesztergombi87` ([Ve87], n₂ ≤ 3n/2). It is meant to stay a flagged hypothesis unless someone formalises Vesztergombi 1987.
- Phase 2 filled every pure algebra and numeric leaf:
  - LP: `lp_mix`, `lp_weighted`, `lp_value_le`, `lp_values`;
  - constants: `N0_check`, `c3`, `c7_kk`, `c8_cos`, `c8_walk`, `c9`, `c5_mixed`, `c5_sOff`, `c5_rhombus`, `c6`, `c10`, `two_beta_lt_of`;
  - algebra: `rung_identity_alg`, `tau_sub_tgap`, `one_lt_tau_iff_alg`, `ownership_ratios`, `cross_dist_identity`;
  - Finset bookkeeping: `card_S_add_R`, `card_edges`, `card_good_add_bad`, `card_good_le_pure_add_mixed`, `card_rungVerts`, `mem_edges`, `bad_subset`.
- Build: `cd Erdos && lake build Erdos.E132Main` takes about 1 min. It is not imported from `Erdos.lean` yet.

## Dependency DAG (remaining sorries; ✓ = proved)

```
erdos132_main ✓ ← exists_normalize, main_normalized ✓
main_normalized ✓ ← mult_minDist_le, degenerate ✓, card_lt_N0, dirField_nonempty,
                    VS ✓, E_bound, VS_weighted, card_S_add_R ✓, lp_* ✓,
                    regionI ✓, regionIII ✓, regionII_high ✓, regionII_rest ✓, regionII_res ✓

VS ✓            ← mult_dist2_eq_S, mult_dist2_subset_le ← vesztergombi87 [CITED], hopf_pannwitz
VS_weighted     ← mult_dist2_eq_S, mult_dist2_subset_le
E_bound, mult_minDist_le ← card_partners_minDist_le (kissing), two_mul_card_le_of_deg_le
card_lt_N0      ← N0_check ✓ (+ packing)

card_bad_le ✓   ← bad_subset ✓, c9 ✓, card_badKK_le, card_badDD_le, card_badC1_le, card_badC2_le
  card_badKK_le ← lens_corner, lens_arc_length, turning_ge_angle, turning_sum_le,
                  card_le_arcLength, card_partners_minDist_le, c3 ✓, c7_kk ✓
  card_badDD_le ← (same machinery on conv X)
  card_badC1_le ← exact_identity_a, turning_sum_le / disjoint normal cones
  card_badC2_le ← turning_sum_le, card_le_arcLength, c8_cos ✓, c8_walk ✓ (+ convex-curve tangents)

regionI ✓       ← regionI_card_good ✓ ← regionI_deg_le ← exact_identity_a/b/c, c4_window
                                        two_mul_card_le_of_deg_le, mem_edges ✓
regionII_high ✓ ← good_subset_T_union_rungs ← good_dichotomy ← exact_identity_a/b/c
                  rungs_eq_empty ← tau_le_one_of_exception ← exact_identity_c
                  card_tEdges_le ← T1, T2, two_mul_card_le_of_deg_le
regionII_rest/res ✓ ← regionII_eS_le ✓ ← card_mixedT_le ← lemma71 ← ball_polygon_b/c, c5_tgap
                                                          turning_sum_le, card_le_arcLength
                      ownership_rest / ownership_res ← T1, T2, R1_v, R1_z, R2, R2_sym,
                                                      R3_no_three_parallel, R3_rhombus,
                                                      R3_resonance, ownership_ratios ✓
  R1_v, R1_z, R2, R2_sym ← rung_offset ← exact_identity_c, DirField.norm_u; c5_sOff ✓
  R3_*                   ← exact_identity_c, u_ne
regionIII ✓     ← good_subset_T_union_rungs, card_tEdges_le, card_rungs_le ← rung_offset,
                  card_cornerVerts_le ← corner_lemma ← exact_identity_b/c, c6 ✓

degenerate ✓    ← degen_star ← degen_step1 ← c10 ✓, cross_dist_identity ✓
                  degen_step3 ← degen_B_no_pair, degen_A_le_one
                  degen_step4 (incidence bound)
```

## Remaining lemmas: difficulty and suggested order

S is under 1 h, M is a few hours, L is a day or more, and XL needs new infrastructure (convex curves, perimeter).

**Wave 1: definitions-level (S / S–M).** These unblock almost everything.
1. `dirField_nonempty` (S)
2. `DirField.norm_u` (S)
3. `mult_dist2_eq_S` (S)
4. `ball_polygon_a` (S–M)
5. `ball_polygon_b` (S–M)
6. `ball_polygon_c` (S)
7. `exact_identity_a` (S–M)
8. `exact_identity_b` (S–M)
9. `exact_identity_c` (M)
10. `tau_le_one_of_exception` (S)
11. `rungs_eq_empty` (S)
12. `u_ne` (S–M)
13. `rung_far_end` (S)

**Wave 2: counting (M).**
14. `two_mul_card_le_of_deg_le` (M)
15. `card_partners_minDist_le` (M)
16. `mult_minDist_le` (S–M)
17. `E_bound` (M)
18. `mult_dist2_subset_le` (M)
19. `VS_weighted` (M)
20. `exists_normalize` (M)
21. `card_lt_N0` (M–L; use a grid pigeonhole rather than area)

**Wave 3: local combinatorial geometry (M).**
22. `good_dichotomy`
23. `good_subset_T_union_rungs`
24. `T1`
25. `T2`
26. `card_tEdges_le`
27. `rung_offset`
28. `R1_v`
29. `R1_z`
30. `R2`
31. `R2_sym`
32. `R3_rhombus`
33. `R3_no_three_parallel`
34. `R3_resonance`
35. `card_rungs_le`
36. `c4_window`
37. `regionI_deg_le`
38. `c5_tgap`
39. `corner_lemma` (M–L)
40. `card_cornerVerts_le`

**Wave 4: degenerate regime.**
41. `degen_star` (M)
42. `degen_B_no_pair` (M)
43. `degen_A_le_one` (M)
44. `degen_step3` (M)
45. `degen_step1` (L)
46. `degen_step4` (L–XL). This is the incidence count, which the write-up names as one of its two least standard parts.

**Wave 5: turning measure and lenses (L).**
47. `card_le_arcLength` (M)
48. `turning_sum_le` (L)
49. `turning_ge_angle` (L)
50. `lens_corner` (L)
51. `hopf_pannwitz` (L)
52. `lemma71` (L)
53. `card_mixedT_le` (M)
54. `card_badC1_le` (L)

**Wave 6: infrastructure-heavy (XL).**
55. `lens_arc_length`. Needs perimeter monotonicity for nested convex sets, which Mathlib does not have.
56. `card_badKK_le`
57. `card_badDD_le`
58. `card_badC2_le`. Needs one-sided tangents of convex curves.
59. `ownership_rest`
60. `ownership_res`. This is the ownership/pairing bookkeeping, the other part the write-up names as least standard. The best route is probably an abstract lemma on "two rows of paths/cycles plus a matching", with (R2)/(R2-sym) as hypotheses.

**Cited:** `vesztergombi87` stays as a flagged `sorry`.

## Notes and risks

- **The statements are unvalidated.** A `sorry` can hide a false statement. The places most likely to need adjusting while proving are:
  - edge-case hypotheses of `turning_ge_angle` (nonempty interior is already assumed);
  - `lemma71` and `lens_arc_length`, which use any 1-Lipschitz path in `∂K` of the given length instead of "the boundary arc on c's side";
  - `T1`/`T2`, whose sides are defined by the sign of `det2 (u p) (q − p)`.

  If a statement changes, re-check the wiring proofs in `E132MainRegions.lean` and `E132Main.lean`.
- **Constants.** All region bounds use the uniform additive constant `cBad + 100` with `cBad = 2·10⁷`, and `C₀ = 5·10⁹ ≥ 3N₀ + cBad + 100`.
- **`open scoped Classical`.** It is used in all `E132Main*` files and triggers a style-linter warning only. The `Finset.filter`s over `Set` membership and `Sym2` predicates need it.

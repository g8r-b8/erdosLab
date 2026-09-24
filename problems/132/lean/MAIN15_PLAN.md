# Lean plan: the 15/11 theorem (angle_R4)

Goal: formalise `problems/132/angle_R4.md` (§§2–4, Appendix A; referee reports in `scratchpad/R4/`):

```lean
theorem Erdos132Main.erdos132_main15 :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 15 / 11 * X.card + C₀
```

The existing, sorry-free `54/37` files (`E132MainDefs/Local/Regions/Degen`, `E132Main`,
`E132ConvexCurve`, `E132Ve87`) are imported **unchanged**.  Reused wholesale: normalisation,
`n ≤ 3`, the degenerate regime, `card_lt_N0`, `VS_weighted` ([Ve87]), `dirField_nonempty`,
`regionI`, `regionII_high`, good/bad edges and `card_bad_le`, `good_subset_T_union_rungs`,
`card_tEdges_le`, `T1`, `T2`, `R1_v`, `R1_z`, `corner_lemma`/`card_cornerVerts_le`,
`card_rungVerts`, `rung_offset`, exact identities, turning measure (`turning_sum_le`,
`turning_ge_angle`, `le_turning_of_Icc`), `RowR`/`rowR_fun`/`rowR_inj`.

## Files

| file | contents |
|---|---|
| `E132Main15Defs.lean` | `degδ`, `mS`, `cN1 = 10⁷`, `cReg = 2cBad + 10⁴`, `twoRungVerts`, `breaks`, `SlotFree`, `rot`, `alpha1/2`; exact identity; `lp15`; `consts15` |
| `E132Main15N1.lean` | Theorem N1 (Euclidean-local form, see below); `E_bound15 : μ(δ) ≤ e(S) + 5r + cN1` |
| `E132Main15RegionII.lean` | Lemmas A, B, C; `regionII15 : e(S) ≤ |S| + |P₁| + cReg` for `√3/2+3β ≤ τ ≤ 1` |
| `E132Main15Exact.lean` | `τ = √3/2` rigidity chain (R)(B′)(W)(Arc)(Rigid)(Arith)(Count) → `exact_breaks` |
| `E132Main15RegionIII.lean` | slot killing, breaks, Lemma 7.1 in Region III; `regionIII15` |
| `E132Main15.lean` | assembly `assemble15`, `main15_normalized`, `erdos132_main15` |

Import chain: `E132MainRegions → Main15Defs → {Main15N1, Main15RegionII, Main15Exact → Main15RegionIII} → Main15` (+ `E132Main`).
Check one file: `cd Erdos && lake env lean -o .lake/build/lib/lean/Erdos/<F>.olean -i .lake/build/lib/lean/Erdos/<F>.ilean Erdos/<F>.lean`
(the `-o` is needed so that downstream `E132Main15*` files can import it without `lake build`).

## ✅ COMPLETE (2026-09-24)

`erdos132_main15` is proved with **no `sorry`**. `#print axioms Erdos132Main.erdos132_main15` =
`[propext, Classical.choice, Quot.sound]`; no `native_decide`/`bv_decide`, no new axioms.
All six `E132Main15*` modules are imported from `Erdos.lean`; full `lake build` succeeds
(`lake build Erdos.E132Main15` ≈ 1 min from the 54/37 oleans).

| file | theorems (incl. helpers) | lines | sorry |
|---|---|---|---|
| Defs | 5 | 192 | 0 |
| N1 | 29 | 1169 | 0 |
| RegionII | 17 | 620 | 0 |
| Exact | 70 | 2277 | 0 |
| RegionIII | 17 | 870 | 0 |
| Main15 | 3 | 123 | 0 |
| **total** | **141** | **5251** | **0** |

No skeleton statement was changed. Notes from Phase 2:
- `lemmaC` is proved by an exact reflection decomposition (`reflect_eq`, `lemmaB_threshold`,
  `two_circles`), not the angle bounds of angle_R4 §2.
- `thin_box` uses an `(e, ν₁)` frame; the constants have a large margin (referee: `L ≤ 19.7`, `W ≤ 2.28`).
- `exact_breaks` is proved through private walk/charge helpers in `E132Main15Exact.lean`.
- An independent math referee (`scratchpad/L15/ref_report.md`) checked the two new arguments
  (Euclidean-local N1; slots/breaks for Region III) and found every statement true as written.

## Status at skeleton time (historical)

`#print axioms erdos132_main15 = [propext, sorryAx, Classical.choice, Quot.sound]`; the `sorryAx`
comes only from lemma sorries.  **Proved already:** the assembly (`erdos132_main15`,
`main15_normalized`, `assemble15`), `lp15`, `consts15`, `mS_le_degδ`, `degδ_le_six`, the N1 wiring
(`N1`, `E_bound15`, `cN1_check`), region wiring (`regionII15`, `card_tEdges_add_doubleEnds_le`,
`regionIII_key`, `regionIII15`).

| file | theorems | sorry |
|---|---|---|
| Defs | 5 | 1 |
| N1 | 19 | 16 |
| RegionII | 11 | 9 |
| Exact | 17 | 17 |
| RegionIII | 10 | 8 |
| Main15 | 3 | 0 |
| **total** | **65** | **51** |

Count again with `grep -c '^  sorry' Erdos/Erdos/E132Main15*.lean`.

## Deviations from the paper (by design)

1. **N1 without arc length.**  The paper's `γ_y` (arc of length `≤ 232` of `∂K`) and Lemma T's
   perimeter-monotonicity case are replaced by a Euclidean-local trichotomy at `y ∈ R ∖ D`:
   *flat* (all unit normals at `∂K ∩ B̄(y,1)` within `1/4` of one vector ⇒ every `S`-neighbour has
   `(q−y)·n > −1/4` ⇒ `m_y ≤ 4`, since an open arc of length `2 arccos(−1/4) < 240°` holds
   `≤ 4` points `60°` apart); *thin* (two nearly antipodal normals there: the paper's fatness step
   ⇒ `K` in a `400 × 9` box ⇒ `|X∖D| ≤ 10⁴`); *big turning* (else every direction between the two
   normals is the normal of a support point within `150` of `y` ⇒ `turning(∂K ∩ B̄(y,150)) ≥ 1/4`
   ⇒ `≤ 8π·601²` such `y`).  `R ∩ D` directly (`m_y ≤ 4`).  Constant `cN1 = 10⁷` (paper `7·10⁷`).
   The flat case needs only `(q−y)·ν > 0` at the exit point of `[y,q]`, not the concave-graph
   description (F1)–(F4).  **Not refereed** — the one new argument of this formalisation.
2. **Region III by slots, not cyclic orders.**  `#T + q₂ ≤ |S| + C` is proved via
   *slots* (`card_tEdges_slots`: `2#T + #free slots ≤ 2|S|`) for `τ < √3/2`, and via
   *breaks* (points without a pure right T-neighbour; `#T + #breaks ≤ |S| + #mixed`) at
   `τ = √3/2`.  So (R) "rows are cyclic orders" is not needed; `rowR_cap_K` is stated for
   fidelity but is off the critical path.
3. **Region II** uses `P₁ = P1set` (rung K-ends of `Δ₂`-degree 1) as `Q`, like the `54/37` Region III.
4. N2 (the `4/3` refinement in Region II) is not formalised (not needed for `15/11`).

## Dependency DAG (✓ = proved)

```
erdos132_main15 ✓ ← exists_normalize, main15_normalized ✓
main15_normalized ✓ ← degenerate, card_lt_N0, dirField_nonempty, consts15 ✓, assemble15 ✓,
                      regionI, regionII_high            (all from the 54/37 development)
                      regionIII15 ✓, regionII15 ✓
assemble15 ✓ ← VS_weighted, lp15 ✓, E_bound15 ✓

E_bound15 ✓ ← mu_delta_identity, N1 ✓, mS_le_degδ ✓, degδ_le_six ✓
N1 ✓ ← mS_le_four_of_D ← card_sep_arc_le_four
       Rset_interior
       exists_near_normal ← Sset_not_interior, exists_frontier_seg
       mS_le_four_of_flat ← Sset_not_interior, exists_frontier_seg, inner_pos_of_seg,
                            card_sep_arc_le_four
       thin_card_le ← thin_box ← frontier_on_circle;  card_sep_box_le
       turning_ge_of_nonflat ← norm_le_of_inner_bounds
       card_bigTurning_le ← card_sep_ball_le
       cN1_check ✓

regionII15 ✓ ← card_tEdges_add_doubleEnds_le ✓ ← lemmaC, card_tEdges_add_le_of_isolated
               card_rungs_le_II ← card_typeOne_le_five ← lemmaA_i
  lemmaC ← lemmaA_ii, lemmaB ← lemmaB_sq;  lemmaC_numeric

regionIII15 ✓ ← card_rungs_le_add, regionIII_key ✓
regionIII_key ✓ ← twoRung_eq_empty                                  (τ > √3/2)
                  card_tEdges_add_twoRung_lt ← card_tEdges_slots,  (τ < √3/2)
                                               slot_kill_one, slot_kill_inj
                  card_tEdges_add_breaks_le, card_mixedT_le_III,   (τ = √3/2)
                  exact_breaks
exact_breaks ← card_badBase_le ← tri_of_twoRung, base_apex_unique
               Bprime_walk_right/left, Bprime_rot, Bprime_span, W_center, apex_eq,
               arc_sub_K, normal_fact, rigid_step, arith_no_land ← tgap_bounds_exact,
               arc_centre_unique            [(R) rowR_cap_K: off the critical path]
```

## Remaining lemmas: difficulty and order

S < 1 h, M a few hours, L a day or more, XL new infrastructure / multi-day.

**Wave 1 (S, S–M: algebra, constants, identities).**
`lemmaB_sq`, `lemmaB`, `lemmaC_numeric`, `tgap_bounds_exact`, `norm_le_of_inner_bounds`,
`Sset_not_interior`, `Rset_interior`, `frontier_on_circle`, `inner_pos_of_seg`, `twoRung_eq_empty`,
`lemmaA_ii`, `mu_delta_identity` (M).

**Wave 2 (M: counting / packing / copies of proved lemmas).**
`card_sep_arc_le_four`, `mS_le_four_of_D`, `exists_frontier_seg`, `exists_near_normal`,
`mS_le_four_of_flat`, `card_sep_box_le`, `card_sep_ball_le`, `card_bigTurning_le`, `thin_card_le`,
`lemmaA_i`, `card_typeOne_le_five`, `card_tEdges_add_le_of_isolated`, `card_rungs_le_II`,
`card_rungs_le_add`, `card_tEdges_slots`, `card_tEdges_add_breaks_le`, `arith_no_land`.

**Wave 3 (M–L: local geometry).**
`turning_ge_of_nonflat`, `lemmaC` (L), `slot_kill_one`, `slot_kill_inj`,
`card_tEdges_add_twoRung_lt`, `card_mixedT_le_III` (copy of `lemma71`/`card_mixedT_le` with
constant `0.835`), `tri_of_twoRung`, `base_apex_unique`, `card_badBase_le`, `arc_sub_K`,
`normal_fact`, `apex_eq`, `rowR_cap_K` (optional).

**Wave 4 (L–XL).**
`thin_box` (the fatness step), `Bprime_walk_right/left`, `Bprime_rot`, `Bprime_span`, `W_center`,
`rigid_step`, `arc_centre_unique`, `exact_breaks` (the injection triangles → breaks: walks,
`Nat.find` of the first break, disjointness of half-open arcs).

## Risks

- The statements are unvalidated until proved; most likely to need adjustment: the orientation
  conventions in `Bprime_rot`/`rigid_step` (counterclockwise = right), the exact hypotheses of
  `exact_breaks`'s chain, and `thin_box` (fatness step constants).  If a statement changes,
  re-check the wiring in `E132Main15RegionIII.lean` and `E132Main15N1.lean`.
- `card_mixedT_le_III` depends on re-running the `lemma71` proof with a weaker constant; if the
  `54/37` proof uses `τ ≥ √3/2 + 3β` elsewhere, it needs a Region III variant.

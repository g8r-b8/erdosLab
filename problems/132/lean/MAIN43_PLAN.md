# Lean plan: the 4/3 theorem (angle_R6 §1, Theorem N3)

Goal: formalise `problems/132/angle_R6.md` §1 (Theorem N3: `Σ_{y∈R}(deg y + m_y) ≤ 8|R| + C₃`;
Corollary `L ≤ 4/3`):

```lean
theorem Erdos132Main.erdos132_main43 :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 4 / 3 * X.card + C₀
```

All `54/37` and `15/11` files are imported **unchanged** (`E132Main43` imports `E132Main15`).
Reused wholesale: normalisation, `n ≤ 3`, `degenerate`, `card_lt_N0`, `VS_weighted`,
`dirField_nonempty`, `regionI`, `regionII_high`, `regionII15`, `regionIII15`,
`mu_delta_identity`, `degδ`, `mS`, `card_S_add_R`, `Rset_interior`, `Sset_not_interior`,
`exists_near_normal`, `exists_frontier_seg`, `exists_unit_normal`, `card_sep_ball_le`,
`card_sep_arc_le_four`, `turning_sum_le`, `norm_le_of_inner_bounds`, `n1_*` helpers of `thin_box`,
`ball_polygon_a/b/c`, `dist_le_diam`, `dist_le_dist2`.

## Files

| file | contents |
|---|---|
| `E132Main43Defs.lean` | `vR`, `nbδ`, `depth`, `Low` (receivers), `heavy`, `IsGood43`, `E43`, `dirF`, `Slot`, structure `Frame43`, `FanSlots`, `IsFan43`, `IsCap43`, constants; `charge_sum` (charging lemma, proved), `lp43`, `consts43`, `degδ_le_three_of_D`, `frame_normal_close` |
| `E132Main43Good.lean` | §1.1–1.2: `card_E43_le` (≤ `cE43` non-good heavy points: thin / big turning at scale Λ), `frame_of_good` (heavy + good ⇒ `Frame43`) |
| `E132Main43Frame.lean` | §1.2 facts from `Frame43`: F′1 `frame_outside`, F′3 `frame_D`, Lemma DN `frame_dn`/`frame_dn1`, D–D heights `dd_heights`, receivers `Low_Z`, `lower_mem_Low`, `card_cone_le_two` |
| `E132Main43Classify.lean` | §1.3: Lemma P (`pair_sym`, `pair_K`, `pair_D`), `hexagon_exact`, Lemma M, Lemma H, shapes, Lemma Pin; outputs `heavy_type`, `heavy_low` |
| `E132Main43Charge.lean` | §1.4: `low_receiver` (receivers in `R`, `v ≤ 7`), `low_disjoint` (owner uniqueness: fans, caps, HF2–HF2) |
| `E132Main43.lean` | `N3`, `E_bound43`, `assemble43`, `main43_normalized`, `erdos132_main43`, `#print axioms` |

Import DAG (shallow, for parallel filling):

```
E132Main15N1 → Main43Defs → Main43Good ─────────────┐
                          → Main43Frame → Main43Classify ─┤→ Main43 (+ E132Main15)
                                        → Main43Charge ───┘
```

`Good ∥ Frame`; `Classify ∥ Charge` (both only need `Frame`'s statements).  The interfaces are
the structure `Frame43 X y n` and the predicates `IsFan43`/`IsCap43` (all in `Defs`).
Check one file: `cd Erdos && lake env lean -o .lake/build/lib/lean/Erdos/<F>.olean -i .lake/build/lib/lean/Erdos/<F>.ilean Erdos/<F>.lean`
(in DAG order; `-o` lets downstream files import it).  Not imported from `Erdos.lean`.

## Status at skeleton time (2026-09-25)

`#print axioms Erdos132Main.erdos132_main43 = [propext, sorryAx, Classical.choice, Quot.sound]`;
`sorryAx` only from the lemma sorries.  **Proved already**: the assembly (`erdos132_main43`,
`main43_normalized`, `assemble43`, `E_bound43`, `N3`), `charge_sum`, `lp43`, `consts43`, and the
wiring `frame_of_good`, `card_E43_le`, `thin_card_le43`, `card_bigTurning_le43`,
`card_notD_le_of_small`, `heavy_shape`, `heavy_type`, `heavy_low`, `low_receiver`,
`low_disjoint`, plus small helpers (`Frame43.top`, `frame_normal_close`, `D_inner`, `Low_Z`,
`Low_interior`, `frame_mem_interior`, …).

| file | theorems | lines | sorry |
|---|---|---|---|
| Defs | 8 | 296 | 1 |
| Good | 15 | 351 | 5 |
| Frame | 15 | 247 | 8 |
| Classify | 13 | 280 | 10 |
| Charge | 6 | 144 | 4 |
| Main43 | 5 | 174 | 0 |
| **total** | **62** | **1492** | **28** |

Count again with `grep -c '^  sorry' Erdos/Erdos/E132Main43*.lean` and
`grep -c '^theorem' Erdos/Erdos/E132Main43*.lean`.

## Deviations from the paper (by design)

1. **Goodness without arc length** (as N1 in `MAIN15_PLAN.md`).  Paper §1.1: `y` good iff
   per K ≥ 2Λ, the arc `γ_y` (arc-distance ≤ Λ from the foot) has turning ≤ ε₀, and
   `∂K ∩ B̄(y,3) ⊂ γ_y`.  Here: `IsGood43 X y` iff all unit normals at boundary points within
   *Euclidean* distance `Λ = 464` of `y` are pairwise within `ε₀ = 1/50` (in norm).
   Non-good heavy points: two normals with `‖ν₁ − ν₂‖ > ε₀` at points within `Λ`; either
   **thin** (`ν₁·ν₂ ≤ −(1 − 10⁻⁴)`) ⇒ `|X ∖ D| ≤ 10¹⁴` (`thin_card_le43`), or every intermediate
   direction is supported within `150Λ = 69600` of `y` ⇒ `turning(∂K ∩ B̄(y, 69600)) ≥ ε₀`
   ⇒ `≤ 100π·278401²` such `y` (`turning_ge43`, `card_bigTurning_le43`).  `cE43 = 10¹⁵`.
   Lemma T* (arcs of length > Λ between close boundary points) is not needed at all.
2. **Thin case at scale Λ needs a small-Δ₂ split.**  With `|b₁b₂| ≤ 2Λ` the width is only
   `W ≤ 928 + L/69`, not `≪ 10⁴`, so the fatness contradiction `|w_bot − w_top| > 1.94Δ₂`
   needs `Δ₂ ≥ 10⁶` (`thin_box43`: box `2·10⁵ × 5000`); for `Δ₂ < 10⁶`,
   `X ∖ D ⊂ K ⊂ B̄(w, Δ₂)` and packing gives `(4·10⁶+1)²` (`card_notD_le_of_small`, proved).
3. **Frame without the graph `f`.**  `Frame43 X y n`: `n` is the unit outer normal at a nearest
   boundary point `p₀ = y + h n` (`h = depth ∈ (0,1]`, not `p₀` as origin), normals within
   distance 6 are within `ε₀` of `n`, and `K` contains *far points* at abscissa `±463`, height
   `≥ h − 9.31` (`far_points`: support point in a direction just outside the `ε₀`-cone lies
   beyond `Λ`; convexity).  F′1 becomes `Z q ≥ h − |Xq|/49` for `q ∉ int K` (`frame_outside`,
   proved via the exit point of `[y, q]`), F′3 `Z z ≥ h + t − |Xz|/49` (`frame_D`), DN uses the
   far points instead of `g± = (±463, f(±463))`: `τ₃ ≤ 3/100`, `τ* ≤ 9/400` (paper
   `0.0267`, `0.0224`).  Slope constant `ε = 1/49` (paper `tan ε₀ < 0.02001`).
4. **Receivers are intrinsic**: `Low X y` = `δ`-neighbours `a ∈ K` with
   `depth a ≥ depth y + 2/3` (the brief suggested `3/4`; `2/3` is used because F5's lower point
   is only known to have height `≤ −0.85`, and the depth estimate loses `3/49`).  All lower
   points of fans (height `≤ −0.8`) and the cap's `b` are receivers (`lower_mem_Low`); the cap's
   `±120°` points (height `≈ −0.5`) are not (`Low_Z`: receivers have height `≤ −2/3`).
   **HF1/HF2 send to both lower points** (the paper sends one unit to `a₊` only): harmless, the
   owner-uniqueness argument (common owner ⇒ horizontal neighbour ⇒ HF2–HF2 ⇒ a D-point of
   degree 4) works for every receiver, and `charge_sum` needs only `v ≤ 8 + |rec|`.
5. **Classification output as shapes/types.**  `FanShape`/`CapShape` (Classify) record the
   slots (tolerance `1/20`), the height gap of lower points, and `v ≤ 8 + #{height ≤ −4/5}`;
   `IsFan43`/`IsCap43` (Defs) add the Pin windows (`t ≥ 0.7`, resp. `t ≤ 0.6`; paper
   `[0.74, 0.99]`, `[0.43, 0.57]`) and the receiver positions consumed by `Charge`.
6. **Lemma Pin in Euclidean form**: `z` not normal for `p` (`⟨z − p, w_p − p⟩ < 0`) ⇒ exception
   `|z w_p| = Δ` ⇒ law of cosines; `n1_circle_normal` supplies the partner `w_p` with
   `(p − w_p)/Δ₂` an outer normal (no DirField needed).  Cap: only F′0 and F′3.

## Dependency DAG (✓ = proved)

```
erdos132_main43 ✓ ← exists_normalize, main43_normalized ✓
main43_normalized ✓ ← degenerate, card_lt_N0, dirField_nonempty, regionI, regionII_high,
                      regionIII15, regionII15 (all proved), consts43 ✓, assemble43 ✓
assemble43 ✓ ← VS_weighted, lp43 ✓, E_bound43 ✓
E_bound43 ✓ ← mu_delta_identity, N3 ✓, card_E43_le ✓
N3 ✓ ← charge_sum ✓, vR_le_twelve ✓, frame_of_good ✓, heavy_low ✓, heavy_type ✓,
        low_receiver ✓, low_disjoint ✓

card_E43_le ✓ ← heavy_not_D ✓ ← vR_le_six_of_D ✓ ← degδ_le_three_of_D
                heavy_interior ✓ (Rset_interior)
                thin_card_le43 ✓ ← card_notD_le_of_small ✓, thin_box43, card_sep_box_le43
                turning_ge43;  card_bigTurning_le43 ✓;  cE43_check ✓
frame_of_good ✓ ← heavy_interior ✓, heavy_depth_le ✓, exists_foot, good_normals ✓, far_points

Frame facts:  frame_outside;  frame_mem_interior ✓ ← frame_outside
              frame_D ← frame_outside
              frame_dn, frame_dn1 ← frame_D, frame_mem_interior, Frame43.far
              dd_heights ← D_inner ✓, frame_dn1
              frame_depth_le;  Low_Z ✓ ← frame_depth_le
              lower_mem_Low ← frame_outside, frame_mem_interior
              card_cone_le_two

heavy_type ✓, heavy_low ✓ ← heavy_shape ✓ ← mS_le_four_of_frame, fanShape_of_m4, lemmaH
                           pin_fan, pin_cap, Low_Z ✓, lower_mem_Low
fanShape_of_m4 ← lemmaM (← pair_K, pair_D ← pair_sym, dd_heights), hexagon_exact
lemmaH ← hexagon_exact, pair_K, pair_D, frame_outside, frame_D

low_receiver ✓ ← Low_interior ✓, mS_le_one_of_Low (← Low_Z, frame_outside, card_cone_le_two)
low_disjoint ✓ ← fan_disjoint (← fan_common_low_slot, frame_normal_close ✓,
                                 degδ_le_three_of_D), cap_disjoint (← frame_normal_close ✓)
```

## Remaining lemmas: difficulty and order

S < 1 h, M a few hours, L a day or more.

**Wave 1 (S–M: algebra, packing, copies of proved lemmas).**
`pair_sym`, `pin_cap`, `cap_disjoint`, `mS_le_four_of_frame` (copy of `mS_le_four_of_D`),
`degδ_le_three_of_D` and `card_cone_le_two` (copies of `card_sep_arc_le_four` with another cone),
`card_sep_box_le43` (copy of `card_sep_box_le`), `turning_ge43` (copy of `turning_ge_of_nonflat`
with `1 ↦ Λ`).

**Wave 2 (M: frame geometry).**
`exists_foot`, `frame_outside`, `frame_D`, `frame_depth_le`, `lower_mem_Low`, `frame_dn`,
`frame_dn1`, `dd_heights`, `far_points` (M–L), `pair_K`, `pair_D`, `mS_le_one_of_Low`,
`pin_fan`, `hexagon_exact` (M–L).

**Wave 3 (L: classification and uniqueness).**
`lemmaM`, `fanShape_of_m4`, `lemmaH` (the paper's case enumeration), `fan_common_low_slot`
(M–L), `fan_disjoint` (HF2–HF2), `thin_box43` (rerun of `thin_box` at scale Λ).

## Constants and margins (checked by hand; a referee should recheck)

- `ε = 1/49 ≥ (1/50)/(1 − 1/5000) = 0.020004`.
- Far points: `κ = 0.0201`, `‖d − n‖ = 0.02010 > 1/50`; `463² + (1 + 463κ)² = 214475 < 464²`;
  height loss `463κ = 9.306 ≤ 9.31`.
- DN: `(9.31 + 3)/460 = 0.02676 ≤ 3/100`; `(9.31 + 1)/462 = 0.02232 ≤ 9/400`.
- Receivers: fan lower points height `≤ −0.8` ⇒ depth `≥ h + 0.8 − 3/49 = h + 0.739 ≥ h + 2/3`;
  receiver `S`-neighbours: `2/3 − 2/49 = 0.626 > 1/2`.
- Pin: fan `Δc ≥ √3/2 − 1/10 = 0.766`, `t ≥ 0.766 − 0.04 − 10⁻⁴ > 0.7`; cap
  `t ≤ 1 − (1/2 − 1/20) + 1/980 < 0.6`.
- Fan owners: `|α| ≤ 36.9°`, `|α′| ≤ 38.8°`, `|α − α′| ≥ 60°` ⇒ `‖y′ − y ∓ perp n‖ ≤ 0.282 ≤ 7/20`;
  `7/20 + 1/20 < 1`; HF2 coincidence `3/20 + 1/50 < 1`.
- Thin: `‖ν₁ + ν₂‖ ≤ 0.01415`, slope `≤ 1/69`; `L ≥ 146358 ⇒ W ≤ L/48`;
  `W ≤ 928 + 2Δ₂/69 < 0.058Δ₂` for `Δ₂ ≥ 10⁶`; box `2·10⁵ × 5000`, packing `≤ 4.1·10⁹`.
- `100π·278401² ≈ 2.44·10¹³`; `cThin43 = 10¹⁴`, `cE43 = 10¹⁵`, `C43 = 10¹⁶ ≥ 3N₀ + (2cE43 + cReg)/3 + cReg`.

## Risks

- **Classification (Lemmas M, H) is the bulk of the work** and is only refereed on paper (with
  `ε = 0.02001`, `τ* = 0.0224`); the slot tolerance `1/20` is comfortably above the derived
  offsets (`≤ 2.6°`, chord `≤ 0.046`), but the fill agent must redo the enumeration with the
  Lean constants (`ε = 1/49`, `τ* = 9/400`, pair bounds `1/49`, `9/200`).  If a statement of
  `FanShape`/`CapShape` must change, only `heavy_type`/`heavy_low` (Classify) and the `IsFan43`
  consumers in Charge need re-checking.
- `far_points` and `thin_box43` are the two genuinely new geometric arguments (not in the
  15/11 development) — **not refereed**.
- `hexagon_exact` states closure under `rot (π/3)` (counter-clockwise); `lemmaH` and HF2's
  `dist z₁ z₂ = minDist` rely on it.
- `Frame43.normals` has radius 6; every use (`frame_outside` at radius 6, `frame_normal_close`
  at 3, `lower_mem_Low` at 3) fits.

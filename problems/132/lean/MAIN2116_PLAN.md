# Lean plan: Theorem 1(b), the 21/16 bound (paper §10 `sec:P4`, §11 `sec:II`)

Goal (paper `problems/132/paper/paper.tex`, thm:IIone):

```lean
/-- scale-invariant τ(X) = (Δ² − Δ₂² − δ²)/(2Δ₂δ) (paper v3 intro) -/
def tauInv (X : Finset Pt) : ℝ :=
  (diam X ^ 2 - dist2 X ^ 2 - minDist X ^ 2) / (2 * dist2 X * minDist X)

theorem Erdos132Main.erdos132_main2116 : ∃ C₁ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
    (tauInv X ≤ √3/2 - 1/50 ∨ √3/2 + 3/100 ≤ tauInv X) →
    (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 21/16 * X.card + C₁
```

`tauInv` is the `τ` of `E132MainDefs` after normalising: `tauInv_eq_tau` (`δ = 1`, `Δ₂ ≠ 0`)
and `tauInv_smul` (dilation invariance) are proved, and `exists_normalize2116` keeps `tauInv`.
No adjustment of the statement was needed.  `√3/2 − 1/50 = √3/2 − 2β` and
`√3/2 + 3/100 = √3/2 + 3β` exactly (`β = 1/100`).

All earlier files are imported **unchanged**: `E132Main2116Defs` imports `E132Main43`, which
imports the whole `54/37`, `15/11` and `4/3` development.
Reused wholesale: `exists_normalize` (proof pattern), `degenerate`, `mult_minDist_le`,
`card_sep_ball_le`, `regionI`, `regionII_high`, `VS_weighted`, `mu_delta_identity`,
`dirField_nonempty`, `Rset_interior`, `Sset_not_interior`, `exists_foot`,
`exists_near_normal`, `vR`, `vR_le_twelve`, `vR_le_six_of_D`, `depth`, `nbδ`, `dirF`,
`card_sep_box_le43`, `ball_polygon_a`, `good_subset_T_union_rungs`, `card_good_add_bad`,
`card_bad_le`, `card_tEdges_add_breaks_le`, `card_mixedT_le`, `breaks`, `RowR`, `RungM`.

## Files

| file | contents |
|---|---|
| `E132Main2116Defs.lean` | `tauInv`, `Q2` (all of `S` with `deg₂ = 1`), constants, `IsGoodP`, `EP`, structure `FrameP`, the shapes `TwoShape`/`APShape`/`CapShapeP`/`KKDShape`/`DtShape`, charge vectors, `ShapeI`, `ShapeII`, `SendRule`, `sendAmt`, `fwdTarget`, `dest`, `Tr`, `ImmSender`; proved: `shapeI_facts`, `charge7`, `weight7_of_rules`, `lp2116`, `consts2116`, `tauInv_eq_tau`, `tauInv_smul`, `exists_normalize2116`, `card_le_of_small2116` |
| `E132Main2116Good.lean` | lem:fewbad2 / lem:frame at scale `Λ = 10⁹`: `far_pointsP`, `thin_boxP`, `turning_geP`, `card_bigTurning_leP`; wired: `frameP_of_good`, `thin_card_leP`, `card_EP_le` |
| `E132Main2116Frame.lean` | lem:flatmodel (a)–(d) and neighbour facts: `FrameP.toFrame43`, `frameP_outside`, `frameP_D`, `frameP_dn`, `flat_D`, `flat_pin`, `frameP_close`, `pair_K2116`, `pair_D2116`, `hex_of_deg6`; proved: `FrameP.top`, `flat_K`, `flat_int`, `nb_kind`, `nb_above_D` |
| `E132Main2116ClassI.lean` | lem:S3, lem:classP4: `S3_noD`, `S3_mS_le`, `S3_three`, `class62`, `class63`, `class53`; wired: `classI_shape` |
| `E132Main2116DischI.lean` | lem:recv2, lem:cone, lem:Th, lem:loads: `recvI`, `coneI`, `ThI`, `loadI`; wired: `recvI_dest` |
| `E132Main2116RegionIIw.lean` | lem:IIS, lem:IIclass, lem:IIrecv, lem:IIloads: `IIS`, `IIclass_shape`, `recvII`, `loadII`; wired: `recvII_dest` |
| `E132Main2116RegionIIe.lean` | lem:IIZ, lem:IIord, lem:IIarc, lem:IIdisj, thm:IIBC, lem:IIcons, thm:IIe: `IIZ_circle`, `IIZ_centre`, `IIord`, `IIarc_walk`, `IIdisj_walk`, `IIBC`, `IIcons_a`, `IIcons_b`, `two_U_le`; wired: `regionIIe` |
| `E132Main2116.lean` | wired: `sendRuleI_of_good`, `sendRuleII_of_good`, `W7_I` (Theorem P4), `W7_II` (Theorem IIw), `E_bound2116`, `assemble2116`, `main2116_normalized`, `erdos132_main2116`, `#print axioms` |

Import DAG (shallow; the six fill files are pairwise disjoint and depend only on statements):

```
E132Main43 → 2116Defs → 2116Good ─────────────────────────┐
                      → 2116Frame → 2116ClassI ────────────┤
                                  → 2116DischI ────────────┤→ E132Main2116
                                  → 2116RegionIIw ─────────┤
                      → 2116RegionIIe ─────────────────────┘
```

`Good ∥ Frame ∥ RegionIIe`; `ClassI ∥ DischI ∥ RegionIIw` (all three need only `Frame`'s
statements and the shape/rule definitions in `Defs`).  Check one file (in DAG order, one
compile at a time, through the semaphore):

```
cd Erdos && ../tools/leanslot.sh lake env lean -o .lake/build/lib/lean/Erdos/<F>.olean \
  -i .lake/build/lib/lean/Erdos/<F>.ilean Erdos/<F>.lean
```

Not imported from `Erdos.lean`.

## Status at skeleton time (2026-09-25)

`#print axioms Erdos132Main.erdos132_main2116 = [propext, sorryAx, Classical.choice, Quot.sound]`;
`sorryAx` comes only from the 37 lemma stubs.  No `native_decide`/`bv_decide`, no new axiom.

| file | theorems | lines | sorry |
|---|---|---|---|
| Defs | 16 | 613 | 0 |
| Good | 11 | 249 | 4 |
| Frame | 15 | 282 | 10 |
| ClassI | 7 | 161 | 6 |
| DischI | 5 | 139 | 4 |
| RegionIIw | 5 | 118 | 4 |
| RegionIIe | 10 | 263 | 9 |
| Main2116 | 8 | 204 | 0 |
| **total** | **77** | **2029** | **37** |

Count again with `grep -c '^  sorry' Erdos/Erdos/E132Main2116*.lean` and
`grep -c '^theorem' Erdos/Erdos/E132Main2116*.lean`.
(The skeleton commit message says "78 theorems": that count included a `theorem` line inside a
docstring code block, now indented.)

## Architecture

**Assembly** (`main2116_normalized`, proved): `n ≤ 3` (`μ(δ) ≤ 3n ≤ 9`); degenerate
`Δ > 1.94Δ₂` (`μ(Δ₂) ≤ n + 1`); `Δ₂ < 2·10¹⁵` (`n ≤ (16·10¹⁵ + 1)²` by packing, `3n ≤ C₁`);
otherwise `Normal Y`, `Δ₂ ≥ 2·10¹⁵`, `tauInv = tau`, and

* Region I: `regionI` (`e(S) ≤ s + cBad + 100`) + `W7_I`;
* `τ > 1`: `regionII_high` + `W7_I`;
* Region II, `τ ≤ 1`: `regionIIe` (`e(S) ≤ s + |Q2|/2 + cIIe`) + `W7_II`;

then `assemble2116`: `μ(δ) ≤ e(S) + (7/2)r + (5/2)cEP` (`E_bound2116`, from
`mu_delta_identity`), `μ(Δ₂) ≤ |Q| + (3/2)(s − |Q|)` (`VS_weighted`, `Q = ∅` or `Q2`), and
`lp2116` (weights `5/8, 3/8`; `(5/8)(3s/2 − p/2) + (3/8)(s + p/2 + 7r/2) = (21/16)(s+r) − p/8`).

**Weight 7** (`W7_I`, `W7_II`, proved from `weight7_of_rules`): the abstract `charge7`
(`v ≤ 12` on `R`, exceptions `E`, a nonnegative transfer inside `R` in which every
non-exceptional point of weight `≥ 8` sends `≥ v − 7`, only those send, charge lands at weight
`≤ 6`, loads `≤ 1` ⇒ `Σ_R v ≤ 7|R| + 5|E|`) applied to `T = Tr Shape X`:

* `sendAmt Shape X y` — a chosen admissible charge vector (`SendRule`: `y` good′ in `R`,
  `v ≥ 8`, `a ≥ 0` on neighbours, `Σ a ≥ v − 7`, a frame `FrameP X y n` and a shape);
* `dest X x` — `x`, or the target `fwdTarget X x = 2x − k` if `v(x) = 7` (**merged
  forwarding**: the paper's two-step rule "receivers of weight 7 pass everything on" is a
  single transfer from the original sender to the final destination);
* inputs: classification (`classI_shape` / `IIclass_shape` + `frameP_of_good` +
  `shapeI_facts`), receivers (`recvI_dest` / `recvII_dest`), loads (`loadI` / `loadII`),
  exceptions (`card_EP_le`).

**Rungs in Region II** (`regionIIe`, proved from `IIBC`, `two_U_le`):
`e(S) = #good + #bad`, `good ⊆ T ∪ rungs`, `#T + #breaks ≤ s + #mixed`,
`#rungs ≤ #breaks + U + 2` (`IIBC`), `2U ≤ |Q2| + 34` (`two_U_le`), `#mixed ≤ 1200`,
`#bad ≤ cBad` ⇒ `e(S) ≤ s + |Q2|/2 + cBad + 1219`.

## Deviations from the paper (by design)

1. **Goodness without arc length** (as `MAIN43_PLAN.md` 1): `IsGoodP X y` iff all unit normals
   at boundary points within Euclidean distance `Λ = 10⁹` of `y` are pairwise within
   `ε₀ = 10⁻⁶` in norm.  Non-good points of weight `≥ 8` are thin (`|X ∖ D| ≤ 10²³`, needs
   `Δ₂ ≥ 2·10¹⁵ ≫ Λ` for the fatness step) or have turning `≥ ε₀` on `∂K ∩ B̄(y, 150Λ)`
   (`≤ 2π·10⁶·(6·10¹¹ + 1)² ≈ 2.3·10³⁰`).  So `cEP = 10³²` (paper `N′_g = 2.6·10²⁵`) and
   `C₁ = 10³³` (paper `2·10³²`).
2. **Frame `FrameP`** (as `Frame43`): unit normal at a nearest boundary point, normals within
   `ε₀` on radius **10** (paper `ρ = 6`; the slack makes `frameP_D` at radius 6 easy), far
   points at abscissa `±(Λ − 1)` and height `≥ h − 1011`.  Slope `εP = 2·10⁻⁶`, DN slope
   `κD = 2·10⁻⁶`, K-row level window `δ₀/5`, D-level window `δ₀/2`, pinning `δ₀/5`, frame
   comparison `δ₀/5` (paper: `6ε`, `2·10⁻⁶`, `1.3·10⁻⁵`, `2·10⁻⁵`).
3. **No parametrised frame layer.** The `4/3` frame lemmas are proved for the fixed `Frame43`
   constants and may not be modified.  Instead `FrameP` is a new concrete structure, the few
   needed facts are restated at the new scale (fill agents copy the `4/3` proofs with new
   constants), and `FrameP.toFrame43` makes every coarse `4/3` frame lemma available.
4. **Rules as shapes.**  The classifications output *shapes* in the frame `(y, n)`:
   `TwoShape σ φ` (one predicate for types A, B, C_φ: exact hexagon with base `σφ`,
   `φ ∈ [−ηA, 30° + ηA]`, `S`-neighbours at slots 0, 5; receivers slots 2, 3, i.e. the slots
   opposite the `S`-pair — this makes the receivers independent of the labelling at `φ ≈ 0°`
   and `φ ≈ 30°`), `APShape` (A′), `CapShapeP` (cap), `DtShape` (Dt and Dt_II, via
   `KKDShape`).  Tolerances `ηA = ηT = 10⁻³` (paper `0.012° = 2.1·10⁻⁴` and `δ₀ = 10⁻⁴`).
   Region II uses `ShapeII` (type A = `TwoShape` with `φ ≥ 30° − ηA`, both `S`-slots K-row;
   Dt_II = `DtShape`), `shapeII_to_I`.
5. **Merged forwarding** (see Architecture); `ImmSender` is the paper's "sender of `x`".
6. **Intrinsic depths** in `ThI` (`depth X d` = distance to `∂K`; within `10⁻⁵` of the
   paper's frame depth near a good′ point, margins `≥ 0.0075`).
7. **Region II gaps without components**: `NextRung` (next good rung along the pure D-row,
   `TransGen (RowR F)` with no rung D-end strictly between), `walkPt` (the half-open arc
   `[v_A, v_B)` as the K-row walk from `v_A` not reachable from `v_B`), `unbrokenK`
   (`U` = K-ends of unbroken gaps), `rungSign` (sign of `det(u_v, z − v)`, `+1` if `σ = 0`).
   thm:IIBC is stated as `#rungs ≤ #breaks + U + 2` with the existing `breaks`; the special
   case "a row with `≤ 2` points" is absorbed by the `+ 2`.
8. **`Q`**: the paper's `Q` (all of `S` of `Δ₂`-degree `1`) is `Q2`, not `P1set`;
   `VS_weighted` accepts any `Q ⊆ S` with `deg₂ = 1`, so both uses share one `Q`.
9. Mixed T-edges in Region II: the Lean bound is `≤ 1200` (paper `< 71`), so
   `cIIe = cBad + 1300`.

## Dependency DAG (✓ = proved)

```
erdos132_main2116 ✓ ← exists_normalize2116 ✓, main2116_normalized ✓
main2116_normalized ✓ ← degenerate, mult_minDist_le, card_le_of_small2116 ✓, consts2116 ✓,
    tauInv_eq_tau ✓, dirField_nonempty, regionI, regionII_high, regionIIe ✓, W7_I ✓, W7_II ✓,
    assemble2116 ✓ ← VS_weighted, E_bound2116 ✓ (mu_delta_identity), lp2116 ✓
W7_I ✓ ← weight7_of_rules ✓ (charge7 ✓), sendRuleI_of_good ✓, recvI_dest ✓, loadI, card_EP_le ✓
W7_II ✓ ← weight7_of_rules ✓, sendRuleII_of_good ✓, recvII_dest ✓, loadII, card_EP_le ✓
sendRuleI_of_good ✓ ← frameP_of_good ✓, classI_shape ✓, shapeI_facts ✓
sendRuleII_of_good ✓ ← frameP_of_good ✓, IIclass_shape, shapeI_facts ✓, shapeII_to_I ✓
frameP_of_good ✓ ← exists_foot, heavyP_* ✓, far_pointsP
card_EP_le ✓ ← thin_card_leP ✓ (thin_boxP, card_sep_box_le43), turning_geP,
                card_bigTurning_leP, cEP_check ✓
classI_shape ✓ ← S3_mS_le, class62, class63, class53
S3_mS_le, S3_three ← flat_K ✓, flat_D, flat_pin, pair_K2116, pair_D2116, nb_kind ✓
class62 ← hex_of_deg6, flat_*, pair_*, nb_above_D ✓, S3_noD
class63 ← S3_three, hex_of_deg6, flat_pin;   class53 ← S3_three, nb_kind ✓
recvI_dest ✓ ← recvI, dest_ok ✓;  recvI ← flat_*, hex_of_deg6, frameP_close
loadI ← recvI, coneI, ThI, frameP_close;  coneI ← recvI;  ThI ← coneI, recvI, frameP_close
IIclass_shape ← IIS, hex_of_deg6, flat_*, pair_K2116;  recvII ← flat_*, hex_of_deg6
loadII ← recvII, frameP_close
flat_K ✓ ← frameP_outside, FrameP.top ✓;  flat_D ← frameP_D, frameP_dn
flat_pin ← frameP_D, FrameP.normals;  frameP_dn ← frameP_D, FrameP.far
regionIIe ✓ ← IIBC, two_U_le, card_tEdges_add_breaks_le, card_mixedT_le, card_bad_le
IIBC ← IIZ_circle, IIarc_walk, IIdisj_walk, R1_v, R1_z
two_U_le ← IIarc_walk, IIdisj_walk, IIcons_b (← IIcons_a), card_typeOne_le_five, lemmaC
IIarc_walk ← IIZ_circle, IIZ_centre, IIord;  IIdisj_walk ← IIarc_walk, IIord, IIZ_*
IIZ_centre ← IIZ_circle, R1_z;  IIord ← IIZ_circle, IIZ_centre, rung_offset
```

## Remaining lemmas: difficulty and waves

S < 1 h, M a few hours, L a day or more, XL several days.

**Wave 1 (S–M; copies of proved `4/3` lemmas, independent).**
Good: `card_bigTurning_leP` (S–M), `turning_geP` (M), `far_pointsP` (M–L).
Frame: `FrameP.toFrame43` (S), `frameP_outside` (M), `frameP_D` (M), `frameP_dn` (M),
`frameP_close` (M).  ClassI: `S3_noD` (S).  IIe: `IIZ_centre` (S–M, after `IIZ_circle`'s
statement).  IIw: `IIS` (S–M).

**Wave 2 (M).**
Frame: `flat_D`, `flat_pin`, `pair_K2116`, `pair_D2116`, `hex_of_deg6`.  Good: `thin_boxP`
(L, rerun of `thin_box43`).  ClassI: `class63`, `class53`.  IIe: `IIZ_circle` (M–L), `IIord`.
DischI: `coneI`.  IIw: `recvII`.

**Wave 3 (L–XL).**
ClassI: `S3_mS_le`, `S3_three`, `class62`.  DischI: `recvI` (L), `ThI` (M–L), `loadI` (XL).
IIw: `IIclass_shape` (M–L), `loadII` (L).  IIe: `IIarc_walk`, `IIdisj_walk`, `IIBC`,
`IIcons_a`, `IIcons_b`, `two_U_le` (all L).

Parallel fill: one agent per file (`Good`, `Frame`, `ClassI`, `DischI`, `RegionIIw`,
`RegionIIe`); `ClassI`/`DischI`/`RegionIIw` only use `Frame`'s *statements*.

## Constants and margins (checked by hand; a referee should recheck)

- LP: `(5/8)(3/2) + 3/8 = 21/16`; `−(5/8)(1/2) + (3/8)(1/2) = −1/8 ≤ 0`; `(3/8)(7/2) = 21/16`.
- `consts2116`: `(3/8)(2.5·10³² + cIIe) ≤ 10³³`; `3(16·10¹⁵ + 1)² ≈ 7.7·10³² ≤ 10³³`.
- Small case: `Δ ≤ 1.94·2·10¹⁵ ≤ 4·10¹⁵ = ρ`, `n ≤ (4ρ + 1)²`.
- `cEP_check`: `2π·10⁶·(6·10¹¹ + 1)² + 10²³ ≈ 2.26·10³⁰ ≤ 10³²`.
- Far points: `κ = 1.01·10⁻⁶`, `‖d − n‖ ≈ κ > ε₀`; `(Λ − 1)² + (1 + κ(Λ − 1))² < Λ²`;
  height loss `(Λ − 1)κ ≤ 1010.01 ≤ 1011`.  `toFrame43`: `463·1011/(10⁹ − 1) < 9.31`.
- Thin at scale `Λ`: `W ≤ 2.1·10⁹ + L/69`; `L ≥ 3.3·10¹¹ ⇒ W ≤ L/48` (fatness
  contradiction needs `W < 0.058Δ₂`: true for `Δ₂ ≥ 7.3·10¹⁰`); box `4·10¹¹ × 10¹⁰`,
  packing `(8·10¹¹ + 1)(2·10¹⁰ + 1) ≤ 10²³`.
- DN: `(6 + 1011 + 1)/(10⁹ − 7) ≈ 1.02·10⁻⁶ ≤ κD`; D-level spread `12κD = 2.4·10⁻⁵ ≤ δ₀/2`.
- Pinning: `12ε₀ + 144/(2Δ₂) ≤ 1.3·10⁻⁵ ≤ δ₀/5`.  K-row level: `6εP = 1.2·10⁻⁵ ≤ δ₀/5`.
- Frame comparison: `7ε₀ + 5ε₀ = 1.2·10⁻⁵ ≤ δ₀/5`.
- Mirror pairs: K `4·10⁻⁵/0.99 ≤ 10⁻⁴`; D `10⁻⁴/0.99 ≤ 2·10⁻⁴`.
- Shapes: C_φ pinning `cos φ − cos(φ − 60°) = sin(30° − φ)` exactly, error `≤ δ₀/5 ≤ ηT`;
  cap/A′: `|t − 1/2| ≤ 0.87·|φ| + δ₀/5 ≤ ηT` (`|φ| ≤ 4·10⁻⁵` by the mirror pair);
  `KKDShape` `t ≥ sin(ψ₁ − 30°) − ηT` absorbs `|ψ₁ − ψ₂| ≤ 3·10⁻⁵` and pinning.
- `coneI`: `cos(60° + 2ηA) = 0.4983 ≥ 12/25`.
- `ThI` (band Th, `ηT = 10⁻³`): C_φ `φ ≤ 0.73°`; sender near `±60°` has depth `≤ 0.512`,
  `depth d ≤ 0.512 + 0.54 = 1.052 ≤ 1.06`; Dt near `0°`: `cos 60.73° + 0.9986 = 1.4875 ≥ 1.48`
  (smallest margin, `0.0075`).
- Loads (paper tab:margins with `ηT = 10⁻³`): band L `φ ≥ 0.6°`, window `[−59.4°, 59.4°]`;
  band H `ψ₁ ≥ 60.5°`; Region I Dt receivers depth `≥ sin 117.9° = 0.8838 > √3/2`.
- Region II: D-neighbour height `≥ t_II − δ₀/2 > 0.8958 > 0.89`; `IIcons`: `2π/0.99999 < 6.3`,
  `4π/0.99999 < 12.6`; `2U ≤ p + 34`; `e(S) ≤ s + p/2 + cBad + 1219 ≤ … + cIIe`.

## Risks

- **`loadI` is the bulk** (paper lem:loads with four bands, forwarding, lem:Th) and depends on
  the exact content of the shapes.  If the fill agent finds that a shape predicate lacks a
  fact the paper's proof uses, strengthen the shape in `Defs` and re-prove only the producing
  `class*` lemma and `shapeI_facts` (the charge vectors do not change).
- Truth of the shape/receiver encoding: receivers are the slots opposite the `S`-pair
  (`TwoShape`), slot 3 (A′), slots 2, 3, 4 (cap), the two non-`S` neighbours (Dt) — the
  paper's receivers for every labelling admitted by the tolerances (checked at `φ ≈ 0°` and
  `φ ≈ 30°`).
- `IIZ_circle` (the whole component, both directions) and `IIord` (orientation: a right
  T-step, `det(u_p, q − p) < 0`, is counterclockwise about the centre, so `det(v_A − w, v_B − w) > 0`)
  follow the paper (§11.1 refereed once); the orientation convention was checked by hand only.
- §11 as a whole has had **one** referee pass (paper, Status); §10 two.  The statements here
  follow the refereed text; no statement has yet been refereed in Lean form.

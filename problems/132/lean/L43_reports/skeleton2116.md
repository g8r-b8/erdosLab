# Skeleton report: Lean formalisation of Theorem 1(b) (21/16)

Date: 2026-09-25.  Plan: `problems/132/lean/MAIN2116_PLAN.md`.

## Result

`Erdos132Main.erdos132_main2116` is proved from 37 sorried lemma statements; all wiring is
proved (assembly, LP `lp2116`, constants, small cases, normalisation keeping `τ`, region split,
the charging lemma `charge7`, its instance `weight7_of_rules`, `card_EP_le`, `frameP_of_good`,
`regionIIe`, `W7_I`, `W7_II`).

```
#print axioms Erdos132Main.erdos132_main2116
'Erdos132Main.erdos132_main2116' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

There is no `native_decide`/`bv_decide` and no new axiom.  Existing files and `Erdos.lean` are
unchanged.  Each file was compiled alone through `tools/leanslot.sh`, in DAG order.

Statement as proved:

```lean
def tauInv (X : Finset Pt) : ℝ :=
  (diam X ^ 2 - dist2 X ^ 2 - minDist X ^ 2) / (2 * dist2 X * minDist X)
theorem erdos132_main2116 : ∃ C₁ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
    (tauInv X ≤ √3 / 2 - 1 / 50 ∨ √3 / 2 + 3 / 100 ≤ tauInv X) →
    (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 21 / 16 * X.card + C₁
```

The statement needed no adjustment.  Two lemmas are proved:
- `tauInv_eq_tau`: `minDist X = 1 → dist2 X ≠ 0 → tauInv X = tau X`.
- `tauInv_smul`: `tauInv` is invariant under dilation.

`exists_normalize2116` is `exists_normalize` with `tauInv Y = tauInv X` added.  The constant is
`C₁ = C2116 = 10³³` (the paper has `2·10³²`).

## Files (lines / theorems / sorry)

| file | lines | theorems | sorry |
|---|---|---|---|
| `Erdos/Erdos/E132Main2116Defs.lean` | 613 | 16 | 0 |
| `Erdos/Erdos/E132Main2116Good.lean` | 249 | 11 | 4 |
| `Erdos/Erdos/E132Main2116Frame.lean` | 282 | 15 | 10 |
| `Erdos/Erdos/E132Main2116ClassI.lean` | 161 | 7 | 6 |
| `Erdos/Erdos/E132Main2116DischI.lean` | 139 | 5 | 4 |
| `Erdos/Erdos/E132Main2116RegionIIw.lean` | 118 | 5 | 4 |
| `Erdos/Erdos/E132Main2116RegionIIe.lean` | 263 | 10 | 9 |
| `Erdos/Erdos/E132Main2116.lean` | 204 | 8 | 0 |
| **total** | **2029** | **77** | **37** |

The skeleton commit message (`42569cb`) says 78 theorems.  That count included a `theorem` line
inside a docstring code block; the line is now indented, and the correct count is 77.

Import DAG:

```
E132Main43 → 2116Defs → Good; → Frame → {ClassI, DischI, RegionIIw}; → RegionIIe
all → E132Main2116
```

The six fill files are pairwise disjoint.  `ClassI`, `DischI` and `RegionIIw` use only the
statements in `Frame` and the definitions in `Defs`.

## Sorried lemmas

Difficulty: S < 1 h, M a few hours, L a day or more, XL several days.

### Good: lem:fewbad2 and lem:frame at `Λ = 10⁹`, `ε₀ = 10⁻⁶`

| lemma | statement | diff. |
|---|---|---|
| `far_pointsP` | At a good′ point with foot `p₀ = y + hn`, `K` contains points at abscissa `±(Λ−1)` with height `≥ h − 1011`. | M–L |
| `thin_boxP` | Nearly antipodal normals within `Λ` and `Δ₂ ≥ 2·10¹⁵` put `K` in a `4·10¹¹ × 10¹⁰` box. | L |
| `turning_geP` | Non-good and not thin implies turning `≥ ε₀` on `∂K ∩ B̄(y, 150Λ)`. | M |
| `card_bigTurning_leP` | At most `2π·10⁶(6·10¹¹+1)²` points have big turning. | S–M |

### Frame: lem:flatmodel

| lemma | statement | diff. |
|---|---|---|
| `FrameP.toFrame43` | Every `FrameP` is a `Frame43`, so all 4/3 frame lemmas apply. | S |
| `frameP_outside` | A non-interior `q` within 6 has `Z q ≥ h − εP·\|X q\|`. | M |
| `frameP_D` | `z ∈ D` within 6 has `Z z ≥ h + t − εP·\|X z\|`. | M |
| `frameP_dn` | Lemma DN: the partner `w` of `z` is below it, with slope `≤ κD = 2·10⁻⁶`. | M |
| `flat_D` | There is `H ≥ t − δ₀/2` with every D-point within 6 at a level in `[H, H + δ₀/2]`. | M |
| `flat_pin` | K-row `k` and `z ∈ D` within 6 satisfy `\|(Z z − Z k) − t\| ≤ δ₀/5`. | M |
| `frameP_close` | Frames at distance `≤ 3` have normals within `ε₀`; levels differ by `≤ δ₀/5`. | M |
| `pair_K2116` | Two distinct K-row neighbours have abscissae summing to at most `10⁻⁴` in absolute value. | M |
| `pair_D2116` | Two distinct D-neighbours have abscissae summing to at most `2·10⁻⁴` in absolute value. | M |
| `hex_of_deg6` | `deg = 6` means the neighbours form an exact regular hexagon (`IsHexNb`). | M |

### ClassI: lem:S3 and lem:classP4 (Region I or `τ > 1`, `Δ₂ ≥ 2·10¹⁵`, `y ∈ R` with a `FrameP`)

| lemma | statement | diff. |
|---|---|---|
| `S3_noD` | `t > 1 + 2δ₀` means no D-neighbour. | S |
| `S3_mS_le` | `m_y ≤ 3`. | M–L |
| `S3_three` | `m_y = 3` gives `∃ ψ₁ ψ₂, KKDShape` (K-mirror pair, a D between them, `t`-bounds). | M–L |
| `class62` | `(6, 2)` gives a `TwoShape` (types A, B, C_φ) or an `APShape` (A′). | L |
| `class63` | `(6, 3)` gives a `CapShapeP`. | M |
| `class53` | `(5, 3)` gives a `DtShape`. | M |

### DischI: lem:recv2, lem:cone, lem:Th, lem:loads

| lemma | statement | diff. |
|---|---|---|
| `recvI` | A receiver `x` of any `ShapeI` rule is in `R` with `m_x ≤ 1`. If `v(x) = 7`, then `fwdTarget x ∈ nbδ x ∩ R` and has `v ≤ 6`. | L |
| `coneI` | An immediate sender `s` of `d` is a neighbour of `d` with `⟨s − d, n⟩ ≥ 12/25` in a nearby frame. | M |
| `ThI` | Band Th, sender near `±60°`: `depth d ≤ 1.06`. Sender near `0°`: `depth d ≥ 1.48`. | M–L |
| `loadI` | `∀ d ∈ R, Σ_{y∈R} Tr (ShapeI X) X y d ≤ 1`. | XL |

### RegionIIw: §11.2

| lemma | statement | diff. |
|---|---|---|
| `IIS` | D-neighbours have height `> 0.89`; there is at most one; `m_y ≤ 3`. | S–M |
| `IIclass_shape` | Good′ with `v ≥ 8` gives `∃ a, ShapeII` (type A or Dt_II). | M–L |
| `recvII` | Same as `recvI`, for `ShapeII`. | M |
| `loadII` | `∀ d ∈ R, Σ_y Tr (ShapeII X) X y d ≤ 1`. | L |

### RegionIIe: §11.1 (`Normal`, `√3/2 + 3β ≤ τ ≤ 1`)

| lemma | statement | diff. |
|---|---|---|
| `IIZ_circle` | The pure D-row component of a rung D-end lies on `C(w_v, Δ)`. | M–L |
| `IIZ_centre` | Rungs whose D-ends are in one component have the same partner `w`. | S–M |
| `IIord` | `TransGen RowR zA zB` implies `det(vA − w, vB − w) > 0`. | M |
| `IIarc_walk` | Points of `walkPt vA vB` are on `C(w, Δ₂)`, not in `D`, and (if `≠ vA`) in `Q2`. | L |
| `IIdisj_walk` | The walks `[vA, vB)` of distinct gaps are disjoint. | L |
| `IIBC` | `#rungs ≤ #breaks + #unbrokenK + 2`. | L |
| `IIcons_a` | At most 6 unbroken gaps have equal signs. | M–L |
| `IIcons_b` | At most 24 rungs are shared by two unbroken gaps. | M–L |
| `two_U_le` | `2·#unbrokenK ≤ \|Q2\| + 34`. | L |

## Design decisions and deviations

Full list: `MAIN2116_PLAN.md`, section "Deviations".

1. **New frame layer, not parametrised.**
   - `FrameP` is a new concrete structure: normals within `ε₀ = 10⁻⁶` on radius 10, and far points at `±(Λ − 1)`.
   - The 4/3 frame lemmas are proved for `Frame43`'s fixed constants, and those files may not change. Parametrising them would have meant rewriting proved files.
   - Instead, the needed facts are restated at the new scale, with copy-the-4/3-proof hints.
   - The bridge `FrameP.toFrame43` makes every coarse 4/3 lemma available directly.
2. **Goodness is Euclidean-local**, as in 4/3.
   - The exception constant is `cEP = 10³²` (paper `N′_g = 2.6·10²⁵`), because the big-turning count is taken at radius `150Λ`.
   - As a result `C₁ = 10³³` (paper `2·10³²`).
3. **The rules are encoded as shapes.**
   - `TwoShape σ φ` is one predicate for types A, B and C_φ. It uses the exact hexagon, with the `S`-pair at slots 0 and 5; the receivers are slots 2 and 3, the slots opposite the pair.
   - Because receivers are "the slots opposite the pair", they do not depend on the labelling where two labellings are admissible (`φ ≈ 0°`, `φ ≈ 30°`). This was checked by hand.
   - The other shapes are `APShape`, `CapShapeP` and `DtShape` (via `KKDShape`).
   - Tolerances are `ηA = ηT = 10⁻³`, versus the paper's `2.1·10⁻⁴` and `10⁻⁴`.
   - The sender's charge vector is chosen by `Classical.choose` (`sendAmt`). All admissible choices give the same receivers.
4. **Forwarding is merged into one step.**
   - Charge sent to `x` lands at `dest X x`, which is `2x − k` when `v(x) = 7`.
   - The charging lemma `charge7` is then one-level: senders send `≥ v − 7`, charge lands only at weight `≤ 6`, and each load is `≤ 1`. This gives `Σ_R v ≤ 7|R| + 5|E|`.
5. **Region II gaps are defined without graph components.**
   - `NextRung` uses `TransGen (RowR F)` along the D-row, with no rung D-end strictly between.
   - `walkPt` is the K-row walk from `v_A`, restricted to points not reachable from `v_B`.
   - `unbrokenK` is the set of K-ends of unbroken gaps, so `U = |unbrokenK|`.
   - thm:IIBC is stated as `ρ ≤ |breaks| + U + 2`, using the existing `breaks`.
   - The paper's `Q` is `Q2` (all of `S` with `deg₂ = 1`), not `P1set`. `VS_weighted` accepts `Q2`.
6. **Other constants.**
   - The Lean bound on mixed T-edges in Region II is 1200 (paper 71), so `cIIe = cBad + 1300`.
   - `ThI` uses the intrinsic depth, which is within `10⁻⁵` of the frame depth.

## Doubts about statement truth (for the referee)

No statement is known to be false.  Every statement follows the paper's refereed text.  The
riskiest points:

1. **`loadI`** is true only if the shape predicates carry enough of the paper's classification. They carry exact hexagon slots, `S`/`D` membership, and pinned `t`-values within `10⁻³`.
   - The smallest paper margin, 0.65° in bands L and H, shrinks to about 0.5° with `ηT = 10⁻³`.
   - The `ThI` Dt margin is `1.4875` against `1.48`.
   - If a missing fact turns up, strengthen the shape in `Defs` and re-prove the matching `class*` lemma. The charge vectors do not change.
2. **Orientation in `IIord`.** A right T-step (`det(u_p, q−p) < 0`) is taken to be counterclockwise about the centre, so the conclusion is `det(vA − w, vB − w) > 0`. This was checked by hand only.
3. **`IIZ_circle`** is stated for the whole component, in both directions. This is the paper's lem:IIZ(a), which has had one referee pass.
4. **`TwoShape` near `φ ≈ π/6 + ηA`.** Slot 5 can be a D-point while slot 0 is K-row, for tiny `t`. This is the paper's C_φ with the other labelling, and the receivers are the same. `recvI` and `loadI` must handle both labellings.
5. **`S3_mS_le` for `1 < t ≤ 1 + 2δ₀`.** The `m = 4` case is excluded by pinning (`t ≈ 0.866`), not by `S3_noD`.
6. **`frameP_D` at radius 6.** Moving `z` down by up to `t ≤ 6` can leave the radius-6 ball. The radius-10 normals of `FrameP` are there to cover this.
7. **Status of the source.** §11 (IIe, IIw) has had one referee pass in the paper; §10 has had two. No Lean statement here has been refereed yet. A statement referee pass is recommended before the fill waves.

## Commits

- `97262b0`: Defs
- `94912eb`: Good
- `2491187`: Frame
- `1f6776b`: ClassI
- `18c5fcc`: DischI and IIw
- `6cd1576`: IIe
- `42569cb`: main skeleton commit
- `3ff9f7f`: docstring fix
- Plan and this report: committed with them.

# ✅ 54/37 theorem fully formalised (2026-09-23)

`Erdos132Main.erdos132_main : ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card → (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 54/37 * X.card + C₀`

- No `sorry`; `#print axioms` = `[propext, Classical.choice, Quot.sound]` (no native_decide / bv_decide).
- Files: E132MainDefs, E132MainLocal, E132MainRegions, E132MainDegen, E132Main, E132ConvexCurve, E132Ve87 (+ E132Layer, E132ConvexFinset).
- Also sorry-free and standard-axioms-only: Vesztergombi 1987 (`vesztergombi87`), Hopf–Pannwitz, Cor A1 (`Erdos132Layer.corA1`).
- `cd Erdos && lake build` builds everything (all modules imported from `Erdos.lean`). See MAIN_PLAN.md for deviations from the paper's proof.

# Erdős #132: Lean formalisation (convex case n = 7, 11, 13; layer bound Theorem A / Cor A1)

Files (in `Erdos/Erdos/`):

| file | contents | check time |
|---|---|---|
| `E132Convex.lean` | ordered-polygon theorems for n = 7, 11; geometry, Lemma R, BitVec encoding | ~90 s (n = 7 LRAT pinned, n = 11 runs CaDiCaL ~20 s) |
| `E132ConvexFinset.lean` | point-set (`Finset`) versions for n = 7, 11; the bridge from convex position to an ordered polygon | ~60 s |
| `E132Convex13.lean` | n = 13, both versions | ~9 min (CaDiCaL + LRAT check) |
| `lrat/bvNoCE7.lrat` | pinned LRAT certificate for n = 7 (1.6 MB) | — |
| `E132Layer.lean` | layer bound: location lemma, Prop 3, degree ≤ 4, Theorem A, Corollary A1 (paper §"A layer bound") | ~25 s |

Check a single file with `cd Erdos && lake env lean Erdos/<file>`. `Erdos.lean` imports `E132Convex`,
`E132ConvexFinset` and `E132Layer`, so a plain `lake build` checks them (measured before `E132Layer` was
added: 2 min 17 s incremental, roughly 3–4 min from a clean E132 build; `E132Layer` adds about 25 s). `E132Convex13` is **not** imported, because it adds about 9 minutes; build it with
`lake build Erdos.E132Convex13`.

## Status: all theorems are sorry-free

Ordered polygons (`E132Convex.lean`, `E132Convex13.lean`):

```
theorem erdos132_convex7  (p : Fin 7  → EuclideanSpace ℝ (Fin 2)) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card
theorem erdos132_convex11 (p : Fin 11 → EuclideanSpace ℝ (Fin 2)) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card
theorem erdos132_convex13 (p : Fin 13 → EuclideanSpace ℝ (Fin 2)) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card
```

Point sets (`E132ConvexFinset.lean`, `E132Convex13.lean`). Here `Pt = EuclideanSpace ℝ (Fin 2)`:

```
theorem erdos132_convex7_finset  (S : Finset Pt) (hn : S.card = 7)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card
theorem erdos132_convex11_finset (S : Finset Pt) (hn : S.card = 11)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card
theorem erdos132_convex13_finset (S : Finset Pt) (hn : S.card = 13)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card
```

- **Convex position** is Mathlib's `ConvexIndependent ℝ ((↑) : S → Pt)`: no point of `S` is in the convex hull of
  the other points (`convexIndependent_set_iff_notMem_convexHull_sdiff`).
- **Pairs** are unordered: `pairsS S = S.sym2.filter (¬ IsDiag)`, i.e. the sets `{x, y} ⊆ S` with `x ≠ y`.
- `pairDist` is the distance of a pair.
- `multS S d` is the number of pairs at distance `d`.
- `distSetS S` is the set of distances determined by `S`.
- `rareDistsS S = (distSetS S).filter (multS S · ≤ S.card)`. So a distance is rare when `1 ≤ #pairs ≤ n`.

`#print axioms` output (all six main theorems):

```
'Erdos132Convex.erdos132_convex7' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex11' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE11._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex13' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE13._native.bv_decide.ax_1_10]
'Erdos132Convex.erdos132_convex7_finset' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex11_finset' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE11._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex13_finset' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE13._native.bv_decide.ax_1_10]
```

The bridge itself (`exists_strictConvexPolygon`, `rareDistsS_eq`) uses only `propext, Classical.choice, Quot.sound`.
The only non-standard axioms are the `bv_decide` ones described next. For n = 7 the certificate is replayed with
`bv_check "lrat/bvNoCE7.lrat"`, and it records the same kind of axiom.

where, for example,

```
axiom Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14 :
  Std.Tactic.BVDecide.Reflect.verifyBVExpr bvNoCE7._expr_def_1_10 bvNoCE7._cert_def_1_10 = true
```

**Disclosure (PROMPT.md rule).** These auxiliary axioms are how `bv_decide` in this toolchain (v4.35.0-rc2)
records its one unverified step. Older toolchains used `Lean.ofReduceBool` for the same step, and it has
the same trust base as `native_decide`. The axiom says that Lean's LRAT checker `verifyBVExpr` returns
`true` on these concrete inputs. The checker itself is proved correct in Lean, including its bit-blaster
and AIG→CNF translation. The `true` answer comes from running the compiled checker, not from the kernel.
What is trusted: the Lean compiler and runtime, and the fact that the compiled `verifyBVExpr` matches its
definition. What is **not** trusted: CaDiCaL, our CNF encoder `b3_sat.py`, and drat-trim. None of them
is involved.

## Sorry count per file

`grep -c sorry Erdos/Erdos/<file>` (2026-09-23):

| file | `sorry` |
|---|---|
| `E132Convex.lean` | 0 |
| `E132ConvexFinset.lean` | 0 |
| `E132Convex13.lean` | 0 |
| `E132Layer.lean` | 0 |

`E132Main.lean` and the `E132Main*.lean` companions (the 54/37 skeleton), together with `MAIN_PLAN.md`,
are maintained by the separate Part 2 effort. They are scaffold files with `sorry` bodies by design;
see `MAIN_PLAN.md` for their status.

## The layer bound (`E132Layer.lean`): sorry-free

This file formalises the section "A layer bound and a new class of sets" of `paper/paper.tex`
(= `angle_C.md` Theorem A / Cor A1, `VERIFY_A1b.md` Prop 3, `VERIFY_A1c.md` Lemma M / Lemma F).
Namespace `Erdos132Layer`, `Pt = EuclideanSpace ℝ (Fin 2)`, `μ(d) = multS X d` (unordered pairs, as in
`E132ConvexFinset`). No `native_decide`, no `bv_decide`.

### Definitions

- `TwoLargest X Δ Δ₂`: `Δ` is the largest element of `distSetS X` and `Δ₂` the largest one below it
  (`exists_twoLargest`: satisfiable as soon as `X` determines two distances).
- `IsExt S p`: `p ∈ S` and an open half-plane bounded by a line through `p` contains `S \ {p}`.
  `isExt_iff_notMem_convexHull`: for a finite set this is `p ∉ conv(S \ {p})` (Hahn–Banach), so
  `L1 X` is the vertex set of `conv X`. `L2 X` = extreme points of `X \ L1 X`.
- `nbr V d v` = `d`-neighbours of `v` inside `V`; `esum V d = Σ_{v ∈ V} deg_V v` (twice the edge count).
- `core V d` (the 2-core): the union of all `S ⊆ V` in which every vertex has `≥ 2` neighbours inside
  `S`. This is the largest such set, which is what repeated deletion of vertices of degree `< 2`
  leaves. Instead of modelling the deletion process we prove its one consequence that is used,
  `esum_le_core`: `esum V ≤ esum (core V) + 2·|V \ core V|` (strong induction, deleting a vertex of
  degree `≤ 1` outside the core).

### Main statements

```
theorem isExt_of_dist_max    (hT : TwoLargest X Δ Δ₂) (hp : p ∈ X) (hq : q ∈ X) (h : dist p q = Δ) : IsExt X p
theorem dist_le_snd_of_not_isExt (hT) (hq : q ∈ X) (hqe : ¬ IsExt X q) (hx : x ∈ X) : dist q x ≤ Δ₂
theorem mem_L1_or_of_dist_snd (hT) (hp) (hq) (h : dist p q = Δ₂) : p ∈ L1 X ∨ q ∈ L1 X
theorem mem_L12_of_dist_snd   (hT) (hp) (hq) (h : dist p q = Δ₂) : p ∈ L1 X ∪ L2 X

-- Prop 3 (VERIFY_A1b): core vertices of L₂ have core degree 2
theorem deg_core_L2 (hT : TwoLargest X Δ Δ₂) (hq : q ∈ L2 X) (hK : q ∈ core (L1 X ∪ L2 X) Δ₂) :
    (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ q).card = 2
-- degree ≤ 4 on L₁′ (VERIFY_A1c)
theorem deg_core_L1_le_four (hT) (hp : p ∈ L1 X) (hK : p ∈ core (L1 X ∪ L2 X) Δ₂) :
    (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card ≤ 4

-- Theorem A (doubled, in ℕ; deg′ ≥ 2 on the core so the truncated subtraction is exact)
theorem theoremA (hT : TwoLargest X Δ Δ₂) :
    2 * multS X Δ₂ ≤ 2 * (L1 X).card + 2 * (L2 X).card +
      ∑ p ∈ L1 X ∩ core (L1 X ∪ L2 X) Δ₂, ((nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card - 2)
-- Corollary A1, under (H3): no point of L₁ has ≥ 4 points at distance Δ₂
theorem corA1 (hT) (hH3 : ∀ p ∈ L1 X, (nbr X Δ₂ p).card ≤ 3) :
    2 * multS X Δ₂ ≤ 3 * (L1 X).card + 2 * (L2 X).card
theorem corA1_le_card (hT) (hH3) (h : (L1 X).card ≤ 2 * (X.card - (L1 X).card - (L2 X).card)) :
    multS X Δ₂ ≤ X.card
-- unconditional form, h(p) = (nbr X Δ₂ p).card, (·)⁺ = truncated subtraction
theorem corA1_uncond (hT) :
    2 * multS X Δ₂ ≤ 2 * (L1 X).card + 2 * (L2 X).card + ∑ p ∈ L1 X, (min (nbr X Δ₂ p).card 4 - 2)
theorem cdl_layer_bound (hT) : multS X Δ₂ ≤ 2 * (L1 X).card + (L2 X).card
```

`#print axioms` (at the end of the file) for `theoremA`, `corA1`, `corA1_uncond`, `cdl_layer_bound`,
`corA1_le_card`, `deg_core_L2`, `deg_core_L1_le_four`, `isExt_iff_notMem_convexHull`,
`exists_twoLargest`:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Proof structure

| paper step | Lean | notes |
|---|---|---|
| location lemma (i), (ii) | `isExt_of_disk`, `isExt_of_dist_max`, `dist_le_snd_of_not_isExt`, `mem_L1_or_of_dist_snd`, `mem_L12_of_dist_snd` | a boundary point of a disc containing the set is exposed (normal `q − c`) |
| `G` contains every `Δ₂`-pair | `esum_eq_esum_L12`, `two_mul_multS` | handshake by a 2-to-1 fibre count onto `pairsS` |
| pruning estimate | `esum_insert`, `esum_le_core` | |
| **frames** | `fx`, `fy`, `frame_sqd`, `frame_cross`, `frame_dot` | frame at `q` with axis `v`, `v ↦ (1,0)`, squared distances divided by `sqd q v`; no square roots |
| Prop 3, Case 3 | `case3_real`, `case3_real'`, `case3_select_real`, `circle3_real` → `prop3_case3_core`, `prop3_case3` | witness `t` from non-extremality; if `v₂` does not separate `v₁, v₃`, the one of them with smaller `|y|` does |
| Prop 3, Case 2 | `case2_aux_real`, `case2_real` → `prop3_case2` | the identity `2(1+c)(1−ρ)(2−ρ) + 4c² − 3 = 0` forces `ρ = 1`, `c² = 3/4`, then the other distance is `2 ∈ (1, D)` |
| Prop 3, Case 1 | `cand_real`, `case1_pair_real`, `far_real`, `case1_real` → `prop3_case1` | candidates `r = (ρ−2/3)A + (ρ−4/3)C`, `ρ² − 3ρ + 4/3 = 0` (coordinate-free, no explicit `√33`); incompatible pairs are at `4/3` or `3ρ` |
| Prop 3 | `prop3_three`, `deg_core_L2` | 8-way split on which pairs are at `Δ` |
| Lemma M, chord monotonicity | `lemmaM_real`, `chord_real` | `(A·W − A·B)(1 + W·B) = (W×B)(A×W + A×B)` |
| Lemma F | `lemmaF_real`, `lemmaF_end_real` → `lemmaF` | `r ∥ a₁ + a₂` forces `x₁ + x₂ < 0` |
| angular order | `eq_of_orient_zero`, `exists_median` | slope `g x = (n × (x−p)) / (n·(x−p))` w.r.t. the supporting half-plane; sort 5 values with `orderEmbOfFin` |
| degree ≤ 4 | `deg_core_L1_le_four` | the hypothesis `p ∈ core` is not needed |
| Theorem A, Cor A1, unconditional form, CDL bound | `theoremA`, `corA1`, `corA1_uncond`, `cdl_layer_bound`, `corA1_le_card` | |

All planar case analyses reduce to lemmas about real numbers (suffix `_real`) closed by
`linear_combination` / `linarith` / small `nlinarith` calls; the polynomial identities were
cross-checked with sympy.

## What is formalised (convex case)

- `StrictConvexPolygon p`: `∀ i < j < k, 0 < orient (p i) (p j) (p k)`. The vertices of a strictly
  convex polygon are listed counter-clockwise, and *every* index-increasing triple is positively
  oriented, not just consecutive ones.
- `distSet p`: the distinct distances over the pairs `i < j`.
- `mult p d`: the number of pairs at distance `d`.
- `rareDists p = {d ∈ distSet p | mult p d ≤ n}`. Membership in `distSet` already gives `mult ≥ 1`.

Proof chain, with the Lean names:

| step | Lean | notes |
|---|---|---|
| Lemma Q (geometry) | `quad_ineq`, `lemmaQ` | Diagonal intersection `O = lineMap A C t = lineMap B E s`, with `t, s` explicit ratios of orientations. `dist_add_dist_eq_iff` (strict convexity of ℝ²) gives equality on the diagonals and strict inequality on the sides, because `O` is off every side line (orientation ≠ 0). |
| ranks | `rk`, `rank`, `rk_le_iff`, `rank_lt_card`, `qord_rank` | Rank = number of distinct distances below. Order-embedding on `distSet`, so the rank colouring satisfies the ordinal `QOrd`. |
| Lemma R | `sum_mult`, `lemmaR`, `main_of_ord` | If ≤ 2 distances are rare, then `(D−2)(n+1) ≤ C(n,2)`, so `D ≤ Dm`: `Dm = 4` for n = 7 (24 > 21) and `Dm = 6` for n = 11 (60 > 55). |
| transfer | `rare_of_ord` | A rare colour class gives a rare distance, injectively. |
| ordinal statement | `OrdNoCE n Dm` | Every `QOrd` colouring with colours `< Dm` has ≥ 3 classes of size in `[1, n]`. This covers all `D ≤ Dm` at once, with unused colours allowed, so there is no case split on `D` or `F`. |
| encoding correctness | `ordNoCE_of_bv` (+ `foldr_ite_toNat`, `countP_eq_card`, `pairsGen`, `quadsGen`) | `BVNoCE` implies `OrdNoCE`, proved in Lean. Colours are `BitVec 3`, class sizes are 8-bit sums of indicators (no overflow, since 55 < 256), and the rare count is a 4-bit sum. Lemma Q appears as 4 BitVec comparisons per quadruple (330 quadruples for n = 11). |
| certificate | `bvNoCE7`, `bvNoCE11` | `simp` unfolds the literal lists into a quantifier-free BitVec formula, then `bv_decide` runs the bundled CaDiCaL (LRAT) and the verified checker. n = 7: under 1 s. n = 11: ~21 s of SAT, ~43 s total (timeout raised to 3000 s). |

The CNF is never written by hand. It comes from Lean's verified bit-blaster, applied to a formula whose
meaning is proved in `ordNoCE_of_bv`. So the "encoding soundness" gap listed in `angle_B3.md` §6 is closed
for n = 7 and n = 11.

## The point-set bridge (`E132ConvexFinset.lean`)

`exists_strictConvexPolygon`: if `S` is in convex position, then there are an `m` and a `p : Fin m → Pt` with
`p` injective, `range p = S` and `StrictConvexPolygon p`. The proof:

1. `mem_hull3` and `hull_of_orient`: barycentric coordinates. If `P` is on the inner side of all three edges of a
   positively oriented triangle `ABC`, then `P ∈ conv{A, B, C}`. Each weight is `orient(…)/orient A B C`.
2. `orient_ne_zero`: three distinct points of `S` are never collinear. Write `z − x = t(y − x)`. Depending on
   `t < 0`, `t ∈ [0, 1]` or `t > 1`, one of the three points lies in the segment of the other two.
3. Pick any `p₀ ∈ S` (it does not have to be lexicographically least) and set `a ≺ b :⇔ 0 < orient p₀ a b` on
   `S \ {p₀}`.
   - It is total by step 2.
   - It is transitive (`orient_trans`): if `a ≺ b ≺ c` but `orient p₀ a c ≤ 0`, then `p₀ ∈ conv{a, b, c}`.
   - `orient_pos_of_lt`: for `a ≺ b ≺ c`, `orient a b c ≤ 0` would put `b ∈ conv{p₀, a, c}`.
4. `linearOrderOfSTO` and `Fintype.orderIsoFinOfCardEq` list `S \ {p₀}` in `≺` order. `Fin.cons p₀` then gives
   the polygon.

`rareDistsS_eq`: for such a listing, `rareDistsS S = rareDists p`. The map `(i, j) ↦ s(p i, p j)` is a bijection
from the pairs `i < j` onto `pairsS S` that preserves distance. `finset_of_polygon` combines the two results.

## Remaining gaps / possible follow-ups

1. **Removing the `bv_decide` axiom.** This would mean checking `verifyBVExpr … = true` in the kernel
   (`decide +kernel`). The LRAT certificate is stored as a string and parsed, so kernel evaluation is very likely
   infeasible. Attempt: `decide +kernel` on the n = 7 axiom statement ran for more than 20 minutes without
   finishing, and was stopped. A fully kernel-checked alternative would need a custom LRAT checker designed for
   kernel reduction. It is not done.
2. **Pinned certificates.** Only n = 7 is pinned (`lrat/bvNoCE7.lrat`, 1.6 MB). The trimmed LRAT from
   `bv_decide?` is 23 MB for n = 11 and 97 MB for n = 13. Both are over the ~20 MB limit for the repo, so those
   two still run CaDiCaL on every compilation: about 20 s for n = 11, and several minutes for n = 13.
3. **n = 13 cost.** `E132Convex13.lean` takes about 9 minutes (309 s user) and peaks at roughly 1.5 GB RSS. It
   is kept out of `Erdos.lean`.
4. **n ≥ 15.** Not attempted. The (15,8,6) order-encoding instance is still unresolved even outside Lean
   (`angle_B3.md`).

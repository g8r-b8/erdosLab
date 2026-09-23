# Erdős #132, convex case: Lean formalisation of Theorems 7 and 11 (angle B3)

File: `Erdos/Erdos/E132Convex.lean`. Check it with `cd Erdos && lake env lean Erdos/E132Convex.lean`.

## Statement formalised

`StrictConvexPolygon p` for `p : Fin n → EuclideanSpace ℝ (Fin 2)` means that every index-increasing
triple `i < j < k` is positively oriented. This is a strictly convex polygon with its vertices
listed counter-clockwise. `rareDists p` is the set of distances `d` that occur among the pairs
`i < j` with multiplicity `1 ≤ mult ≤ n`.

- `erdos132_convex7 : StrictConvexPolygon p → 3 ≤ (rareDists p).card` for `n = 7`
- `erdos132_convex11`: the same for `n = 11`

## Plan (scaffold-then-fill)

| step | Lean names | status |
|---|---|---|
| (a) Geometry, Lemma Q via the diagonal intersection point | `orient_*`, `dist_lt_of_orient_ne`, `quad_ineq`, `lemmaQ` | skeleton |
| (b) Ordinal reduction: ranks, Lemma R, transfer | `rank_*`, `qord_rank`, `sum_mult`, `lemmaR`, `rare_of_ord`, `main_of_ord` | skeleton |
| (b') Encoding correctness, `BitVec` statement ⇒ ordinal statement | `ordNoCE_of_bv` | skeleton |
| (c) Certificates | `bvNoCE7`, `bvNoCE11` (`bv_decide`) | skeleton |
| main theorems | `erdos132_convex7`, `erdos132_convex11` | skeleton |

## Certificate mechanism (c)

`bv_decide`, from Lean core `Std.Tactic.BVDecide`, works in three stages:
1. It bit-blasts the goal with a bit-blaster that is proved correct in Lean.
2. It runs the bundled CaDiCaL to get an LRAT proof.
3. It checks that proof with an LRAT checker that is also verified in Lean.

The one step that is not kernel-checked is running the compiled checker. In this toolchain
(v4.35.0-rc2), `bv_decide` records that step as an **auxiliary axiom**. For example:

    axiom bvNoCE11._native.bv_decide.ax_1_5 :
      Std.Tactic.BVDecide.Reflect.verifyBVExpr bvNoCE11._expr_def_1_1 bvNoCE11._cert_def_1_1 = true

This replaces the older `Lean.ofReduceBool`, and it has the same trust base as `native_decide`.

The CNF encoding does not need to be trusted. The only hand-written encoding step is
`ordNoCE_of_bv`, which is proved in Lean: a `QOrd` colouring gives a `BitVec` model. Lean's
verified bit-blaster does everything after that.

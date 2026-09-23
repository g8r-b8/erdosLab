# Erdős #132, convex case: Lean formalisation of Theorems 7 and 11 (angle B3)

File: `Erdos/Erdos/E132Convex.lean` (~560 lines, of which 80 are generated literal lists). Check it with

    cd Erdos && lake env lean Erdos/E132Convex.lean     # ~75 s: ~1 s + ~20 s of CaDiCaL inside bv_decide

The file is **not** imported by `Erdos.lean`, so a plain `lake build` does not re-run the SAT solver.

## Status: both theorems are sorry-free

```
theorem erdos132_convex7  (p : Fin 7  → EuclideanSpace ℝ (Fin 2)) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card
theorem erdos132_convex11 (p : Fin 11 → EuclideanSpace ℝ (Fin 2)) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card
```

`#print axioms` output:

```
'Erdos132Convex.erdos132_convex7' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex11' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE11._native.bv_decide.ax_1_14]
```

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

## What is formalised

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

## Remaining gaps / possible follow-ups

1. **Point set to ordered polygon.** The theorems take an ordered polygon. A version for
   `S : Finset ℝ²` with `S.card = 11` and `ConvexIndependent` would also need this bridge: a
   convex-independent finite planar set can be listed so that every increasing triple is positively
   oriented, e.g. by sorting by angle around the lowest point. That is standard but not trivial to
   formalise, and it has not been done.
2. **Removing the `bv_decide` axiom.** This would mean checking `verifyBVExpr … = true` in the kernel
   (`decide +kernel`). The LRAT certificate is stored as a string and parsed, so kernel evaluation is
   very likely infeasible. Attempt: `decide +kernel` on the n = 7 axiom statement ran for > 20 min without finishing, and was stopped. A fully kernel-checked
   alternative would need a custom LRAT checker designed for kernel reduction. It is not done.
3. **Time and reproducibility.** Each compilation re-runs CaDiCaL. `bv_decide?` / `bv_check "file.lrat"`
   could pin the LRAT files in the repo, but they are not stored.
4. **n = 13.** This should work the same way (`OrdNoCE 13 7`: (7−1)·14 = 84 > 78). The binary BitVec
   encoding may be much harder for CaDiCaL than the order encoding, for which (13,7,5) took ~100 s.
   Not tried.

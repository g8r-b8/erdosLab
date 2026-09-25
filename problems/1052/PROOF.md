# Fixed-m classification of unitary perfect numbers: soundness of the search

Setting: N = 2^m · n, n odd, with odd unitary components q_1 < … < q_r (pairwise coprime odd prime powers, n = ∏ q_i).
Since σ* is multiplicative with σ*(p^a) = p^a + 1:

  σ*(N) = 2N  ⇔  (2^m + 1) ∏ (q_i + 1) = 2^{m+1} ∏ q_i  ⇔  ∏ (1 + 1/q_i) = T_m := 2^{m+1}/(2^m + 1).   (★)

Every unitary perfect N is even (Subbarao–Warren 1966), so m ≥ 1.

## Rules used by `scripts/fixm.gp` (each is a necessary condition, so pruning is sound)

- **(R) required primes.** TODO: proof that every odd prime of 2^m + 1 and of each q_i + 1 divides n.
- **(B) 2-adic budget.** TODO: Σ v₂(q_i + 1) = m + 1 with every term ≥ 1 (so r ≤ m + 1), and
  v₂(p^a + 1) = v₂(p + 1) for a odd, 1 for a even.
- **(W) ratio window.** TODO: the next (smallest remaining) component q of r remaining satisfies
  1/(T − 1) < q and (1 + 1/q)^r > T, hence q < r·T/(T − 1).
- **(F) free-component window.** TODO: with u unchosen required primes, each contributes at most 1 + 1/s_min,
  so the smallest free component q satisfies (1 + 1/q)^{r−u} ≥ T / ∏ (1 + 1/s_min).
- **(D) last two components.** TODO: ((a−b)x − b)((a−b)y − b) = ab for T = a/b; both factors are positive.
- **Rigour of arithmetic.** TODO: exact rationals throughout; `factor_proven = 1`; `isprimepower` proves primality.

## Results

TODO: table of m, nodes, time, solutions.

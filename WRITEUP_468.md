# Erdős Problem #468 — `f(N) = o(N)` fails, even for almost all `N`

**Problem.** For `n` let `D_n` be the set of sums `d₁, d₁+d₂, d₁+d₂+d₃, …` where
`1 < d₁ < d₂ < ⋯` are the divisors of `n`. Let `f(N)` be the least `n` with `N ∈ D_n`.
Is `f(N) = o(N)`? Perhaps just for almost all `N`?

**Answer: no.** For every `K ≥ 1` and every `X`,

    #{ N < X : N ∈ D_n for some n ≤ N/K }  ≤  S · X / K²,     S = ζ(2) · Σ_{b≥1} H_b / b² = 2 ζ(2) ζ(3) ≈ 3.955.

So `f(N) > N/3` for more than 56% of all `N < X` (for every `X`). In particular, "`f(N) ≤ εN` for
almost all `N`" is false for every `ε < 1/2` (take `K = 1/ε`, bound `≈ 3.96 ε² < 1`).
This matches Vjeko Kovač's data on the forum (e.g. at `X = 2·10⁵`: 31.9% of `N` have
`f(N) ≤ N`, 4.6% have `f(N) ≤ N/2`, 0.4% have `f(N) ≤ N/3`).

## Proof

Fix `K ≥ 1`. Suppose `N ∈ D_n` with `Kn ≤ N`. Then `N` is the prefix sum up to some divisor
`d > 1` of `n`; write `d = n/e` with `e ∣ n`. Substituting `d' = n/e'`,

    N ≤ Σ_{d' ∣ n, d' ≤ d} d' = n · Σ_{e' ∣ n, e' ≥ e} 1/e' =: n · T_e(n).

Hence `T_e(n) ≥ K`, and `n ≤ X/K` if `N < X`. The map `(n, e) ↦ N` is onto the set being counted, so

    #{…} ≤ Σ_{n ≤ X/K} #{ e ∣ n : T_e(n) ≥ K }  ≤  (1/K) Σ_{n ≤ X/K} Σ_{e ∣ n} T_e(n)        (Markov).

It remains to show `Σ_{n ≤ Y} Σ_{e ∣ n} T_e(n) ≤ S·Y`. Swap the order of summation:

    Σ_{n ≤ Y} Σ_{e ∣ n} Σ_{e' ∣ n, e' ≥ e} 1/e'
      = Σ_{e ≤ e'} (1/e') · #{ n ≤ Y : lcm(e, e') ∣ n }
      ≤ Y Σ_{e'} (1/e'²) Σ_{e ≤ e'} gcd(e, e') / e.

Since `gcd(e, e') ≤ Σ_{g ∣ e', g ∣ e} g`, the inner sum is at most
`Σ_{g ∣ e'} Σ_{a ≤ e'/g} 1/a = Σ_{g ∣ e'} H(e'/g)`. Writing `e' = g·b`,

    Σ_{e'} (1/e'²) Σ_{g ∣ e'} H(e'/g) = Σ_{g, b} H_b / (g² b²) = ζ(2) Σ_b H_b / b² = S.

Putting it together: `#{…} ≤ (1/K) · S · (X/K) = S X / K²`. ∎

## Remarks
* The same argument shows `Σ_{n ≤ Y} #{j : d₁+⋯+d_j ≥ Kn} ≪ Y/K`: large prefix sums of
  divisors are rare on average, even though `limsup σ(n)/n = ∞`.
* On the literal "all `N`" reading: if `f(N) = o(N)` held along every `N` for which `f(N)` is
  defined, then the set `R` of such `N` would have density 0 (it would lie inside the covered set
  above for every `K`). So `f(N) = o(N)` fails unless `R` itself has density 0. Numerically `R`
  has density ≈ 1: 99.985% of `N < 20000` lie in some `D_n` with `n ≤ 10⁶`. A rigorous proof
  that `R` has positive upper density (e.g. via a Romanov-type sieve argument on the families
  `N = σ(a) − 1 + p`) would settle the literal version too; we have not written this down.
* **Lean 4 / Mathlib formalisation:** `Erdos/Erdos/E468.lean` in this repo proves
  `card_covered_le : #covered(K, X) ≤ S·X/K²` and `not_erdos468AlmostAll`, which negates
  the "almost all" statement in the form used by google-deepmind/formal-conjectures PR #4076
  (a function `f` that is the minimal preimage on a density-1 set and is `o(N)`).

# Erdős Problem #468: prefix sums of divisors

> **⚠ NOT NEW — DO NOT POST AS A NEW RESULT (found 2026-09-22 by the parallel audit session).**
> Terence Tao proved the same bound (upper density of {N : f(N) ≤ δN} ≪ δ², same first-moment
> method) on **2025-11-01** in the #468 thread; the comment was later **moved to the #1054 thread**
> (#1054 = same f with divisor 1 counted, Guy B2, OEIS A167485), so the #468 page showed nothing.
> #1054 page: "The strong claim that f(n)=o(n) was disproved by Tao in the comments to [468]".
> Later: Kovač (2026-05-11) ≪ exp(−e^{(1/δ)^c}); Liam Price/GPT-5.5 Pro O_k(δ^k); jif (2026-04-16)
> every n ≥ 6 representable (so the Romanov step is unnecessary); Principia Math (Jun–Jul 2026)
> limsup f(N)/N = ∞ with full Lean formalisation. Evidence: forum/thread/1054, erdosproblems.com/1054.
> Full review: `NOVELTY.md`. Note: the Romanov hypothesis is unnecessary — jif's result makes
> every N except 1, 4 reachable, so Tao + jif already disprove the literal version.
> What remains ours: an independent Lean formalisation in formal-conjectures' #468 form (PR #4076),
> with explicit constant S = 2ζ(2)ζ(3). Marginal value at best.

**Status (ours):** (superseded, see above) DISPROVED, "almost all N" version; Lean-verified, sorry-free.
Literal "all N" version: DISPROVED on paper via Romanov's theorem. Lean proves it
conditional only on "R has positive upper density" (explicit hypothesis, not an axiom).
**Prize:** none.
**Site status:** OPEN (as of 2026-09-22).

## Statement
D_n = {d₁, d₁+d₂, …} where 1<d₁<d₂<⋯ are the divisors of n. f(N) = least n with N ∈ D_n.
Is f(N) = o(N)? Perhaps just for almost all N? (Also: what is |D_n \ ∪_{m<n} D_m|?)

## Prior work (what we found)
- **Source:** Erdős–Graham 1980 problem book [ErGr80]. Also Guy, *Unsolved Problems in Number
  Theory*, §B2 (cited by OEIS A167485).
- **OEIS A167485** (F. T. Adams-Watters, 2009): least m with n a prefix sum of the divisors
  of m (0 if none). It asks "Is a(n) = o(n)?" and notes liminf a(n)/n = 0. Only zeros observed
  are at n = 2, 5; that all n > 5 are representable "could follow from a strengthened Goldbach".
  (A167485 may include the divisor 1, which differs slightly from the site's `1<d₁` convention.)
- **OEIS A387502 / A387503** (V. Kovač, 2025-08-31): number of "debut" sums |D_n \ ∪_{m<n} D_m|
  and cumulative count. Average ≈ 0.8349 over n ≤ 10⁵; record indices 2, 12, 36, 144, 336, 1320, …
- **Forum** (only comment, Vjeko_Kovac, 2025-09-14): data suggests f(N) = o(N) is false;
  31.3% of N ≤ 10⁵ have f(N) > 10⁵. He expected a rigorous result to be hard. Proved only the
  trivial liminf f(N)/N = 0 (from limsup σ(n)/n = ∞).
- **formal-conjectures:** open PR #4076 (May 2026) adds the Lean statement. Our definitions
  match it (`divisorPrefixSum`, `D`, `IsMinimalDPreimage`, the almost-all variant).
- Not on Tao's AI-contributions wiki. No arXiv papers found.

## Our result
For all K ≥ 1 and X: #{N < X : ∃ n, Kn ≤ N, N ∈ D_n} ≤ S·X/K², S = 2ζ(2)ζ(3) ≈ 3.955.
The proof is a first-moment argument; see `WRITEUP.md`. Numerics agree (`scripts/check.py`):
covered fraction at X = 2·10⁵ is 0.319 (K=1), 0.046 (K=2), 0.004 (K=3).
Representable N: 99.985% of N < 20000 (`scripts/rep.py`).

## Files
- `lean/E468.lean`: full Lean proof. Compile with
  `cd Erdos && lake env lean ../problems/468/lean/E468.lean`.
  Key theorems: `card_covered_le`, `not_erdos468AlmostAll`, `mem_D_two_pow_mul_prime`,
  `not_erdos468MinimalPreimageLittleO_of_romanov`, `not_erdos468AlmostAll_upstream` (stated with formal-conjectures' own `Set.HasDensity`, verbatim copy; bridge Lean-checked).
  Axioms: propext, Classical.choice, Quot.sound.
- `WRITEUP.md`: human-readable proof.
- `FORUM_POST.md`: draft proof-claim post (only the [LINK] placeholders left to fill).
- `scripts/check.py`, `scripts/rep.py`, `scripts/romanov.py`: numerics (density of
  {p+2^{k+1}−2 : p>2^k} ≈ 0.455 at 10^7).

## Unconditional Lean for the literal version (not done)
Needs Romanov in Lean: Selberg upper bound for prime pairs + Romanov's lemma + Cauchy–Schwarz.
Mathlib has Chebyshev bounds (`Chebyshev.pi_ge`) and an abstract Selberg-sieve framework
(`NumberTheory/SelbergSieve.lean`) but no prime-pair application. Estimated 3–6k lines.

## Next steps
1. (Optional, big) unconditional Lean Romanov.
2. Publish the Lean file publicly (GitHub); fill in the links in FORUM_POST.md.
3. User posts to https://www.erdosproblems.com/forum/thread/468 with AI disclosure.
4. Optionally comment on formal-conjectures PR #4076.

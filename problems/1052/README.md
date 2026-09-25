# Erdős Problem #1052: unitary perfect numbers ($10)

**Statement (erdosproblems.com/1052, verbatim content, checked 2026-09-25).** A unitary divisor of n is d | n with
(d, n/d) = 1. A number n ≥ 1 is *unitary perfect* if it is the sum of its unitary divisors other than n itself
(equivalently σ*(n) = 2n). Are there only finitely many unitary perfect numbers?
Source: Guy, *Unsolved Problems in Number Theory* [Gu04], problem B3. Carlitz, Erdős and Subbarao offer $10;
Subbarao offers 10 cents per new example. Known: 6, 60, 90, 87360, 146361946186458562560000 (OEIS A002827).
Site tag: "open, and cannot be resolved with a finite computation".

Unitary-component form: if n = ∏ q (q = the prime-power components p^a ∥ n), then σ*(n) = ∏(q + 1), so n is unitary
perfect iff ∏_{q ∥ n} (1 + 1/q) = 2.

| n | components | ω(n) | odd components k |
|---|---|---|---|
| 6 | 2 · 3 | 2 | 1 |
| 60 | 2² · 3 · 5 | 3 | 2 |
| 90 | 2 · 3² · 5 | 3 | 2 |
| 87360 | 2⁶ · 3 · 5 · 7 · 13 | 5 | 4 |
| 146361946186458562560000 | 2¹⁸ · 3 · 5⁴ · 7 · 11 · 13 · 19 · 37 · 79 · 109 · 157 · 313 | 12 | 11 |

## Open-status evidence (rule 1 checklist)

| Source | Checked | Finding |
|---|---|---|
| https://www.erdosproblems.com/1052 | 2026-09-25 | OPEN; 0 comments, 0 proof claims, 0 expositions; last edited 2026-09-02; one "looks difficult" vote, no "working on" |
| https://www.erdosproblems.com/forum/thread/1052 | 2026-09-25 | empty thread |
| formal-conjectures `FormalConjectures/ErdosProblems/1052.lean` (main) | 2026-09-25 | `erdos_1052` tagged `research open`; `even_of_isUnitaryPerfect` tagged solved (AlphaProof proof in mzhorvath1 fork); test lemmas for 6, 60, 90 (87360 `stop`ped as too slow; the 24-digit one via a Sanexxxx777 fork) |
| Literature, OEIS, Tao wiki, arXiv 2024–26, sibling problems | pending | see LITERATURE.md (agent) |

## Prior work

(pending: filled from LITERATURE.md once verified)

## Angles

1. **Classify all unitary perfect numbers with ω(n) = K** for K beyond the published bound: a ratio search
   (components sorted by size; the last two solved from ((a−b)x − b)((a−b)y − b) = ab) combined with factor chasing
   (every odd prime of q + 1 and the prime 2 must divide n; the 2-adic budget Σ_{odd q} v₂(q + 1) = m + 1).
2. A Lean certificate for a small case (e.g. all unitary perfect n with ω(n) ≤ 5, or with 2 ∥ n).

## Results so far

- `scratchpad` prototype (to be moved to `scripts/`): K ≤ 8 gives exactly {6, 60, 90, 87360} (K = 8 in 2.5 s, 46k nodes);
  this is far below the published frontier, so it is only a validation.

# Erdős #470 — odd weird numbers ($10)

A number n is *weird* if σ(n) > 2n (abundant) but n is not *pseudoperfect* (not a sum of
distinct proper divisors). #470 asks: (i) is there an odd weird number? (ii) are there
infinitely many primitive weird numbers? This folder works on (i) only.

Realistic goal: a new, checkable partial result, not the prize.

## Open-status evidence (checked 2026-09-25)

| Source | Finding |
|---|---|
| https://www.erdosproblems.com/470 | **OPEN**, $10. Last edited 18 Jan 2026. 2 forum comments, 0 proof claims. Notes cite Fang 2022 (none < 10^21) and Liddy–Riedl 2018 (odd weird ⇒ ≥ 6 distinct primes). |
| https://www.erdosproblems.com/forum/thread/470 | Dogmachine (22 Sep 2025): the $10 is for part (i). Woett (18 Jan 2026): the $10 and the #825 $25 could be combined; obsolete once Larsen solved #825. No resolution claimed. |
| formal-conjectures `ErdosProblems/470.lean` (main, fetched 2026-09-25) | `erdos_470.parts.i` and `.parts.ii` are `research open`. Solved variants: positive density, 70 is the smallest weird number, Melfi's conditional result, Fang's 10^21, Liddy–Riedl ≥ 6 prime divisors, and abundancy < 4 if no odd weird exists. |
| teorth/erdosproblems `data/problems.yaml` (commit of 2026-09-22) | 470: status `open`, last_update 2025-08-31. |
| Tao's wiki "AI contributions to Erdős problems" (wiki clone, last commit 2026-06-30) | #470 and #825 are not mentioned. |
| OEIS A006037 / A002975 (fetched 2026-09-25) | Search history: Hearn < 10^17 (2005), Fang < 1.8·10^19 (2013), < 10^21 (2014), and < 10^28 when the abundance is < 10^14 (2015). No odd weird number known. |
| arXiv/web search, 2024–2026 | Only Hisamoto, arXiv:2607.25278 (28 Jul 2026): σ(n)/n > 633 ⇒ semiperfect. This is #825-type and says nothing about odd weird numbers. |

Sibling **#825** (is σ(n) > Cn ⇒ pseudoperfect for some absolute C?) is **proved (Lean)**. Larsen
posted the proof on the forum on 31 Jan 2026 (github.com/Larsen-Daniel/Erdos-825). His theorem: for all
ε > 0 there is an L such that every n with all prime factors > L and σ(n) > (2+ε)n is pseudoperfect.
It does not settle #470. Weisenberg's remark connects the two problems: a weird number with
σ(n)/n ≥ 4 has an odd weird divisor.

**Conclusion: #470(i) is open.**

## Prior work (the frontier)

- **Benkoski–Erdős 1974**: weird numbers have positive density. They posed the odd case.
- **Search bounds**: Fang (with Beckert, yoyo@home volunteer computing, about 80 + 150 core-years,
  2013–2015; arXiv:2207.12906; J. Grid Comput. 2018) found no odd weird number < 10^21, and none
  < 10^28 with abundance A(n) = σ(n) − 2n < 10^14. The method is a DFS over the tree
  "n → n·p (p ≥ gpf n)" with a size bound and the barrier σ(N)/N·(p/(p−1))^k < 2. Each abundant
  leaf gets an individual subset-sum check.
- **Amato–Hasler–Melfi–Parton** (JNT 201 (2019); arXiv:1802.07178): enumerate primitive abundant
  numbers (PANs) by Ω. They **count** odd PANs: Ω = 5: 121, Ω = 6: 15 772,
  Ω = 7: 102 896 101, Ω = 8: 3 475 842 606 319 962 (OEIS A287728). Their weirdness checks
  cover all PANs only up to Ω = 5, plus PANs with a non-squarefree odd part up to Ω = 7
  (repo amato-gianluca/weirds). No odd weird number was found.
- **Liddy–Riedl 2018** (Univ. Akron honours thesis; the PDF is behind a Cloudflare wall, so I
  have not read it): odd weird ⇒ ω(n) ≥ 6. OEIS A188439 and A287728 say the number of odd PANs
  with ω = 5 is not settled in the literature. This result is not peer-reviewed.
- **Melfi 2015**: a prime-gap conjecture implies infinitely many primitive weird numbers, and a
  variant gives odd weird numbers conditional on the existence of odd *almost perfect* numbers
  (σ = 2n − 1).
- **#825** (Larsen 2026; explicit constant C = 633 by Hisamoto 2026): a large abundancy index
  forces pseudoperfectness.

## Reduction used here

If d | n and d is pseudoperfect, then n is pseudoperfect (scale the representation by n/d).
Every abundant n has a primitive non-deficient divisor m with Ω(m) ≤ Ω(n), and a perfect m
is pseudoperfect. Hence:

> **No odd weird n with Ω(n) ≤ k ⇔ every odd abundant n with Ω(n) ≤ k whose n / gpf(n) is
> deficient is pseudoperfect.**

Also, n is pseudoperfect ⇔ A(n) = σ(n) − 2n is a sum of distinct proper divisors of n
(take complements).

## Angle pursued: odd weird ⇒ Ω(n) ≥ 8

See the "Status" section below.

## Status

(updated as work proceeds)

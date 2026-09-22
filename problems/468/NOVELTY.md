# Erdős #468: novelty review

Checked 2026-09-22 by three independent research agents (OEIS/recent activity, databases/preprints,
Guy/ErGr80 wording). The headline was verified by hand against the saved erdosproblems.com/1054 page.
Raw sources (A*.txt, 1054.html, forum1054.txt, forum468.html, problems.yaml) were saved alongside the
agent reports.

## Verdict: NOT NEW

Our theorem `card_covered_le`, #{N < X : ∃ n, K·n ≤ N, N ∈ D_n} ≤ S·X/K² with S ≈ 3.96, is
**Terence Tao's theorem of 2025-11-01**, with δ = 1/K. The architecture of the proof is also the same.

- erdosproblems.com/1054, the problem text:
  > "The strong claim that f(n)=o(n) was disproved by Tao in the comments to [468], in which he proves
  > that the upper density of {n : f(n) ≤ δn} is ≪ δ²."
- Tao posted it in the **#468** thread. Bloom **moved** it to the #1054 thread (#1054 is the Guy B2
  version, which counts divisor 1, so f_1054(N) = f_468(N−1)). The #468 page itself still says OPEN
  and mentions neither Tao nor #1054, which is why the first check missed it. Kovač's 2025-09-14
  comment on #468 now has the edit: "Terry Tao solved the second part under [1054]".
- The ingredients match one to one:
  - our T_e(n) ↔ Tao's σ_k(n)/n (the divisor sum without the top k divisors);
  - Markov plus a union bound over k;
  - a first moment Σ_k Σ_{n≤x} σ_k(n) ≪ x² via lcm sums.
- Kovač (2025-11-18) wrote it out as #{N ≤ X : f(N) ≤ δN} ≪ δ²X, uniformly in X.

## Later work (all in https://www.erdosproblems.com/forum/thread/1054)

| Date | Who | Result |
|---|---|---|
| 2026-04-16 | jif (github.com/jif-perso/erdos_1054) | f defined for all n ≠ 2, 5 (1054 indexing), using explicit ternary Goldbach and computation |
| 2026-05-10 | Liam Price (GPT-5.5 Pro) | O(δ³), then O_k(δ^k) |
| 2026-05-10/11 | Kovač (with Bloom) | q-th moments ⇒ δ^{q+1}; then sup_x density ≪ exp(−e^{(1/δ)^c}) |
| 2026-06-22 – 07-21 | principia_math (github.com/antoshashakov/Principia-Math-Solutions, erdos1054) | Lean-verified: {N : f(N) > AN} has positive lower density for every A, so limsup f(N)/N = ∞. Kovač says it also formalises an O(δ³) density bound (not independently confirmed). |

Consequences for our file:
- **Literal "all N" version.** Our `not_erdos468MinimalPreimageLittleO_of_romanov` assumes Romanov-type
  density. That is unnecessary: jif's result shows almost every N is reachable, and combined with
  Tao's bound this disproves the literal version outright.
- Our bound is asymptotically much weaker than the current state of the art.

## What might still be ours (modest)

1. The explicit constant S = ζ(2)·Σ H_b/b² ≈ 3.96.
2. A sorry-free Lean proof in formal-conjectures' form: `Set.HasDensity` via the verbatim `Upstream`
   copy. Upstream status:
   - `FormalConjectures/ErdosProblems/1054.lean` parts i/ii/iii are still `answer(sorry)`;
     only f 2 = 0 and f 5 = 0 are proved (PRs #4137, #4333);
   - there is no `468.lean` on main (issue #745 is open, PR #4076 is open).

   **Caveat:** Principia's Lean may already contain an equivalent standalone density statement.
   Check that before claiming even this.

Any public mention must credit Tao (2025-11-01), Kovač, jif and Principia Math.

## Source wording

- **ErGr80 p. 93** (reconstructed from Google Books snippets): "For a given n, let 1 < d_1 < d_2 < ... be
  the divisors of n and consider the sums d_1, d_1 + d_2, d_1 + d_2 + d_3, .... How many new sums do we
  get from n, i.e., sums not occurring for m < n? When does N first occur as a sum? In particular, if
  f(N) denotes the least value of n for which N occurs, is it true that f(N) = o(N)? (or for almost all
  N?)". It gives no reference or partial result.
- **Guy, UPINT 3rd ed. (2004), §B2 p. 80**, a side remark at the end of the section: "Erdős lets f(n) be
  the smallest integer for which n = Σ_{i=1}^k d_i for some k, where 1 = d_1 < d_2 < ⋯ < d_l = f(n) is
  the increasing sequence of divisors of f(n). Is f(n) = o(n)? Or is this true only for almost all n,
  with lim sup f(n)/n = ∞?"
  - The 1st ed. (1981, p. 29) has the same text without the "lim sup" clause.
  - The 2nd ed. was not seen.
  - Guy counts divisor 1.

## OEIS facts

- A167485 (Adams-Watters 2009) **includes divisor 1**: f_468(N) = A167485(N+1). Checked for
  N = 2..2999 against Israel's b-file, with 0 mismatches.
- Its comments: Wesolowski 2013 ("Is a(n) = o(n)?"), Spezia 2024 (attributes it to Erdős/Guy),
  Israel 2024 (liminf = 0).
- It has no density result and no link to Tao.
- A387502/A387503 (Kovač 2025) contain numerics only.

## Search coverage and gaps

- **Searched:**
  - zbMATH (via API) and arXiv: no paper on this f. The nearest items are tangential (Balog–Erdős–Tenenbaum
    1990, Zbl 0718.11041; Weingartner/Saias on practical numbers).
  - OEIS and related sequences.
  - formal-conjectures and GitHub code search.
  - The erdosproblems pages and threads for 468 and 1054.
- **Not searched:** MathSciNet (no access), a full Scholar "cited by" crawl, Zulip/Mathstodon/X, and
  Tenenbaum's 2013 survey and Erdős's 1978/79 papers (scans not machine-readable). The forum evidence
  already settles the question.

## Process lesson

A problem's own page can omit a resolution that was **moved** to a sibling or duplicate problem.
Always check the "See also" links, duplicates (for example the Guy-numbered twin), and the forum
threads of cross-referenced problems.

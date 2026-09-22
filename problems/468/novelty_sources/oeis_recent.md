# Erdős #468 — OEIS and recent-activity literature check

Accessed: 2026-09-22 (all URLs below, unless noted). Raw fetches are saved beside this file (A*.txt, ep468.html, forum468.html, forum1054.txt, 1054.html, history_468.html, problems.yaml, p3.lean).

## TL;DR (read this first)

**We have a prior result, and it is decisive.** Erdős #1054 (erdosproblems.com/1054) is the same f as #468 with divisor 1 included, so f_1054(N) = f_468(N-1). On **2025-11-01** Terence Tao posted a proof in the #468 forum (later moved to the #1054 thread) that
  #{N ≤ X : f(N) ≤ δN} ≪ δ² X,
i.e. f(N)=o(N) fails, even for almost all N. This is the same statement as our result, with δ = 1/K and an unspecified constant where we have 3.96. The site text of #1054 says: "The strong claim that f(n)=o(n) was disproved by Tao in the comments to [468], in which he proves that the upper density of {n : f(n) ≤ δn} is ≪ δ²."
Later work:
- Kovač (2026-05-11): improved the bound to ≪ exp(-e^{(1/δ)^c}), uniformly in x.
- GPT-5.5 Pro via Liam Price (2026-05-10): O(δ³), then O_k(δ^k).
- jif (2026-04-16): showed f is defined for every n ≠ 2, 5.
- Principia Math (2026-06/07): Lean-verified proof that limsup f(N)/N = ∞, with positive lower density of {f > AN}.

---

## 1. OEIS

### A167485 — https://oeis.org/A167485 (text: `search?q=id:A167485&fmt=text`; internal: /A167485/internal)
- %I #24, last edited Sep 27 2024. Author: **Franklin T. Adams-Watters, Nov 04 2009**. Offset 0,4. Keywords nonn,look.
- %N: "Smallest positive integer m such that n can be expressed as the sum of an initial subsequence of the divisors of m, or 0 if no such m exists."
- %S: 1,1,0,2,3,0,5,4,7,15,12,21,6,9,13,8,12,30,10,42,19,18,20,57,14,36,46,30,12,102,…
- Comments:
  - (no author, presumably Adams-Watters 2009) It looks like 2 and 5 are the only zeros. This would follow from a strong Goldbach variant: every even integer > 22 is p+q with 5<p<q<5p; then take pq or 5pq.
  - **Arkadiusz Wesolowski, Nov 09 2013:** "Is a(n) = o(n)?"
  - **Stefano Spezia, Sep 25 2024:** "The above question has been posed by Erdős. See Guy."
  - **Robert Israel, Sep 26 2024:** a(A000203(n)) ≤ n, so liminf a(n)/n = 0.
- %D: R. K. Guy, *Unsolved Problems in Number Theory*, 1st ed. 1981, §B2.
- %H: Robert Israel, b-file n=0..20000 (n=0..1000 from Michel Marcus). b-file header: "# Computed by Robert Israel using Maple, September 26 2024". It has 20002 lines. The other link is Robert Israel's "Plot of a(n)/n for n=1..10^6" (a167485.png).
- %e: divisors of 15 are 1,3,5,15, with prefix sums 1,4,9,24, so a(9)=15.
- Programs: Maple (Israel 2024), PARI (unsigned).
- %Y Cf.: A000203 (sigma), A001065 (aliquot sum), A078587 (largest prime p<n with 2n-p prime; Goldbach-related, T. D. Noe 2002, no o(n) content), A051444 (least k with sigma(k)=n; Jud McCranie, no o(n) content). None of these cross-references mention o(n), density, or a(n)/n.
- Not updated since 2024: no link to erdosproblems 468/1054 and no mention of Tao's disproof.

### A387502 — https://oeis.org/A387502
- %I #29, Sep 11 2025. Author **Vjekoslav Kovac, Aug 31 2025**. %N: "Number of debut sums of initial subsequences of the divisors > 1 of n." (= |D_n \ ∪_{m<n} D_m|).
- Comments by Kovač: cites Erdős–Graham 1980 p.93 and Guy B2 (the divisor-1 variant). Record indices are 2, 12, 36, 144, 336, 1320, 1980, 5040, 8400, 25200, 75600. The mean of the first 100000 terms is 0.8349. "The smallest m such that D(m) contains a given positive integer n is sequence A167485 with indices shifted by 1."
- %D: Erdős & Graham, *Old and new problems…*, Monogr. Enseign. Math. 28 (1980) p.93, and Guy 1981 B2. %H: Kovač b-file 1..10000 (no header comment), and Bloom, erdosproblems.com/468.
- Programs: Mathematica (Kovač), PARI (**Andrew Howroyd, Sep 01 2025**), Python (**Michael S. Branicky, Sep 06 2025**). %Y: A167485, A387503.

### A387503 — https://oeis.org/A387503
- %I #26, Sep 11 2025. Author **Vjekoslav Kovac, Aug 31 2025**. %N: "Total number of distinct sums of initial subsequences of the divisors > 1 of positive integers up to n." (partial sums of A387502).
- It has the same references, links, and shift remark as A387502, with PARI by Howroyd (Sep 01 2025) and Python by Branicky (Sep 06 2025). b-file 1..10000, no header. %Y: A167485, A387502.
- Neither Kovač sequence says anything about o(n) or density beyond the average values above.

### Other OEIS sequences found (searches: "partial sums of divisors", "partial sums of the divisors", "initial subsequence" divisors, "first k divisors", "cumulative sums" divisors, "sum of the smallest" divisors, erdos graham divisors "initial", and a reverse search for A167485)
- A search for "A167485" returns only A167485, A243970, A387502, A387503.
- **A243970** (Michel Marcus, Jun 16 2014): the analogue of A167485 with divisors taken in *decreasing* order. Its comment says "similar to A167485". Trivially a(n) ≤ n. Cf. A167485.
- **A243971** (Marcus, Jun 16 2014): numbers n with A243970(n)=n. Adams-Watters (Jul 20 2017) asks: "Is this sequence infinite?"
- **A240698** (Zumkeller, Apr 10 2014): a table of the partial sums of the divisors of n.
- A064510, A377247 (Corneth 2024), A378314 (Alekseyev 2024), A187822/A187825, A289872, A093891 and A197410 are all prefix-sum-of-divisor variants. None mentions f, o(n), or density of small a(n)/n.
- **Conclusion:** OEIS holds no density result. Its only related content is Wesolowski's question and Israel's liminf=0 remark.

## 2. A167485 includes divisor 1: confirmed
- The definition says "divisors of m" with no exclusion. The example uses divisors 1,3,5,15 (prefix sums 1,4,9,24), and a(1)=1 (m=1).
- Our f uses divisors >1, so D'_m (with 1) = {1} ∪ {1+s : s ∈ D_m}. Hence f(N) = A167485(N+1) for N ≥ 2. Checks: f(2)=A(3)=2, f(3)=A(4)=3, f(4)=A(5)=0 (unreachable), f(5)=A(6)=5, f(6)=A(7)=4, f(8)=A(9)=15, f(11)=A(12)=6. All match.
- I verified this by computer for every N in 2..2999 against Israel's b-file, with 0 mismatches.
- Kovač's remark "A167485 with indices shifted by 1" is consistent with this.

## 3. erdosproblems.com

- **https://www.erdosproblems.com/468**: still **OPEN**. It shows "Formalised statement? No", OEIS A167485/A387502/A387503, and Comments (1). Likes: antonshakov, Vjeko_Kovac. The statement is unchanged; the history page has one prior revision dated 2025-10-20 (formatting only). **The page does not mention Tao or #1054.** This is probably why the 2026-09-22 teammate check missed the result.
- **https://www.erdosproblems.com/forum/thread/468**: only Kovač's 2025-09-14 comment is still shown there, but it now carries an EDIT: "[EDIT: I was unnecessarily pessimistic. Terry Tao solved the second part under [1054] and there were further upgrades.]" Tao's comment was moved from #468 to #1054 by Bloom in May 2026.
- **https://www.erdosproblems.com/1054** ([Gu04], Guy B2 version with divisor 1 included; still marked OPEN, last edited 06 Dec 2025, Formalised: Yes):
  "The strong claim that f(n)=o(n) was disproved by Tao in the comments to [468], in which he proves that the upper density of {n : f(n) ≤ δn} is ≪ δ²." Additional thanks: Vjekoslav Kovac. Open parts: well-definedness, and "limsup f(n)/n = ∞?".
- **https://www.erdosproblems.com/forum/thread/1054** (36 comments). Key items in date order:
  - StijnC, 2025-11-01: based on the OEIS plot, o(n) looks false.
  - Kovač, 2025-11-01: #1054 duplicates the last question of #468, shifted by 1. Bloom, 2025-11-01: "I'll move the second question over here."
  - **TerenceTao, 2025-11-01 22:50 (moved from 468):** let σ_k(n) be the sum of the divisors of n excluding the top k. Tao proves Σ_{n≤x} σ_k(n) ≪ x²/k^{1.1} (a divisor-anatomy moment argument), hence Σ_k Σ_{n≤x} σ_k(n) ≪ x². By Markov and a union bound over k, #{N ∈ [C₀x, 2C₀x] : f(N) ≤ x} ≪ x/C₀.
  - Kovač, 2025-11-02: states the consequence #{N≤X : f(N) ≤ δN} ≪ δ²X and notes it also rules out "almost all". Tao, 2025-11-02: suggests second moments for o(δ²) and explains why the sum over k is needed.
  - Kovač, 2025-11-18: gives the full dyadic write-up of the δ² bound; the site was updated after this comment. Dogmachine, 2025-11-18: notes f is not yet known to be well-defined.
  - jif, 2026-04-16 (repo github.com/jif-perso/erdos_1054): **every n ≠ 2,5 is represented**. The proof combines a computer check, prime-window interval extension, and explicit Helfgott ternary Goldbach bounds.
  - Liam Price, 2026-05-10: GPT-5.5 Pro gives O(δ³), then O_k(δ^k) (ChatGPT share links). Kovač, 2026-05-10: already had the q-th moment Σ_n Σ_j (σ_j(n)/n)^q ≪_q x, giving O(δ^{q+1}).
  - Kovač, 2026-05-11 (with Bloom): the note improves the bound to sup_x #{n≤x : f(n) ≤ δn}/x ≪ exp(-e^{(1/δ)^c}). Kovač, 2026-05-17: open whether the density is actually 0 for fixed small δ; conjectures a limit distribution of f(n)/n.
  - principia_math, 2026-06-22 through 2026-07-21 (GPT-5.5 Pro plus Claude Opus 4.8; repo github.com/antoshashakov/Principia-Math-Solutions/erdos1054, paper draft "Unbounded ratios in Erdős Problem 1054"): for each A ≥ 1, {N : f(N) > AN} has positive lower density, so limsup = ∞. This is **fully Lean-verified**, including a from-scratch almost-all binary Goldbach proof (≈36.7k-line master files).
  - Kovač, 2026-06-26: says the Principia Lean formalizes #{N≤X : f(N) ≤ δN} = O(δ³X), which is a Lean-checked small-f density bound. (I did not confirm the standalone statement: the headline theorem is the limsup one.) Nat Sothanaphan screened it and found no issue. old-bielefelder posted a ChatGPT compilation (althofer.de/erdos1054_compilation.pdf). Kovač, 2026-06-24: proposes one joint paper starting from Tao's disproof.
- **teorth/erdosproblems data** (raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml): #468 is open (last_update 2025-08-31) and unformalized. #1054 is open (2025-09-28) with formalized: yes (2025-11-25). The data files are stale relative to the forum.

## 4. Formal-conjectures, GitHub, web
- formal-conjectures: issue #745 "Erdős Problem 468" is still open. There is **no FormalConjectures/ErdosProblems/468.lean** on main (404).
- **1054.lean exists** (PR #1190, merged 2025-11-11): parts i/ii/iii are `answer(sorry)` and tagged research open. PR #1338 fixed the limsup brackets (2025-12). PR #4137 proved f 2 = 0 (merged 2026-05-30) and PR #4333 proved f 5 = 0 (merged 2026-06-26). PRs #2789 and #3305 (closed, 2026-03) targeted a "variants.known_result". Part ii (the "almost all" question) is still `sorry` upstream, so a Lean disproof of 1054.parts.i/ii would still be an upstream contribution.
- GitHub code search for "erdos_468" / "Erdos468" found only stubs or reviews: ryantuck/erdos-ai (an AI review of a draft 468.lean), daedalus/alphaproof-nexus (an empty EVOLVE stub), and rjwalters/lean-genius (a "wip" meta entry marked open). None claims a disproof. TheJustinSunPrize/awards has no 468 or 1054 entries.
- Web searches ("Erdős problem 468", "Erdős problem 1054 Tao …", "Unbounded ratios in Erdős Problem 1054") found only the erdosproblems pages above and the unrelated arXiv 2605.00695. There is no arXiv paper yet for Tao/Kovač/Principia.
- I did not search Zulip or Mathstodon/X individually, because the forum already settles the question.

## Implications for our claim
- Our bound #{N<X : ∃n, Kn ≤ N, N ∈ D_n} ≤ 3.96·X/K² is Tao's 2025-11-01 δ² theorem (δ = 1/K), transferred to the #468 indexing, with an explicit constant.
- Asymptotically it is weaker than Kovač's exp(-e^{(1/δ)^c}) (2026-05) and than the O(δ^k) bounds.
- What may still be new: (a) the explicit constant 3.96; (b) a Lean proof stated in the #468 indexing, or in the formal-conjectures `Set.HasDensity` form of 1054.parts.i/ii, which is still sorry upstream (unless Principia's Lean already contains an equivalent standalone statement); (c) the uniform-in-X form, although Kovač's note is uniform too.
- We must cite Tao (erdosproblems forum #1054, 2025-11-01), Kovač, jif, and Principia.

PRIOR RESULT FOUND: yes. Tao proved #{N≤X : f(N) ≤ δN} ≪ δ²X on the erdosproblems forum on 2025-11-01, which disproves f(N)=o(N) even for almost all N. It is recorded on erdosproblems.com/1054, the divisor-1 duplicate of the #468 question. Kovač later strengthened it to ≪ exp(-e^{(1/δ)^c}) (2026-05-11), and Principia Math has a Lean-verified O(δ³) density bound plus limsup = ∞ (2026-06/07). Our 3.96·X/K² result is an explicit-constant, Lean-verified version of Tao's theorem, not a new answer.

A167485 INCLUDES DIVISOR 1: yes. Its definition says "divisors of m" with no exclusion, and the worked example uses 1,3,5,15 → 1,4,9,24. So f_468(N) = A167485(N+1): I checked this for all N = 2..2999 against Israel's b-file with 0 mismatches, including f(2)=2, f(3)=3, f(4)=0, f(5)=5, f(6)=4, f(8)=15, f(11)=6.

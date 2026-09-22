# Erdős #468 literature and novelty check: databases and preprints

Date checked: 2026-09-22. About 25 searches and fetches.

## HEADLINE: the result is already known (Tao, Nov 2025, on the erdosproblems.com forum)

The f(N)=o(N) question was **moved from #468 to Erdős Problem #1054** (Bloom, 1 Nov 2025). #1054 is the same f with the indices shifted by 1, because there the divisor 1 is counted. #1054 now says:
"The strong claim that f(n)=o(n) was disproved by Tao in the comments to [468], in which he proves that the upper density of {n : f(n) ≤ δn} is ≪ δ²."

### Direct hits (erdosproblems.com forum, thread 1054; comments were moved there from 468)
URL: https://www.erdosproblems.com/forum/thread/1054 (problem page https://www.erdosproblems.com/1054, last edited 06 Dec 2025)

1. **Terence Tao, 01 Nov 2025**. RATING: DIRECT, same result and essentially the same technique.
   - σ_k(n) is the sum of the divisors of n excluding the top k divisors. This is exactly our prefix sum ending at d=n/e, with k ↔ e.
   - Goal: Σ_{n≤x} σ_k(n) ≪ x²/k^{1.1}. He sums over k and applies Markov/union bound: #{n≤x : ∃k, σ_k(n) ≥ C₀x} = O(x/C₀). So f(N) ≤ x for only O(x/C₀) of the N in [C₀x, 2C₀x].
   - His proof of (1) splits into two cases (τ(m) large, or d has many small factors) and uses lcm sums Σ 1/[r₁,r₂]. It is cruder than ours (it bounds each k separately), but the architecture is the same: Markov plus a first moment over all "k" plus lcm counting.
2. **Vjeko Kovač, 02 Nov 2025 and 18 Nov 2025**. RATING: DIRECT.
   - Notes that this also disproves f(N)=o(N) for almost all N.
   - Restates the proof as Σ_k Σ_{n≤x} σ_k(n) ≪ x². Then by Markov and a dyadic split: **#{N ≤ X : f(N) ≤ δN} ≪ δ² X**.
   - With δ=1/K this is our theorem, #{N<X : ∃n, Kn ≤ N, N∈D_n} ≤ S·X/K², except for our explicit constant S ≈ 3.96.
   - Our Σ_{e|n} T_e(n) = Σ_k σ_k(n)/n. So our (iii) is exactly the Tao/Kovač first-moment bound, with an explicit constant.
3. **Kovač, 10–17 May 2026**. RATING: DIRECT, and stronger than ours.
   - Higher moments: Σ_{n≤x} Σ_j (σ_j(n)/n)^q ≪_q x. He describes the proof as "expand, flip the divisors, organize by the LCM", which is our lcm-counting trick in its q-th moment form. That gives density ≪ δ^{q+1}.
   - After a remark by T. Bloom (11 May 2026) he improved it to sup_x (1/x)#{n≤x : f(n) ≤ δn} ≪ exp(−e^{(1/δ)^c}), uniformly in x. He posted a short self-contained note (a link in the thread).
4. **Liam Price, 10 May 2026 (GPT-5.5 Pro)**. Claimed bounds O(δ³) and then O_k(δ^k). RATING: DIRECT, stronger.
5. **principia_math, 22 Jun and 21 Jul 2026**. Proposed full resolution of the limsup part: for every A ≥ 1, {N : f(N) > AN} has positive lower density, so limsup f(N)/N = ∞. It has a Lean formalization, and the first message credits Claude Opus 4.8 and GPT-5.5 Pro among the models used. The formalized statement includes #{N≤X : f(N) ≤ δN} = O(δ³X).
   - Paper: https://github.com/antoshashakov/Principia-Math-Solutions/blob/main/erdos1054/paper/erdos1054.pdf (I could not read the PDF through the fetch tool).
   - RATING: DIRECT for the #1054 question; covers more than our result.
6. **jif, 16 Apr 2026**. f is well-defined for all n ∉ {2,5}, using explicit Helfgott ternary Goldbach plus computation. Repo: https://github.com/jif-perso/erdos_1054. RATING: tangential, but it settles the well-definedness caveat.
7. Also in the thread: a ChatGPT compilation by old-bielefelder (https://althofer.de/erdos1054_compilation.pdf), and a comment (Kovač, 24 Jun 2026) that nobody plans a separate publication and a joint write-up was suggested.

Also:
- https://www.erdosproblems.com/forum/thread/468: one visible comment (Kovač, 14 Sep 2025). Numerical data: 31.3% of N ≤ 1e5 have f(N) > 1e5. It gives liminf f(N)/N = 0 via N = σ(n)−1. RATING: tangential.
- OEIS A167485 (https://oeis.org/A167485) is f; A387502/A387503 are by Kovač, Aug 2025. Neither states a density bound. RATING: tangential.
- google-deepmind/formal-conjectures issue #745 (https://github.com/google-deepmind/formal-conjectures/issues/745, 5 Oct 2025) formalizes the #468 statement. There is also https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1054.lean. RATING: tangential.

## zbMATH Open (via the api.zbmath.org JSON API; the web UI returned 403)
Queries run: "consecutive divisors"; partial sums divisors; sum of divisors initial; divisors up to sum practical; Erdős Graham divisors sums; sums of consecutive divisors; sigma(n,x) divisors; divisors d_1+d_2; sum of smallest divisors; sum of the small divisors; "truncated divisor sum"; the Erdős–Graham 1980 problem book.

No hit concerns prefix sums of the ordered divisors or f(N). Closest (all tangential):
- Zbl 0434.10001: Erdős–Graham 1980, *Old and new problems and results in combinatorial number theory*. This is the source of the problem.
- Zbl 0718.11041: Balog, Erdős, Tenenbaum 1990, *On arithmetic functions involving consecutive divisors*. Tangential.
- Zbl 0526.10036 and Zbl 0676.10030: Erdős–Tenenbaum, on consecutive divisors. Tangential.
- Zbl 0437.10020: Erdős–Tenenbaum 1981, *Sur la structure de la suite des diviseurs d'un entier*. Tangential.
- Zbl 1338.11087 (Weingartner 2015, *Practical numbers and the distribution of divisors*), Zbl 1536.11143 (Weingartner 2023, mean number of divisors for dense and practical numbers), Zbl 1505.11121 (Pomerance–Weingartner 2022), Zbl 0822.11064 (Saias 1994). Practical and dense-divisor literature. They concern the condition d_{i+1} ≤ σ(d_1..d_i)+1 and densities, not the size of prefix sums relative to n. Tangential.
- Zbl 1015.11047: de la Bretèche–Tenenbaum 2002, *Local distribution laws of the k-th divisor of an integer*. Tangential.
- Zbl 0478.10027 (Bateman–Erdős–Pomerance–Straus 1981) and Zbl 0291.10040 (Erdős 1974, σ(n)/n distribution). Tangential.
- "truncated divisor sum" returned only unrelated sieve-weight papers (Goldston–Yıldız type).

## MathSciNet
Not accessible (subscription; not attempted beyond noting this).

## arXiv (export.arxiv.org API plus web search)
Queries run: "prefix sums" and divisors; "consecutive divisors"; "problem 468" Erdos; "partial sums" "divisors of n"; "divisors up to" sum; "truncated divisor sum"; A167485; "initial segment" divisors; "smallest divisors" sum; "Erdős problem 1054".

- No arXiv paper on #468 or #1054 f(N) was found.
- Nothing relevant beyond the Weingartner dense/practical papers (arXiv 1405.2585, 2101.11585, 2104.07137, 2211.05819) and Cambie–van Doorn 2510.19727 (separable numbers / interlocking divisors, Erdős–Hall). All tangential.
- arXiv 2311.10087 (consecutive sums in increasing sequences, Erdős–Graham) is a different problem.
- arXiv 2605.00695 (Campbell, Σ 1/d(d(n))) is unrelated.

## Semantic Scholar / Google Scholar
Not queried directly (bounded effort). General web search turned up nothing beyond the erdosproblems.com, OEIS and GitHub sources above.

## Assessment
Our theorem is #{N<X : f(N) ≤ N/K} ≤ S·X/K², with S = ζ(2)Σ H_b/b² ≈ 3.96, uniform in X. This is exactly the δ² bound of Tao (1 Nov 2025) as written out by Kovač (18 Nov 2025), with our three ingredients mapping one-to-one:
- (i) T_e(n) ↔ σ_k(n)/n;
- (ii) Markov and union bound over k;
- (iii) first moment Σ_n Σ_k σ_k(n) ≪ x² via lcm counting.

What is new in ours: only the explicit constant S ≈ 3.96, perhaps a cleaner exact lcm evaluation, and uniformity in X (Kovač's dyadic version is already uniform in X). The known results have since gone much further: δ³, δ^M, exp(−e^{(1/δ)^c}), and the limsup = ∞ question has a proposed Lean-verified resolution by Principia Math (Jun–Jul 2026).

PRIOR RESULT FOUND: yes. Tao (erdosproblems.com forum, #468 comments later moved to #1054, 01 Nov 2025) proved the upper density of {N : f(N) ≤ δN} is ≪ δ², by Markov plus the first moment Σ_k Σ_{n≤x} σ_k(n) ≪ x². Kovač (18 Nov 2025) wrote it as #{N≤X : f(N) ≤ δN} ≪ δ²X, uniform in X. Since then there are stronger bounds (Kovač/Bloom, May 2026: exp(−e^{(1/δ)^c})) and a proposed resolution of the limsup part (Principia Math, Jun 2026). erdosproblems.com #1054 records the disproof. Our bound differs only by an explicit constant.

CLOSEST TECHNIQUE OVERLAP: T. Tao's comment of 01 Nov 2025 on Erdős #468/#1054 (https://www.erdosproblems.com/forum/thread/1054), together with V. Kovač's 18 Nov 2025 write-up and his May 2026 moment note ("expand, flip the divisors, organize by the LCM"). In the formal literature (zbMATH/arXiv) there is no overlap closer than Balog–Erdős–Tenenbaum 1990 (Zbl 0718.11041), which is tangential only.

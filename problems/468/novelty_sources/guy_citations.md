# Erdős #468: Guy B2 / ErGr80 wording and citation search

Accessed: 2026-09-22 (all sources). About 30 searches/fetches.

## 1. Guy, *Unsolved Problems in Number Theory*, section B2

B2's title in the 3rd edition (p. 74) is **"Almost perfect, quasi-perfect, pseudoperfect, harmonic, weird,
multiperfect and hyperperfect numbers."** Our question is a **one-paragraph side remark near the end of B2**, and it is
the last problem in the section. B2 is mainly about variants of perfect numbers. It is not about unitary perfect numbers.

### 3rd ed. (2004), p. 80. Verbatim, from Google Books search-inside snippets (id=1AP2CEGxTkgC)
URL: https://books.google.com/books?id=1AP2CEGxTkgC (search-inside JSON endpoint, q="Erdős lets", "increasing sequence of divisors", "d1 < d2")

> "Erdős lets f(n) be the smallest integer for which n = Σ_{i=1}^{k} d_i for some k, where
> 1 = d_1 < d_2 < ⋯ < d_l = f(n) is the increasing sequence of divisors of f(n). Is f(n) = o(n)? Or is this true
> only for almost all n, with lim sup f(n)/n = ∞?"

A table follows: "n 1 2 3 … 28 / f(n) 1 – 2 3 – 5 4 7 15 12 21 …" (this matches OEIS A167485).
The OCR snippet drops the summation and ellipsis symbols, so I restored them from the 1st-ed. snippet, which reads
"1 = d1 < d2 < ··· < dl = f(n)". Everything else is verbatim from the snippets.
- **Guy includes the divisor 1.** ErGr80 starts at d_1 > 1. So f_Guy(N) = f_ErGr(N−1): A167485 is the ErGr version
  with the index shifted by 1, as the A387502 comment also says. Our bound carries over directly.
- **The 3rd edition adds "with lim sup f(n)/n = ∞".** This refines the question. Our density bound
  (#{N<X : f(N) ≤ N/K} ≤ S·X/K²) does **not** by itself show lim sup f(N)/N = ∞. It shows f(N) ≥ εN outside a
  set of density O(ε²).
- I found **no reference** attached to this paragraph in the snippets. It reads as a personal communication from Erdős
  ("Erdős lets"). The B2 bibliography on pp. 80–82 lists papers on quasiperfect, weird and multiperfect numbers.
  None of them is about this question.
- The paragraph just before it on p. 80 is a different Erdős question. It asks for n_k, "the smallest integer for which if you
  partition the proper divisors of n_k into k classes, n_k will always be the sum of distinct divisors from the same class".

### 1st ed. (1981), p. 29. Verbatim snippets (Google Books id=t_3lBwAAQBAJ, the Springer reprint of the 1st ed.; B1 is on p. 25)
URL: https://books.google.com/books?id=t_3lBwAAQBAJ

> "… (n) = [n/2] implies that n is 2 or a power of 3. Erdös lets f(n) be the smallest integer for which n = Σ_{i=1}^{k} d_i
> for some k, where 1 = d_1 < d_2 < ··· < d_l = f(n) is the increasing sequence of divisors of f(n). Is f(n) = o(n)?
> Or is this true only for almost all n?"

A table follows (n = 1..28; "… 57 14 36 46 30 12"), and then the B2 references (Abbott–Aull–Brown–Suryanarayana,
*Quasiperfect numbers*, …). The 1st edition does **not** have the "lim sup f(n)/n = ∞" clause.

### 2nd ed. (1994)
Not checked. The archive.org copies (unsolvedproblems0000guyr = 1994, unsolvedproblems0003guyr = 2004) are lending-only.
Their OCR text and in-book search returned 401 or "Item not available". The Google Books API was rate-limited. The wording
very likely matches either the 1st or the 3rd edition.

## 2. ErGr80 (Erdős & Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monogr. Enseign. Math. 28, 1980), p. 93

Pieced together from overlapping Google Books search-inside snippets (id=E-sZAQAAIAAJ, snippet view). The snippet OCR
interleaves the displayed formula with the text. Reconstructed wording:

> "For a given n, let 1 < d_1 < d_2 < ... be the divisors of n and consider the sums d_1, d_1 + d_2, d_1 + d_2 + d_3, ....
> How many new sums do we get from n, i.e., sums not occurring for m < n? When does N first occur as a sum? In
> particular, if f(N) denotes the least value of n for which N occurs, is it true that f(N) = o(N)? (or for almost all N?)"

(The phrases "How many new sums do we get", "from n, i.e., sums not occurring for m < n? When does N first occur as a sum?
In particular, if f(N) denotes the least value of n for which N occurs, is it true that f(N) … = o(N)? (or … almost all N?)"
and "For a given n, let 1 < d1 < d2 < ... be the divisors of n and consider" all appear verbatim in the snippets.)
The problem before it on p. 93 is about covering systems ("…every integer x less than n satisfies x ≡ a_i mod q_i…"). The
problem after it is about weird-type numbers, "Suppose n = d_1 + … + d_k where the d_i are distinct proper divisors of n
but this is not true for any proper divisor of n. Must the sum of the reciprocals of all such n converge?" (#470-ish).
ErGr80 gives **no reference or partial result** for this question.

### erdosproblems.com/468
URL: https://www.erdosproblems.com/468. Status **OPEN**. References: [ErGr80] only. OEIS: A167485, A387502, A387503.
The statement is a faithful paraphrase of ErGr80: "…is it true that f(N)=o(N)? Perhaps just for almost all N?"
The page does not mention Guy B2. Only the forum comment does.

### Forum thread
URL: https://www.erdosproblems.com/forum/thread/468. There is one comment, from Vjeko_Kovac on 14 Sep 2025. It gives
numerics: "31.279% of the numbers N≤100000 even have f(N)>100000", fewer than 6% of N ≤ 10000 have f(N)/N ≤ 0.5, and
"The claim f(N)=o(N) seems experimentally unlikely." The only rigorous statement is the trivial liminf f(N)/N = 0, which
follows from limsup σ(n)/n = ∞. The comment mentions Guy's book and the difference over whether 1 counts as a divisor.
**It proves nothing about almost all N.**

## 3. OEIS

- **A167485** (https://oeis.org/A167485): "Smallest positive integer m such that n can be expressed as the sum of an initial
  subsequence of the divisors of m, or 0 if no such m exists." Comments: "Is a(n) = o(n)? - Arkadiusz Wesolowski, Nov 09
  2013"; "The above question has been posed by Erdős. See Guy. - Stefano Spezia, Sep 25 2024"; "a(A000203(n)) <= n. Since
  A000203(n)/n can be arbitrarily large, that shows that lim inf_{n -> oo} a(n)/n = 0. - Robert Israel, Sep 26 2024".
  It conjectures that the only zeros are at n = 2 and n = 5, via a strengthened form of Goldbach. It cites Guy 1st ed. 1981, B2. There is a plot of a(n)/n up to 10^6.
  **It has no upper-density or lower-bound result.**
- **A387502 / A387503** (Kovač, 2025): these count the new sums |D_n \ ∪_{m<n} D_m| and the running total. The comments
  say that ErGr80 p. 93 is the source and that "A related problem on partial sums of divisors including 1 was posed by
  Erdős and it was mentioned towards the end of Section B2 of Guy's book from 1981." They contain numerics only.

## 4. Citing literature

Searches covered: "How many new sums do we get", "When does N first occur as a sum", "sum of an initial subsequence of the
divisors", "A167485", "Erdős problem 468", "partial sums"/"initial segments"/"initial sums" of divisors combined with
Erdős/o(N), and Guy B2 plus "f(n) = o(n)". **None found a paper that addresses this question.** The hits were unrelated.
They covered practical numbers, Egyptian fractions, σ-fibres, and Tenenbaum–Weingartner on dense divisors.
- Tenenbaum, "Some of Erdős' unconventional problems in number theory, thirty-four years later" (arXiv:1908.00488;
  Erdős Centennial 2013). This revisits Erdős 1979, "Some unconventional problems in number theory" (Astérisque 61 / Math. Mag. 52),
  which is the natural earlier home for a problem like this. The arXiv PDF could not be text-extracted: there is no
  pdftotext here and the fonts are custom. The abstract and search snippets only mention the d_1 < d_2 < 2d_1 density problem
  and the G(n) problem. **I did not confirm that the prefix-sum question is absent.** It could be worth a manual check.
  The Erdős 1979 and 1978 scans (renyi.hu 1979-23.pdf, 1978-26.pdf) are image-only and I could not read them.
- A full Google Scholar or Semantic Scholar "cited by" crawl of ErGr80 was not feasible, because ErGr80 has hundreds of
  citations. No targeted phrase search turned up a paper on this problem.

## Verdict

**PRIOR RESULT FOUND: no** (fairly confident, not certain).
Justification: Guy (1st and 3rd eds, B2) and ErGr80 p. 93 both state the question with no partial result and no
reference. The erdosproblems.com page (status OPEN, Sept 2026) and its forum have only numerics and the trivial
liminf f(N)/N = 0. OEIS A167485, A387502 and A387503 have only numerics and the same trivial liminf. Targeted searches
found no paper proving f(N) ≥ εN for almost all N or any density bound like #{N<X : f(N) ≤ N/K} ≪ X/K².
Remaining gaps: (i) Guy 2nd ed. was not seen; (ii) the Tenenbaum 2013 survey and the Erdős 1978/79 "unconventional problems"
papers were not text-searched. (iii) Note that Guy's 3rd-ed. clause "lim sup f(n)/n = ∞" is a separate question.
Our bound does not settle it.

# Erdős #1052 (unitary perfect numbers) — literature / novelty audit

Audit date: 2026-09-25. Web research only; no heavy compute.
Legend: **[READ]** = I read the primary source text myself; **[2nd]** = second-hand (quoted by OEIS, a later paper, or a review); **[ABS]** = abstract or zbMATH review only.

Notation: N = 2^m · n with n odd; r = ω(n) = number of odd prime factors ("odd components"); ω(N) = r + 1.

---

## 0. Bottom line (current state of knowledge)

| Constraint on a hypothetical 6th UPN N = 2^m n | Best known | Source | Status |
|---|---|---|---|
| N is even | yes | Subbarao–Warren 1966, Thm 1 | [READ] |
| number of odd prime factors r | **r ≥ 9** (so ω(N) ≥ 10) | Wall, Fib. Quart. 26 (1988) 312–317 | [READ, pp. 1–3; proof outlined] |
| exponent of 2 | **m ≥ 11**. m ∈ {1,2,6} only give 6, 90, 60, 87360; m ∈ {3,4,5,7,8,9,10} are impossible | SW 1966 Thm 2 + Subbarao–Cook–Newberry–Weber 1972 Thm 2 | [READ] |
| largest odd component (prime power p^e ‖ N) | **> 2^15** (smallest candidate 32771) | Wall, Fib. Quart. 25 (1987) 312–316 | [READ; proof only outlined, "table ... may be obtained from the author"] |
| odd part squarefree | then N ∈ {6, 60, 87360} | Graham, Fib. Quart. 27 (1989) 317–322 | [READ, p.1] |
| 3 ∤ N | then 2^m ‖ N with m ≥ 144, r ≥ 144, N > 10^440 | Frei, Elem. Math. 33 (1978) 95–96 | [2nd] (OEIS comment by A. Eldar) |
| size vs ω | N < 2^(2^k) where k = ω(N) | Goto, Rocky Mountain J. Math. 37 (2007) 1557–1576 | [ABS] (zbMATH review) |
| fixed m, or fixed ω | only finitely many UPNs | SW 1966 Thms 3, 4 (ineffective); Goto 2007 makes the ω version effective | [READ] / [ABS] |
| 5th UPN is the 5th smallest | no UPN between 87360 and 146361946186458562560000 | Wall, Canad. Math. Bull. 18 (1975) 115–122 | [ABS] (zbMATH review by Hagis) |
| exhaustive search | trivial sieve to 10^8 (GitHub, 2026); no published "no 6th below 10^x" bound | — | see §3 |

**No classification exists for r = 7 or 8 beyond "impossible"**, since Wall 1988 proves r ∉ {7, 8}. Combined with SW 1966 (r ∈ {1,2,4} give only the known ones; r ∈ {3,5} impossible) and SCNW 1972 (r = 6 impossible), **every r ≤ 8 is fully classified: only 6, 60, 90, 87360.** The 5th UPN has r = 11 (odd primes 3, 5, 7, 11, 13, 19, 37, 79, 109, 157, 313), so r ∈ {9, 10} is the first open window. For m, the classified set is {1,…,10}. The 5th UPN has m = 18, so m ∈ {11,…,17} is open in the published literature. Wall 1987 also rules out a = 78 and handles many a ≤ 46 in his internal case analysis (Table 2), but only for the "largest component < 2^15" subproblem.

I found **no** published improvement of r ≥ 9 (1988) or m ≥ 11 (1972) since then, and **no** modern published large-scale computer search.

---

## 1. Primary literature (exact citations and statements)

### 1.1 Subbarao & Warren 1966 [READ]
M. V. Subbarao, L. J. Warren, "Unitary perfect numbers", *Canad. Math. Bull.* **9** (1966), no. 2, 147–153. zbMATH 0139.26901; MR 33 #3994. Full text on Cambridge Core: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/741FD190AF22FFAC67645BCB29324531/S000843950005267Xa.pdf/unitary-perfect-numbers.pdf
- Introduces the definition and lists 6, 60, 90, 87360. They suggest it "might seem reasonable to conjecture" there is none larger than 87360, and record that Erdős thought the problem might be as hard as odd perfect numbers.
- Thm 1: no odd UPNs.
- Lemma 1: (3.1) p_r | 2^m+1 if a_1=…=a_{r−1}=1. (3.2) a+b+2c ≤ m+1, with equality when c=0. Here a = #primes ≡1 (mod 4), b = #primes ≡3 (mod 4) with even exponent, c = #primes ≡3 (mod 4) with odd exponent. Sharpened in (3.6) to a+b+Σ i·C_i = m+1.
- Lemma 2 (if 3 | N): m even; p^e ‖ n implies p^e ≡ 1 (mod 6) for p ≠ 3 [as printed]; some p ≡ 5 (mod 6) occurs with even exponent; r even. The authors state they could neither find a UPN with 3 ∤ N nor prove none exists.
- Thm 2: r=1 gives only 6; m=1 gives 6 or 90; m=2 gives 60; r=2 gives 60 or 90; m ∈ {3,4,5,7} impossible; r ∈ {3,5} impossible; m=6 gives only 87360; r=4 gives only 87360.
- Thm 3: for fixed m, finitely many UPNs with 2^m ‖ N. Thm 4: for a fixed number of primes, finitely many. Both are ineffective compactness arguments.

### 1.2 Subbarao, Cook, Newberry, Weber 1972 [READ, pp. 22–24 of 5]
M. V. Subbarao, T. J. Cook, R. S. Newberry, J. M. Weber, "On unitary perfect numbers", *Delta* **3** (1972), no. 1, 22–26. PDF (scanned) via Wayback: http://web.archive.org/web/20241227170642/http://www.math.ualberta.ca/~subbarao/documents/Subbarao_Cook_Newberry_Weber1972.pdf
- Corrects SW (2.1): the monotonicity statement is false (counterexample 25·41 vs 5·41²). The corrected version compares prime powers.
- **Thm 2: m ∈ {8, 9, 10} impossible; r = 6 impossible.** Proved by desk-calculator case analysis; details "in the possession of the authors".
- Wall 1988 summarises this as "a > 10 and b > 6" for any new UPN.

### 1.3 Subbarao 1970 [2nd]
M. V. Subbarao, "Are there an infinity of unitary perfect numbers?", *Amer. Math. Monthly* **77** (1970), 389–390. This is the Monthly problem that is the likely origin of the Subbarao prize offer; I did not read it. Wall 1987 cites it for "a > 10 except for the first four", which conflicts slightly with Delta 1972 being the source for m = 8–10. Both are cited.

### 1.4 Wall 1969 / 1975 [ABS]
- C. R. Wall, "A new unitary perfect number", *Notices AMS* **16** (1969), 825 (announcement of the 5th).
- C. R. Wall, "The fifth unitary perfect number", *Canad. Math. Bull.* **18** (1975), 115–122. doi:10.4153/CMB-1975-021-9. zbMATH 0312.10004; MR 51 #12690. zbMATH review (P. Hagis): the paper proves **there are no UPNs between 87360 and W = 146361946186458562560000 = 2^18·3·5^4·7·11·13·19·37·79·109·157·313.**

### 1.5 Wall 1987 — largest odd component [READ]
C. R. Wall, "On the largest odd component of a unitary perfect number", *Fibonacci Quart.* **25** (1987), no. 4, 312–316. https://www.fq.math.ca/Scanned/25-4/wall1.pdf
- Main result (outlined): **apart from the five known UPNs, the largest odd component K (prime-power unitary divisor) satisfies K > 2^15.**
- Method: entry points of primes p < 2^15 in 1+2^a. Table 1 lists the a ≥ 11 with 1+2^a having all components < 2^15: a ∈ {11,12,13,14,15,18,21,22,24,25,26,30,33,34,42,46,78}. The cases are then eliminated one by one; a = 24 is done in detail. It uses a > 10 from Subbarao [Monthly 1970].
- Most of the proof is omitted, with the table available "from the author". It has not been independently re-verified in print as far as I found.

### 1.6 Wall 1988 — nine odd components [READ, pp. 1–3 of 6]
C. R. Wall, "New unitary perfect numbers have at least nine odd components", *Fibonacci Quart.* **26** (1988), no. 4, 312–317. doi:10.1080/00150517.1988.12429611; MR 0967649; Zbl 0657.10003. https://www.fq.math.ca/Scanned/26-4/wall.pdf
- Exact statement: if N = 2^a m is a *new* UPN (not one of the five known), m odd with b distinct prime divisors, then **b > 8, i.e. b ≥ 9**. This is **unconditional**: no hypothesis on 3 | N or on a.
- It relies on Wall 1987 (N has an odd component > 2^15, smallest candidate 32771) and on a > 10, b > 6 (Subbarao et al.).
- Sections: seven odd components (Thms 2.1–2.4, forcing 3, 5, 7, then 13, 67, …, contradiction) and eight odd components. Proofs are "outlined, omitting repetitive details".

### 1.7 Graham 1989 [READ, p.1]
S. W. Graham, "Unitary perfect numbers with squarefree odd part", *Fibonacci Quart.* **27** (1989), no. 4, 317–322. https://www.fq.math.ca/Scanned/27-4/graham.pdf
- Thm: if 2^m s is a UPN with s odd and squarefree, then (m,s) ∈ {(1,3), (2,15), (6,3·5·7·13)}. It cites Wall [5] for "odd prime divisor exceeding 2^15".
- Note: Maciejewski 2026 attributes "any further UPN has an odd prime divisor > 2^15" to Graham. It is really Wall 1987, and there it is a *component* (prime power), not necessarily a prime.

### 1.8 Frei 1978 [2nd — not read]
H. A. M. Frei, "Über unitär perfekte Zahlen", *Elemente der Mathematik* **33** (1978), no. 4, 95–96. The e-periodica link on OEIS (https://www.e-periodica.ch/digbib/view?pid=edm-001:1978:33#105) did not give me the article text via scripted fetch.
- Per the OEIS A002827 comment by A. Eldar (2019): **if a UPN is not divisible by 3, then 2^m ‖ N with m ≥ 144, it has at least 144 distinct odd prime factors, and N > 10^440.**
- Needs a browser check of the actual statement (e.g. whether it is m ≥ 144 or m > 144).

### 1.9 Goto 2007 [ABS]
T. Goto, "Upper bounds for unitary perfect numbers and unitary harmonic numbers", *Rocky Mountain J. Math.* **37** (2007), no. 5, 1557–1576. doi:10.1216/rmjm/1194275935; zbMATH 1141.11006. Paywalled; I read the zbMATH review.
- **If N is a UPN with k distinct prime factors (k = ω(N), including 2), then N < 2^(2^k).** For a unitary harmonic number, N < (2^(2^k))^k.
- This makes SW Thm 4 effective (a Pomerance/Heath-Brown/Nielsen-type bound).

### 1.10 Other related, peripheral
- P. Hagis Jr., "Lower bounds for unitary multiperfect numbers", *Fibonacci Quart.* **22** (1984), no. 2, 140–143 [READ p.1–2]. This is about σ*(n) = kn with k ≥ 3, not k = 2. For k = 4 or 6: a ≥ 49, t ≥ 51, n > 10^110. For k ≥ 8: t ≥ 247. For odd k ≥ 5: n > 10^461.
- C. R. Wall, "Bi-unitary perfect numbers", *Proc. AMS* **33** (1972), 39–42: the only bi-unitary perfect numbers are 6, 60, 90.
- V. Sitaramaiah, M. V. Subbarao, "On the equation σ*(σ*(n)) = 2n", *Util. Math.* 53 (1998); "On unitary multiperfect numbers", *Nieuw Arch. Wiskd.* 16 (1998).
- T. Yamada (arXiv): no paper on UPN bounds. The related ones are "Unitary super perfect numbers" (arXiv:0802.4377; the odd unitary superperfect numbers are 9 and 165), "2 and 9 are the only biunitary superperfect numbers" (1705.00189), "Infinitary superperfect numbers" (1705.10933), "An analog of perfect numbers involving the unitary totient function" (1806.00647), and "Determining all biunitary triperfect numbers of a certain form" (2406.19331). **No Yamada improvement of r ≥ 9 or m ≥ 11 exists on arXiv.**
- Function-field analogues (Beard; Gallardo–Rahavandrainy, e.g. arXiv:1003.5316 "All unitary perfect polynomials over F_2 with less than five distinct prime factors") are not directly relevant.
- Also cited in OEIS but not read: Le Lionnais; Mitrinović et al. *Handbook of Number Theory* III.45.1; Sándor–Crstici *Handbook of Number Theory II* (2004), which zbMATH cites as a survey; Tattersall pp. 147–148; Lelechenko, TAAC 2014 "The quest for the generalized perfect numbers".

### 1.11 Guy, UPINT B3 [2nd — not read]
R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, §B3 "Unitary perfect numbers". MathWorld cites the 2nd ed. (1994), pp. 53–59, for the B-section range. I could not get the text: the Internet Archive copy is lending-only and inside-search failed. Per erdosproblems.com/1052, Guy reports that **Carlitz, Erdős, and Subbarao offer $10** for settling finiteness, and Subbarao offers **10 cents per new example**. MathWorld: "conjectured that there are only a finite number of even ones". Worth a library/Google-Books check for any additional bounds Guy quotes, e.g. Frei or Wall.

---

## 2. OEIS

**A002827** (https://oeis.org/A002827, rev. #76, last edited Jun 28 2026): 6, 60, 90, 87360, 146361946186458562560000; keywords nonn,nice,hard.
- Comments:
  - Muljadi (2005): "The prime factors of a unitary perfect number are the Higgs primes (A057447)." **This is unproven and suspicious.** A057447 is the exponent-3 Higgs primes, which exclude e.g. 17. I found no proof in the literature, and it is not a known theorem.
  - Sloane (2015): it is not known if a(6) exists.
  - Eldar (2019): the Frei result above.
  - Ianakiev (2020): conjecture that it is a subsequence of the Zumkeller numbers.
  - Luschny (Jun 2026): all UPNs are even, with a proof via the LeanGenius link.
- Formula (Eldar 2020): Goto's N < 2^(2^k).
- Links: erdosproblems 1052; Frei 1978; Goto 2007; Lelechenko 2014; Subbarao letter to Sloane (1974); Subbarao–Cook–Newberry–Weber 1972; Villemin; Wall letter to Hagis (1972); Wall 1975; Wall 1987; R. J. Walters LeanGenius "Erdős #1052"; MathWorld; Wikipedia.
  - The two letters are fragmented scans that I could not text-extract. They may contain historical search information.
- **There is no "no further terms below 10^x" comment.** OEIS records no explicit search bound.
- **The Wall 1988 "nine odd components" paper is NOT cited in A002827.** Wikipedia cites it.
- Related: A034448 (usigma), A057447 (3-Higgs primes), A034460, A327159 (usigma−x cycle sizes), A063991 (unitary amicable), A189000 (bi-unitary multiperfect; contains 6, 60, 90), A007357 (**infinitary** perfect, not bi-unitary), A003062, A290466, A293188, A327157, A327158.

---

## 3. Recent activity (2023–2026)

- **arXiv:2605.20475** (v1 19 May 2026, v2 24 May 2026): Tom Maciejewski (independent; njit.edu), "Bounded-box reductions in the Subbarao–Warren problem for unitary perfect numbers". https://arxiv.org/abs/2605.20475 [READ, intro, setup and refs from the HTML]
  - Explicitly **does not** prove finiteness.
  - It enumerates "source kernels" in a box (p ≤ 2000, e ≤ 6, p^e ≤ 10^9, SCC size ≤ 6). It finds the 2 known kernels (3^2, 5^4) plus 5 "impostor kernels", and eliminates those for seed 2^a+1 with 1 ≤ a ≤ 10000.
  - It reduces to a set H_even of even m such that every prime factor of 2^m+1 is 3-Higgs, and proves |H_even ∩ [2,40000]| ≤ 201 and |H_even ∩ [2,50000]| ≤ 272. It also gives a Ford-type thinness bound and several conditional results.
  - **Caveat, my assessment: the reduction rests on its Proposition 1, "every prime divisor of a UPN is 3-Higgs"** (essentially the Muljadi OEIS comment). The printed proof is incorrect: it uses q | p−1 | p^e+1, but p−1 does not in general divide p^e+1, and it bounds exponents by appealing to the box. So the paper's link to actual UPNs looks unsound, and its results should not be cited as constraints on UPNs without an independent proof.
  - It also misattributes the "> 2^15" result to Graham.
  - It links a mersenneforum ECM/SNFS thread.
- **erdosproblems.com/1052**: OPEN, "cannot be resolved with a finite computation", 0 comments, 0 proof claims, last edited 2 Sep 2026. teorth/erdosproblems `data/problems.yaml`: number "1052", prize "$10", status open (last_update 2025-09-28), formalized yes (2025-10-10), oeis [A002827], comments "unitary perfect numbers", tags ["number theory"].
- **Tao's AI-contributions wiki** (github.com/teorth/erdosproblems/wiki, pages "AI contributions to Erdős problems", "Notable cases…", "AI contribution section placement system"): **1052 does not appear**. I grepped the rendered pages for "1052" and "unitary". The nearby 1051 and 1054 do appear.
- **formal-conjectures (google-deepmind)**:
  - #902 (merged 2025-10-08) formalised the problem.
  - #4244 (merged 2026-06) links the 24-digit proof (Sanexxxx777 fork).
  - #4360 (OPEN, awaiting-author) links a fast 87360 proof.
  - #4405 (OPEN, Mnehmos) adds formal_proof links for even/87360/Wall's 5th, from Mnehmos/llm-driven-proof-search.
  - #2224, #2728, #3250 are closed attempts at even_of_isUnitaryPerfect.
  - All of these are test cases or evenness only. **No formalisation of Wall's r ≥ 9, the m-classification, Goto, or Graham.**
- Other GitHub activity, all trivial or low-value:
  - research-developer/erdos-banger PR #6 (brute sieve to 10^8, open).
  - rjwalters/lean-genius (erdos-1052 page: evenness proof).
  - DomTheDeveloper/formal-conjectures #273.
  - TheJustinSunPrize/awards JSP-000872 (Lean for 60; 6/60/90).
  - zjukop3/erdos872-unitary-perfect and chainstart/unitary-perfect-lean4 (Lean repos).
  - neelsomani/gpt-erdos candidate_solution.md (literature summary only).
  - techno-optimist/erdos-frontier-atlas (notes "web search 2026-07-18 found no new discovery").
  - dancinlab/hexa-lang (n=6 numerology).
- MathOverflow / math.SE: no substantive recent result surfaced in my web searches (not exhaustively crawled).

## 4. Sibling problems on erdosproblems.com
- 1052's LaTeX source cites only [Gu04]; there are no "see also" links.
- **#1053**: k-perfect numbers, must k = o(log log n)? This is Guy B2. OPEN, 0 comments, OEIS A007539.
- **#1051**: an irrationality problem, unrelated (solved; Aletheia / BKKKZ26).
- No bi-unitary or infinitary perfect problem is on the site as far as I saw.

## 5. Gaps / to-do for a human with library access
1. Read Frei 1978 (e-periodica, 2 pages) to confirm "m ≥ 144, r ≥ 144, N > 10^440" and its exact hypothesis.
2. Read Guy B3 (3rd ed.) text.
3. Read Wall 1988 pp. 4–6 (eight-components section) and Delta 1972 pp. 25–26 (the m=8 illustration).
4. Wall 1987/1988 proofs are outlines relying on unpublished tables. A modern machine re-verification (and extension to r ∈ {9,10} or m ∈ {11..17}) appears **never to have been done or published**. This is a plausible novelty target.

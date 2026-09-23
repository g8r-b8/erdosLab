# Erdős #132: novelty review

Checked 2026-09-23. Raw page and thread dumps are in `novelty_sources/`. This review follows the rule we
learned on #468: before calling anything new, read the threads of sibling and duplicate problems, not only
the #132 thread.

## Headline

- **Nothing we claim appears anywhere I could find.** That covers erdosproblems.com (#132 and 30+ sibling
  pages and threads), Tao's AI wiki, arXiv 2024–2026, citations of CDL, and the GitHub repos for #132.
- **No comment has been moved into or out of the #132 thread.** It still has exactly 5 comments, the newest
  from 25 Jul 2026. There is 1 proof claim (Beller, n = 8, 23 Aug 2026).
- **None of the sibling threads carries an edit like "solved under [N]".**
- **Two caveats:**
  - Result 4 is essentially LP duality applied to ienjoymath's published trade-off, and ienjoymath has
    announced a companion "LP analysis" note that has not appeared yet.
  - Result 1 is a small modification of CDL's own degree count.

| # | Result | Verdict |
|---|---|---|
| 1 | Cor A1 (H3 ⇒ μ(Δ₂) ≤ 3/2\|L1\|+\|L2\|), Lemma T, B1–B4 | A1: **NEW** (a minor corollary of CDL's proof). Lemma T: probably folklore (UNCLEAR). B1, B3, B4: **PARTIALLY KNOWN** (the counting lemma is known). B2: NEW as a combination. |
| 2 | Cap Lemma + Theorem E | **NEW** (not found; elementary) |
| 3 | Theorem A: 16n/11 + O(1) outside a window | **NEW** (not found; conditional, and does not cover the window) |
| 4 | "9/7 optimal ⇔ μ(δ) + (4/3)μ(Δ₂) ≤ 3n + o(n)" | **PARTIALLY KNOWN / UNCLEAR** (implicit in ienjoymath's trade-off; companion note announced but not published) |

## 1. Sources checked

### erdosproblems.com

**#132 page** (https://www.erdosproblems.com/132, accessed 2026-09-23).
- OPEN, $100.
- "See also [223], [756], and [957]."
- Comments (5), Proof claims (1).
- History: the only revision is dated 2025-10-20 (the CDL paragraph).
- The LaTeX source cites only HoPa34, Er84c, Er97e, ErFi95 and CDL25.

**#132 thread** (https://www.erdosproblems.com/forum/thread/132). Five comments, oldest first:

| Date | Who | Content |
|---|---|---|
| 28 Jan 2026 | Chojecki | GPT-5.2 argument for n = 8 |
| 28 Jan 2026 | Zeraoulia Rafik | n = 7, plus the n = 8 reduction |
| 05 Jul 2026 | Marche | 7 ≤ n ≤ 13 |
| 23 Jul 2026 | onetwothreefour | typo |
| 25 Jul 2026 | ienjoymath | 9/7 lower bound for Problem 1.6; n = 7, 8, 9, 10, 13 |

- **Nothing after 25 Jul 2026.**
- Post anchors: 3875, 3883, 7370, 8003, 8100.
- No moderator or Bloom comment, and no "moved" note.

**#132 proof claims** (https://www.erdosproblems.com/forum/thread/132/proof-claims). One claim:
- Evan Beller, submitted 2026-08-23, partial, n = 8 only. The notes say "the general problem remains open".
- Nothing newer.

**Tag "distances"** (https://www.erdosproblems.com/tags/distances): 55 problems. I read the page and the
thread for every candidate below.

| # | Topic | Anything matching results 1–4? |
|---|---|---|
| 223 (see-also) | diameter multiplicity in R^d | No. One comment (msellke, 13 Oct 2025, Swanepoel reference). |
| 756 (see-also) | ≫n distances each > n times (Bhowmick) | No. One comment (Woett, 15 Mar 2026, Aristotle formalisation). |
| 957 (see-also) | f(d₁)f(d_k) ≤ 9n²/8 (Dumitrescu) | No comments. The page records the stronger form f(d₁) ≤ 3n − 2m + o(√n), with m the number of hull vertices. That is a toolbox fact we already use (μ(δ) ≤ 3n − \|L1\|); it is not one of our results. |
| 958 | "k = n−1, i-th distance i times" | No. Seed-Prover and Aristotle only. The page credits CDL (2025). |
| 959 | a₁ − a₂ (CDL Problem 1.11) | No comments. |
| 97 | convex polygon: a vertex with no 4 others equidistant | No. Comments by veljjanoski (14 Sep 2026), sallerk (31 Aug and 17 Sep 2026), mysticflounder and others concern small n and symmetric cases. **Relevance:** our hypothesis (H3) in Cor A1 ("no hull vertex has 4 points at distance Δ₂") has the same flavour, restricted to one distance. Worth citing as context. It is not prior art for A1. |
| 96 | O(n) unit distances in convex position | No (Aggarwal 2016 status discussion). |
| 93, 94, 95 | Altman; Σf² ≪ n³ | No (Lean formalisations, Lefmann–Thiele sketch). |
| 98 | no 3 collinear, no 4 cocircular ⇒ h(n)/n → ∞ | No. DesmondWeisenberg (06 Sep 2026) has h(n) ≥ (n+2)/3 via convex layers. sallerk (18 Sep 2026) has exact h(n) for n ≤ 7. Both concern distinct-distance counts, not multiplicities. |
| 982, 1082 | distinct distances from a vertex; no-3-collinear ⌊n/2⌋ | No. sallerk (31 Aug 2026, #1082) reduces to h(k) = 2k+1 and notes "rigidity of the regular odd polygons". That is about distance counts; there is no Cap Lemma or Theorem E. |
| 89, 90, 91, 92, 99, 100, 103, 604, 605, 652–655, 1083–1088 | other distance problems | No. Keyword scan (132, Clemen, Dumitrescu, Vesztergombi, second largest, multiplicity) found nothing relevant. #1088 is not in the tag; its thread is empty. |

**teorth/erdosproblems `data/problems.yaml`.** No other entry mentions 132.

**Tao AI wiki** (https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems, "no
longer updated … as of Jun 30, 2026").
- **#132 does not appear.**
- Related rows: 90, 93, 94, 223, 652, 654, 756, 958, 1082, 1084. None touches μ(Δ₂), μ(δ), rare distances,
  or convex rare-distance counts.

### Literature

**CDL**, arXiv:2505.04283.
- v5 of 3 Feb 2026 is still the latest version. Published in Acta Math. Hungar. 177 (2025) 231–245.
- Problem 1.6 is still stated with the 9/8 construction, and the 3/2 upper bound comes only from Ve87.
- The CDL proof of Thm 1.3 uses deg ≤ 4 on L1′ (their observations (4)–(8)). It contains no concyclicity or
  degree-3 refinement.

**Citations of CDL.**
- Semantic Scholar (DOI 10.1007/s10474-025-01562-y): `citationCount: 0`.
- OpenAlex W4417084323 and W4416142823: 0 each.
- Google Scholar is not scriptable. Web searches found no citing paper.

**Vesztergombi.** Ve96 (Discrete Math. 150) abstract: "We determine all homogenous linear inequalities
satisfied by the numbers of occurrences of the two largest distances". That concerns (μ(Δ), μ(Δ₂)), not
layers, concyclicity or δ. On OpenAlex, Ve96 is cited only by CDL 2025, "Some Famous Problems of Discrete Geometry"
(2015) and "Large simplices determined by finite point sets" (2012).

**arXiv API, 2024–2026.** Queries run:
- "second largest distance" (only distance-eigenvalue graph papers)
- "interpoint distances"
- Vesztergombi
- "distinct distances" + "regular polygon"
- "convex polygon" + "distinct distances"
- "repeated distances" (2607.05374 Minkowski grid)
- "rich distances", "frequent distances", "distance multiplicities"
- ti:distances + ti:Erdős, e.g. 2601.09102, which is #659, not relevant
- "convex layers", "penny graph", "diameter graph"
- recent papers by Dumitrescu, Clemen and D. Liu, none on this topic since CDL

**Nothing improves on 3/2, gives a count of rare distances for convex sets, or states a layer bound under a
concyclicity hypothesis.**

**Web searches.** Queries on "second largest distance" multiplicity, "Problem 1.6" together with "3/2",
Vesztergombi + concyclic, Altman stability, and convex rare distances returned only CDL, the #132 thread and
classical papers (Altman, Fishburn, Morić–Pritchard 1103.0412, NPPZ 1207.1266).

### GitHub (gh search "erdos 132")

| Repo | Last push | Content |
|---|---|---|
| mathematiclover1337/erdos-132-note (ienjoymath) | 2026-07-25 | note.tex, code/ (see §4). The README links `RESULT3-upper-bound-program.md` and `NOTES.md`, but **both return 404**, so they were never pushed. |
| JuanMarchetto/erdos-132-note | 2026-07-05 | 7 ≤ n ≤ 13 |
| EvanBeller/erdos-132 | 2026-08-30 | n = 8 only. Its literature and candidate-lemma files have no overlap with our results. |
| lyfar/erdos132-wei-certificates | 2026-09-03 | Wei 2011 E₁₁(5) chain (n = 11, 12 support) |
| lyfar/erdos-132-moment-obstruction-lean | 2026-07-27 | conditional n = 14 |
| lyfar/erdos-132-convex-k3-lean | 2026-08-17 | Conditional Lean result: in strict convex position, the graph of the three largest distances has a vertex of degree ≤ 6 (Erdős–Lovász–Vesztergombi 1989). It is about ELV large-distance sums. It does **not** count rare distances and does not overlap Theorem E. |
| DeckardShaw31/erdos-132-proof | 2026-09-10 | Claims a "complete resolution" via energy/Cauchy–Schwarz. It uses CDL's layer bound verbatim, with no H3 or 16/11. It looks unsound (it asserts Lefmann–Thiele gives ½M³ energy bounds, and so on) and was not posted to the forum. No overlap. |
| JAgbanwa/Erdos-Problem-132 | 2026-08-05 | "Light distances" paper. Thm "Q1 when \|D(A)\| > (n−1)/2", which is **our Lemma B / B-counting** (see §1 below). The rest is energy methods and n ≤ 6. |
| vibemathing/problem-…-132 | 2026-09-06 | harness scaffold only, no mathematics |

## 2. Per-result verdicts

### Result 1 (angle C)

**Corollary A1: NEW, but a minor corollary.**
- In CDL's proof of Thm 1.3 (arXiv 2505.04283v5 §2.2) the only per-vertex input is "deg(p) = deg₁(p) +
  deg₂(p) ≤ 4". A1 replaces 4 by 3 under (H3) and keeps track of the excess.
- No source states a bound of the form (3/2)|L1| + |L2|, the criterion |L1| ≤ 2m₃, or any no-4-concyclic
  variant of Thm 1.3. That includes CDL v5, the #132 thread, the #97 and #98 threads (where no-4-cocircular
  and "4 equidistant vertices" hypotheses are discussed), and the GitHub repos.
- #97 (erdosproblems.com/97) is the natural thing to cite for the flavour of (H3).
- Expect a referee to call this "a straightforward refinement of CDL". It widens the class of proved sets,
  but only under a genericity hypothesis.

**Lemma T: UNCLEAR, probably folklore.**
- The content is SSS congruence ⇒ an isosceles trapezoid ⇒ concyclic.
- Vesztergombi's Ve96 case analysis almost certainly uses equivalent reasoning. I could not read Ve96: it is
  paywalled and the OpenAlex abstract is one line.
- Do not claim it as new.

**B1–B4: PARTIALLY KNOWN.**
- The counting lemma s′ ≥ (n+1)(2D−n)/(2n) is implicit in CDL's proof of Thm 1.2. That proof says: "If X
  determines strictly more than ⌊n/2⌋ distinct distances and all distances smaller than Δ occur more than n
  times, then … ⌊n/2⌋(n+1)+1 > C(n,2)".
- It is also stated as a theorem in JAgbanwa/Erdos-Problem-132 (light_distances.tex, "Q1 when |D(A)| > (n−1)/2").
- B1 and B3 are one-line consequences of this and should be presented as such.
- B2 (Pach–de Zeeuw ⇒ (a), and s′ ≥ n/2 when ≥ C n^{3/4} points lie on a curve with no line or circle
  component) was not found anywhere. It is new as a combination of known results, but easy.
- B4 was not found. It is elementary.

### Result 2 (angle B): Cap Lemma + Theorem E

**NEW. Not found; elementary.**
- Checked against:
  - CDL Thm 1.2, which gives only "≥ 2 rare distances" for convex sets;
  - the Altman and Fishburn classifications;
  - the #93, #982 and #1082 threads (sallerk's "rigidity of the regular odd polygons" is about h(k) = 2k+1
    for distance counts);
  - lyfar's convex-k3 Lean repo (ELV top-three graph, a different question);
  - arXiv and web searches for convex rare-distance counts or "regular polygon plus points".
- Nobody states "a convex n-set containing a regular a-gon has ≥ a − (n+1)/2 distances of multiplicity ≤ n",
  or any lower bound > 2 on the number of rare distances for convex sets.
- Caveat: the Cap Lemma is elementary trigonometry and may be folklore in the k-distance-set literature on
  "regular polygon + points" (e.g. Erdős–Fishburn and Wei classify sets such as R₇ ∪ {centre}). I found no
  statement of it.
- The question whether s(A) → ∞ for convex sets is not raised anywhere on the site. It is not a CDL problem
  either.

### Result 3 (angle A): Theorem A, min{μ(Δ₂), μ(δ)} ≤ 16n/11 + O(1) outside the window

**NEW. Not found; conditional and incomplete.**
- The upper bound 3/2 is untouched everywhere I looked:
  - CDL v5 §1.1;
  - ienjoymath's note: line 74 reads "Vesztergombi's bound μ(Δ₂) ≤ 3/2 n [Ve87] gives L ≤ 3/2", and the note
    works only on the lower bound;
  - the #132 thread and every sibling thread;
  - arXiv and web.
- No "16/11" or any improvement of the Problem 1.6 upper bound exists anywhere.
- It must still be presented as partial, because the resonant window √3/2 < t/δ ≤ 1 and the degenerate
  regime Δ > (2−κ)Δ₂ are open, so there is no unconditional L < 3/2.

**Main risk: ienjoymath's announced companion note.**
- note.tex lines 213–215: "Supporting evidence, including a linear-programming analysis over Vesztergombi's
  structural constraints [Ve85, Ve87, Ve96] in which the construction above is simultaneously extremal for
  every inequality, will appear in a companion note."
- The README also lists `RESULT3-upper-bound-program.md`, "research notes toward the conjectured optimal
  constant 9/7 (work in progress)", but that file is not in the repo (404).
- If that note appears, it could contain an upper-bound programme. As of 2026-09-23 there is none: the repo
  was last pushed 2026-07-25 and there is no further forum post.

### Result 4 (angle D): "9/7 optimal ⇔ μ(δ) + (4/3)μ(Δ₂) ≤ 3n + o(n)"

**PARTIALLY KNOWN / UNCLEAR.**
- The inequality is exactly the LP dual certificate of the trade-off that ienjoymath published on the forum
  (25 Jul 2026): "changing the trade-off from min(3m, 3n−5m) to min(3m, 3n−4m)". The weights 4/7 and 3/7 give
  4·(3m) + 3·(3n−4m) = 9n.
- ienjoymath also explicitly claims an LP over Vesztergombi's constraints "in which the construction … is
  simultaneously extremal for every inequality" (companion note, unpublished).
- So the reduction itself is essentially implicit in public work. Anyone could derive it in one line, and
  ienjoymath has announced (but not published) the LP picture around it.
- The parts that are ours:
  - the explicit statement F := μ(δ) + (4/3)μ(Δ₂) ≤ 3n + o(n);
  - the numerical facts: F = 3n exactly on the even ring core, 3n − m on the odd core, and 3n − (2/3)n for
    R_odd;
  - the gadget screening (4a + 3b ≤ 7);
  - the heuristic Euler-face-deficit argument.
- The heuristic argument is not a proof and should not be claimed as one.
- Credit ienjoymath for the trade-off if this is ever posted.

## 3. Suggested wording if anything is posted

- Credit:
  - CDL for Thm 1.2, Thm 1.3 and Problem 1.6;
  - ienjoymath (25 Jul 2026) for 9/7 and for the announced LP analysis;
  - Rafik, Marchetto and Beller for small n.
- Present A1 as "a refinement of CDL's degree count under (H3) (cf. #97)".
- Present B1–B4 as consequences of the pair-counting identity already used by CDL.
- Theorem E and Theorem A are the two items with a plausible novelty claim. Theorem A is only a partial
  upper bound.
- Re-check before posting:
  - the #132 thread (anchor after post-8100);
  - https://github.com/mathematiclover1337/erdos-132-note, for the companion LP note;
  - arXiv listings for Clemen, Dumitrescu and D. Liu.

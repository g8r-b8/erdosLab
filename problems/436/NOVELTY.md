# Erdős #436: novelty audit of Λ(5,3) ≥ 5,062,794

Audit date: 2026-09-23. Every URL below was accessed on that date. Raw dumps are in `novelty_sources/`. Copies of
paper PDFs and their text extractions (`*.pdf`, `*.pdf.txt`) are gitignored, as for #132.

## Verdict

| Result | Verdict |
|---|---|
| **Λ(5,3) ≥ 5,062,794.** The claim is that there are infinitely many primes p with r(5,3,p) ≥ 5,062,794. It rests on a SAT model with no zero-run below that point, plus Chebotarev / independence of quintic characters. | **NEW.** Nobody has published a numerical lower bound, table or computed value of Λ(5,3), or of any Λ(k,3) with k ≥ 5. There is a small residual risk from two classical sources I could not read (see below). |
| The reduction Λ(k,l) = Λ_comb(k,l) for odd k (completely additive f: Z>0 → Z/k) | **KNOWN (method).** This is exactly the Lehmer–Lehmer–Mills "case vector" framework. The lower-bound half is the fact that "for k < 8 every case vector corresponds to an infinite class of primes", which BLL64 attribute to their reference [6]. Present it as the classical reduction and cite LLM63/BLL64, not as ours. |
| The SAT/CDCL encoding, the smooth-run weakening F_y(X), and the Knuth tree-size estimate (≈1e18) | **NEW as tooling.** LLMS62 used exactly the "triplets of S-smooth numbers dispose of S-vectors" idea for k = 3, by machine case enumeration. Our F_y(X) is the SAT form of that 1962 method. No SAT treatment of the problem exists. |

## Sources checked

**erdosproblems.com**
- Page https://www.erdosproblems.com/436 (`erdosproblems_436_20260923.txt`):
  - Status OPEN; last edited 25 Oct 2025.
  - Comments (3), Proof claims (0).
  - No "See also" or duplicate links.
  - OEIS link: A000445 only.
  - The page lists only the known values Λ(2..7,2), Λ(3,3) = 23532, and Λ(k,3) = ∞ for even k. For odd k ≥ 5 it states that finiteness of Λ(k,3) remains to be examined. It gives no bound for Λ(5,3).
- Thread https://www.erdosproblems.com/forum/thread/436 (`erdosproblems_436f_…`): unchanged. It still has 3 comments: Adenwalla (24 Oct 2025), Bloom (25 Oct 2025) and Adenwalla (25 Oct 2025, a link to a VDW-related bibliography). None contains computations.
- Proof claims (`…436pc…`): none.
- History (`…436h…`): only the 2025-10-20 revision.
- LaTeX source (`…436tex…`): saved.
- Rule-4 sibling check: there are no see-also or duplicate pages to follow.

**Classical papers.** All of these were read in full; the PDFs are in `novelty_sources/`, gitignored.
- LLM63: Lehmer–Lehmer–Mills, *Pairs of consecutive power residues*, Canad. J. Math. 15 (1963) 172–177 (`llm63.pdf`). It deals only with pairs, Λ(k,2) for k ≤ 6. It restates the Lehmer–Lehmer result Λ(k,m) = ∞ for k even and m ≥ 3, and for 2 < k < 1048909 with m ≥ 4. Nothing on (5,3).
- LLMS62: Lehmer–Lehmer–Mills–Selfridge, *Machine proof of a theorem on cubic residues*, Math. Comp. 16 (1962) 407–415, read via the Wayback copy of the AMS PDF (`llms62.pdf`). It covers k = 3, triplets only. Its method uses triplets of consecutive integers whose prime factors all lie in S, plus exhaustive S-vector disposal. That is the ancestor of our F_y(X). Nothing on k = 5.
- BLL64: Brillhart–Lehmer–Lehmer, *Bounds for pairs of consecutive seventh and higher power residues*, Math. Comp. 18 (1964) 397–407 (`bll64.pdf`, Wayback). It covers pairs only, k = 7..10. It gives the independence remark "For k < 8, to each case vector … there corresponds an infinite class of primes", which supports our Chebotarev step for k = 5. Nothing on triples.
- Dietzel, arXiv:1309.7506 (2013) and arXiv:1810.01518 (2018, Moscow J. Comb. Number Theory 8 (2019)): these give elementary Hindman/IP-set proofs of Hildebrand's pair theorem. The only triple content is the k = 2 aside Λ(2,3) = ∞. Nothing on odd k ≥ 5.
- Mishra–Santonastaso, arXiv:2507.11828 (blocking sets and q-th power residues modulo integers with few prime factors; to appear in Acta Arith.). No occurrence of "consecutive", Lehmer or Hildebrand. It is unrelated to runs.
- Lehmer obituary and bibliography, Acta Arith. 62.3 (1992), http://matwbn.icm.edu.pl/ksiazki/aa/aa62/aa6231.pdf (`aa62.pdf`). D. H. Lehmer's publication list has only #101 (runs, 1962), LLMS62, LLM63 and BLL64 on this topic. So the Lehmers never published a paper on Λ(5,3).

**OEIS** (`oeis_*.txt`)
- A000445 (Λ(k,2)): references LLM63, BLL64, Dietzel, Dunton, Hildebrand, Jordan, Rabung–Jordan and Mills 1965, plus Reble's 2019 computation for k = 8. It covers pairs only.
- **A188384**, "Primes for which there are not three consecutive nonzero quintic residues" (T. D. Noe, 2011). It quotes Lehmer, *Mechanized mathematics* (BAMS 72, 1966): every prime > 3331 has *some* triple of consecutive quintic residues. **This is a different quantity.** It is the existence of a triple anywhere in [1, p−1], not the position r(5,3,p) of the first one, and it says nothing about the limsup. It neither contradicts nor anticipates our bound.
- A000236 and A097160: not relevant (non-residue runs; quadratic case).
- Searches run: "consecutive residues", "consecutive quintic", "consecutive power residues" and "Lehmer residues runs". No sequence tabulates r(5,3,p) or Λ(k,3).

**Citations (OpenAlex)** (`openalex_citations_20260923.txt`)
- LLMS62 has 25 citers and BLL64 has 13. Both sets are all from 1963–2011: Jordan, Rabung–Jordan, the Eisenstein-integer analogues (1969/1974), Emma Lehmer "Patterns of power residues" (1983), Hildebrand 1986, Erdős–Graham 1980, Guy's Monthly unsolved problems (1983), and historical and philosophical essays.
- Hildebrand 1991 has 6 citers: Dietzel ×2, Wright 2007, Phong 2006 and Hildebrand's own notes. None is about triples for k ≥ 5.

**arXiv API** (`arxiv_queries_20260923.txt`)
- Queries run: "consecutive power residues", "k-th power residues" + consecutive, "quintic residues", "Erdos problem 436", "completely multiplicative" + roots of unity + consecutive, and Hildebrand + power residues.
- Hits were only 1309.7506, math/0312010 (Sun, runs mod composite m, unrelated) and 1702.01470 (Najnudel, a probabilistic model of consecutive values of random multiplicative functions, with no Λ bounds).

**Web search**
- Queries: "consecutive quintic residues" triples; Λ(5,3); "5,062,794"; the Mills 1965 survey; completely multiplicative with fifth roots of unity and three consecutive values; Lehmer "runs of residues" + quintic.
- Nothing gives a Λ(5,3) value or bound.
- Tangential: arXiv:2404.04981 (±1 completely multiplicative sequences omitting consecutive +1s, the k = 2 analogue) and 2402.10737 / 2607.17267 (consecutive squares or non-squares in finite fields).

**GitHub** (`github_jsp_20260923.txt`)
- Repo search for "erdos 436", "erdos-436" and "consecutive power residues" found only `vibemathing/problem-um-ep-436-…` (pushed 2026-09-06). It is an empty harness scaffold: a single planned "source-fidelity" attempt, with no artifacts and no results.
- google-deepmind/formal-conjectures: issue #731 "Erdős Problem 436" is open. There is no 436 file.
- TheJustinSunPrize/awards:
  - PR #278 (JSP-000355, Ren, 16 Sep 2026): a Lean proof of Λ(2,2) = 9 only. Its scope says explicitly that Λ(k,3) is "not claimed". Closed as partial on 20 Sep 2026.
  - PR #3388 (JSP-000436, 22 Sep 2026, open): its diff contains only trivial `Nat.Prime 2`-type lemmas. The cited file `src/latest/ErdosProblems/Erdos436.lean` does **not exist** in plby/lean-proofs (API 404; the repo tree has no such file). No mathematical content.
- teorth/erdosproblems `problems.yaml`: 436 is open and unformalized (last_update 2025-08-31).
- Tao's AI-contributions wiki: no 436 entry (per the NOTES.md triage; the wiki is frozen since 30 Jun 2026).
- unsolvedmath.com/problems/EP-436 sits behind a Vercel bot checkpoint. It was not accessed, and I did not try to bypass the check.

## Could not read (residual risk)

1. **Lehmer, *Mechanized mathematics*, BAMS 72 (1966) 739–759.** AMS and Project Euclid returned 403 and there is no Wayback copy. It discusses quintic triples (the 3331 statement). It *might* also report a machine search for r(5,3,p) and some lower bound. If it does, that bound would almost certainly be far below 5·10⁶, given 1966 hardware and the fact that Λ(3,3) = 23532 was their frontier. It is still worth reading before any public claim.
2. **W. H. Mills, *Bounded consecutive residues and related problems*, Proc. Symp. Pure Math. 8 (1965) 170–174** (AMS survey, not online). It may state the (5,3) problem and a small lower bound.
3. **Lehmer–Lehmer, *On runs of residues*, Proc. AMS 13 (1962) 102–106.** AMS returned 403. Its content, as quoted in LLM63 and on the site, is Λ(k,3) = ∞ for even k and Λ(k,4) = ∞ for k < 1048909.

Suggested wording: "To our knowledge no lower bound for Λ(5,3) beyond trivial ones has been published; we show Λ(5,3) ≥ 5,062,794 by an explicit character assignment (SAT model), using the Lehmer–Lehmer–Mills case-vector reduction." Credit LLMS62 for the smooth-triplet method.

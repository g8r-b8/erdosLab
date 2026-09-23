# Pre-flight novelty re-check: Erdős #132 / CDL Problem 1.6

**Date of check:** 2026-09-23 (about 17:30 local time). Compared against `problems/132/novelty_sources/forum132.txt` and NOVELTY.md (Audits 1–2, also 2026-09-23).

## Verdict

**No red flags.** Nothing new has appeared that threatens the novelty of the 54/37 bound (Theorem 1) or of the other results. No public upper bound below 3/2 for CDL Problem 1.6 exists, and ienjoymath's announced LP companion note is still unpublished.

**Repeat this check on the day of posting or submission.** The residual risk is unchanged: ienjoymath's LP note could appear at any time.

## Findings

### 1. Forum thread for #132
- URL: https://www.erdosproblems.com/forum/thread/132
- There are still **5 comments**, and they match the saved copy:
  - ienjoymath, 25 Jul 2026 17:54;
  - onetwothreefour, 23 Jul 2026;
  - Marche, 05 Jul 2026;
  - Zeraoulia Rafik, 28 Jan 2026;
  - Przemek Chojecki, 28 Jan 2026.
- **Nothing has been posted after ienjoymath's 25 Jul 2026 comment.**

### 2. Problem page
- URL: https://www.erdosproblems.com/132
- Status is still **OPEN**, and the \$100 prize still cites [Er97e].
- The page shows Comments (5), Proof claims (1) and Proof expositions (0).
- "Formalised statement?" still reads No.

### 3. Proof claims
- URL: https://www.erdosproblems.com/forum/thread/132/proof-claims
- There is still **1 claim**: Evan Beller, for the n = 8 case of the first question only.

### 4. ienjoymath's companion LP note
- Repo: https://github.com/mathematiclover1337/erdos-132-note
- The repo was last pushed 2026-07-25T18:06Z. It has 2 commits, both on 25 Jul, "Add files via upload", and 0 forks.
- Its contents are unchanged: `README.md`, `code/`, `note.pdf`, `note.tex`. `note.tex` is byte-identical to `novelty_sources/ienjoymath_note.tex`.
- `RESULT3-upper-bound-program.md` and `NOTES.md` still return **HTTP 404**.
- The user has no other public repositories.
- **The LP analysis has not appeared.**

### 5. arXiv
Queries were run through https://export.arxiv.org/api/query, newest first:
- CDL (arXiv:2505.04283) is **still v5 (2026-02-03)**.
- **CDL authors' listings:**
  - Adrian Dumitrescu: latest is 2609.25288, 2026-09-21, on Rado's covering problem. Off-topic.
  - Felix Christian Clemen: latest is 2608.14687, which is off-topic. 2606.05841, "Geometric Sidon Problems", was already known and does not overlap.
  - Dingyuan Liu: latest is "Extremal problems for suspensions of even cycles", 2026-08-23. Off-topic.
- **Phrase searches:**
  - "second largest distance" and "second-largest distance" return only graph distance-eigenvalue papers.
  - "distance multiplicities" returns only CDL.
  - "interpoint distances" returns only off-topic papers (random-point limit laws, clustering).
  - Hopf with Pannwitz, and "Erdos problem 132", find nothing relevant.
- **No arXiv paper improves 3/2 for Problem 1.6, and none cites CDL on this question.**

### 6. Citations of CDL
- OpenAlex has **0 citing works** for W4417084323 and for W4416142823 (the arXiv and Acta Math. Hungar. records).
  - https://api.openalex.org/works?filter=cites:W4417084323
  - https://api.openalex.org/works?filter=cites:W4416142823
- The Semantic Scholar citations API returned HTTP 429, so it was not checked.

### 7. GitHub
- `gh search repos` for "erdos 132", "erdos132" and "erdos-132" returned only repos already listed in NOVELTY.md.
  - The latest push is DeckardShaw31/erdos-132-proof, on 2026-09-10.
  - Nothing has been pushed after 2026-09-10.
- `gh search code "2505.04283"` returned only hits already known: formal-conjectures 756/958, agentic-erdos, l3afyb0y, lean-genius 958/959 and others. None is on Problem 1.6 upper bounds.

### 8. Web search
- Queries: CDL "multiplicities of interpoint distances" with upper bound 3/2 improvement; "Erdős problem 132" with 54/37, 9/7 and CDL.
- Results were only CDL (arXiv, Springer https://link.springer.com/article/10.1007/s10474-025-01562-y), the #132 forum thread, the tags page and classical references.

## Still to do on the day of posting
- [ ] Re-fetch the forum thread and the proof-claims page, looking for anything after 25 Jul 2026.
- [ ] Re-check the ienjoymath repo for the two 404 files and for new commits.
- [ ] Re-run the arXiv author listings for Clemen, Dumitrescu and Dingyuan Liu, and check that CDL is still v5.
- [ ] Try Semantic Scholar citations of arXiv:2505.04283 (rate-limited today).

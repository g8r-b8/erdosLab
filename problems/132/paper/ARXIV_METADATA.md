# arXiv submission metadata (DRAFT: not submitted)

The source bundle is `arxiv/arxiv-source.tar.gz`. It contains `paper.tex`, `paper.bbl` and `refs.bib`.
- It compiles with plain `pdflatex` ×3 from a clean extract, without bibtex, because arXiv uses the `.bbl`.
- The result is 66 pages, with no undefined references or citations and no overfull boxes.
- It uses only standard TeX Live packages and has no figures or external files.
- **Before uploading:** make sure the repository https://github.com/g8r-b8/erdos132-lean contains every script cited in the appendix (v2 adds `r1_*`, `r2_verify.py`, `r2_local_lemmas.py`, `r3_*`, `r4_*`, `r5_verify_n8.py`; v3 adds `r6_n3_*`, `r6_ref_*`, `r6_refB1_*`, `r6_below_*`, `r6_Eprime_full_checks.py`, `r6_refE_parallel.py`, `r6_gap_L_family.py`, `r6_gap_M_pairgap.py`, `r7_A2_*`, `r7_B_*`, `r7_refB_*`, `r6_below_*_B1copy.py`). After any edit, rebuild the `.bbl` and the tarball:
  ```
  cd arxiv && pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper
  COPYFILE_DISABLE=1 tar -czf arxiv-source.tar.gz paper.tex paper.bbl refs.bib
  ```
- The arXiv copy differs from `../paper.tex` only in the date line: `\date{25 September 2026}` replaces "Draft of …". Keep the two in sync if you edit either one.

## Fields

**Title**
Second-largest and minimum distance multiplicities in planar point sets: an upper bound of 4/3, and related results on Erdős Problem #132

**Authors**
Wingate Jones

**Abstract** (plain text; the arXiv limit is 1920 characters)
```
For a finite set X in the plane let Delta_2 and delta be the second-largest and the smallest distance determined by X, and let mu(d) be the number of pairs of X at distance d. Clemen, Dumitrescu and Liu asked for L = limsup_{n->oo} max_{|X|=n} min{mu(Delta_2), mu(delta)}/n; the known bounds were 9/7 <= L <= 3/2, the upper bound coming from Vesztergombi's inequality mu(Delta_2) <= 3n/2. We prove that min{mu(Delta_2), mu(delta)} <= (4/3)n + C_0 for an absolute constant C_0, so L <= 4/3. The new step is an averaged bound for the points with no partner at distance Delta_2; locally extremal configurations pin (Delta - Delta_2)/delta to one of two short intervals. For a scale-invariant measure tau(X) of the excess of the diameter over Delta_2, we get (21/16)n + C_1 when tau(X) <= sqrt(3)/2 - 0.02 or tau(X) >= sqrt(3)/2 + 0.03, and (9/7)n + O(n^{2/3}) when tau(X) > 1, which matches the lower bound. A weaker bound, (15/11)n + C_0, is formalised in Lean 4 with Mathlib.

We also give three results on Erdős Problem #132, which asks whether some distance other than the diameter must occur at most n times. First, if no hull vertex has four points of X at distance Delta_2, then mu(Delta_2) <= (3/2)|L_1| + |L_2|, where L_1, L_2 are the first two convex layers. Second, for n points in convex position at least three distances occur between 1 and n times when n is even and at least 6, and when 6 <= n <= 18; the cases n = 11, 13, 15, 17 are computer-assisted, certified by DRAT proof checking (and n = 7, 11, 13 also in Lean 4). Third, if all but w of n points in convex position lie on one circle, with n >= 3w and n + w >= 91, then at least (n - 3w + 1)/4 distances occur between 1 and n times.
```

This abstract is a shortened plain-text version of the paper's abstract (it omits the remark on the proof method for the almost-cocircular result and the statement that the bounds 4/3, 21/16 and 9/7 are not formalised, which is in the Comments field).

**Primary category:** math.CO (Combinatorics)
**Cross-list:** math.MG (Metric Geometry)

**Comments**
```
66 pages. The 15/11 and 54/37 versions of the main theorem are formalised in Lean 4/Mathlib (sorry-free, standard axioms only); the 4/3, 21/16 and 9/7 bounds are not formalised (a formalisation of 4/3 is in progress); code, Lean files and certificates at https://github.com/g8r-b8/erdos132-lean. An AI assistant (Claude, Anthropic) was used for exploration, computation, formalisation and drafting; see the AI disclosure in the paper.
```

**MSC classes:** `52C10` (primary: Erdős problems and related topics of discrete geometry). Optional secondaries:
- `68V20` (formalisation of mathematics in connection with theorem provers). This is apt because the Lean formalisation is a major component.
- `52A10` (convex sets in 2 dimensions). This is apt for the convex-position results.
- `05D99` fits less well. The paper has no extremal set-theory content beyond counting, so prefer 68V20.

Suggested MSC string: `52C10 (Primary) 68V20, 52A10 (Secondary)`

**Journal-ref / DOI:** leave empty until published.
**License:** the arXiv perpetual non-exclusive licence (the default), or CC BY 4.0 if you want maximum reuse.

## Endorsement (first-time submitter)

- arXiv requires an **endorsement** from an established author the first time you submit to a category (math.CO here).
- The cross-list to math.MG needs no separate endorsement.
- Institutional email addresses are sometimes auto-endorsed, but a personal Gmail account will almost certainly need an endorser.
- How it works:
  1. Start the submission at https://arxiv.org/submit. arXiv shows an endorsement code and a link.
  2. Ask someone who is registered as an endorser for math.CO to enter the code at https://arxiv.org/auth/endorse.
  3. The endorsement page for any math.CO paper shows "Which of these authors are endorsers?", which helps you find one.
- Ask someone who knows the work. A natural choice is one of the CDL authors, but only *after* they have responded positively to the email in `EMAILS_DRAFT.md`, and never as a cold request in the first message.
- Endorsers vouch that the paper is appropriate scholarly work, not that it is correct.
- See https://info.arxiv.org/help/endorsement.html.
- Check arXiv's current policy on AI-assisted papers before submitting (https://info.arxiv.org/help/policies). The paper already names the AI tool and its role, and the author takes full responsibility for the content.

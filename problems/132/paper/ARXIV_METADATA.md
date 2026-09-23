# arXiv submission metadata (DRAFT: not submitted)

The source bundle is `arxiv/arxiv-source.tar.gz`. It contains `paper.tex`, `paper.bbl` and `refs.bib`.
- It compiles with plain `pdflatex` ×3 from a clean extract, without bibtex, because arXiv uses the `.bbl`.
- The result is 21 pages, with no undefined references or citations. There is one harmless 6.6 pt overfull hbox, in the Lean paragraph.
- It uses only standard TeX Live packages and has no figures or external files.
- **Before uploading:** replace `https://github.com/<user>/erdos132-lean` in `arxiv/paper.tex`, in §"Computational verification" (look for the `TODO(author)` comment). Then rebuild the `.bbl` and the tarball:
  ```
  cd arxiv && pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper
  COPYFILE_DISABLE=1 tar -czf arxiv-source.tar.gz paper.tex paper.bbl refs.bib
  ```
- The arXiv copy differs from `../paper.tex` in only two places: the repository URL TODO replaces `\placeholder{REPOSITORY URL}`, and `\date{23 September 2026}` replaces "Draft of …". Keep the two in sync if you edit either one.

## Fields

**Title**
Second-largest and minimum distance multiplicities in planar point sets: an upper bound below 3/2, and related results on Erdős Problem #132

**Authors**
Wingate Jones

**Abstract** (plain text, 1368 characters; the arXiv limit is 1920)
```
For a finite set X in the plane let Delta_2 and delta be the second-largest and the smallest distance determined by X, and let mu(d) be the number of pairs of X at distance d. Clemen, Dumitrescu and Liu asked for L = limsup_{n->oo} max_{|X|=n} min{mu(Delta_2), mu(delta)}/n; the known bounds were 9/7 <= L <= 3/2, the upper bound coming from Vesztergombi's inequality mu(Delta_2) <= 3n/2. We prove that min{mu(Delta_2), mu(delta)} <= (54/37)n + C_0 for an absolute constant C_0, so L <= 54/37 < 3/2. This theorem is formalised in Lean 4 with Mathlib.

We also give two results on Erdős Problem #132, which asks whether some distance other than the diameter must occur at most n times. First, if no vertex of the convex hull has four points of X at distance Delta_2 (for instance, if no four points of X are concyclic), then mu(Delta_2) <= (3/2)|L_1| + |L_2|, where L_1, L_2 are the first two convex layers; so, under this hypothesis, the answer is yes whenever at least half as many points lie at depth >= 3 as on the hull. Second, for n points in convex position there are at least three distances occurring between 1 and n times when n is even and at least 6, and when n is 7, 9, 11 or 13. The cases n = 11, 13 are computer-assisted: they reduce to the unsatisfiability of finite ordinal problems, certified by DRAT/LRAT proof checkers and by a Lean 4 formalisation.
```

This abstract matches the paper's abstract except in three ways:
- It adds one sentence: "This theorem is formalised in Lean 4 with Mathlib."
- It drops the sentence "This rests on a layer bound…".
- It shortens the last clause.

Consider adding the Lean sentence to the paper's abstract too, so the two agree.

**Primary category:** math.CO (Combinatorics)
**Cross-list:** math.MG (Metric Geometry)

**Comments**
```
21 pages. The main theorem (54/37 bound) is formalised in Lean 4/Mathlib (sorry-free, standard axioms only); code, Lean files and certificates at https://github.com/<user>/erdos132-lean. An AI assistant (Claude, Anthropic) was used for exploration, computation, formalisation and drafting; see the AI disclosure in the paper.
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

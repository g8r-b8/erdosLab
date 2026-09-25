# Email drafts (DRAFT: do not send)

**Before sending:**
- Email (a) goes out *before* the arXiv submission: it attaches the PDF and asks for an arXiv endorsement. Get your endorsement code first by starting a math.CO submission on arXiv.
- Email (b) goes out after the forum post.
- Do the same-day re-check in `PREFLIGHT.md` first.

Fill in every `<…>` placeholder. Take recipient addresses from the authors' **own public pages** (links below). This file deliberately contains no addresses.

---

## (a) To Clemen, Dumitrescu and Liu

**Recipients.** The affiliations are as given on arXiv:2505.04283v5 and on the authors' public pages, checked 2026-09-23. Confirm them before sending.
- **Felix Christian Clemen**, PIMS Postdoctoral Fellow, University of Victoria. Public page: https://sites.google.com/view/felix-christian-clemen/
- **Adrian Dumitrescu**, Algoresearch L.L.C., Milwaukee, WI. Use the address on his arXiv papers or homepage.
- **Dingyuan Liu**, Karlsruhe Institute of Technology. Public pages: https://www.math.kit.edu/iag6/~d.liu/en and https://sites.google.com/view/liudyyy

**To:** `<Clemen address>`, `<Dumitrescu address>`, `<Liu address>`
**Subject:** An upper bound 4/3 for Problem 1.6 in "On multiplicities of interpoint distances"

> Dear Dr Clemen, Dr Dumitrescu and Mr Liu,
>
> I have been working on Problem 1.6 of your paper "On multiplicities of interpoint distances" (arXiv:2505.04283; Acta Math. Hungar. 2025). It asks for
> L = limsup_n max_{|X|=n} min{μ(Δ₂), μ(δ)}/n, and the known bounds were 9/7 ≤ L ≤ 3/2. The lower bound 9/7 is a construction posted by the user ienjoymath on the erdosproblems.com #132 forum thread; the upper bound is Vesztergombi's μ(Δ₂) ≤ 3n/2.
>
> I have written a paper proving that min{μ(Δ₂), μ(δ)} ≤ (4/3)n + C₀ for every n-point planar set, where C₀ is an absolute constant (not optimised). Hence L ≤ 4/3. In outline:
> - apply Vesztergombi's bound to the points having a Δ₂-partner, keeping track of those with only one partner;
> - show that almost all δ-edges among these points join points of the "Δ₂-boundary" with nearly equal normals, and that each extra ("rung") edge is paid for by a Δ₂-degree-1 endpoint or a missing tangential edge;
> - show that for the remaining points y, the δ-degree plus the number of δ-neighbours having a Δ₂-partner is at most 8 on average; the key step is that every locally extremal configuration pins Δ − Δ₂ to one of two short intervals.
>
> In terms of the scale-invariant quantity τ(X) = (Δ² − Δ₂² − δ²)/(2Δ₂δ), the same method gives (21/16)n + C₁ when τ(X) ≤ √3/2 − 0.02 or τ(X) ≥ √3/2 + 0.03, and a separate global argument gives (9/7)n + O(n^{2/3}) when τ(X) > 1. The last bound matches the lower bound 9/7 in that range, although the known 9/7 constructions have τ(X) → 0.
>
> A weaker bound, 15/11, obtained with pointwise estimates, is fully formalised in Lean 4 with Mathlib (no `sorry`, standard axioms only, including Vesztergombi's and Hopf–Pannwitz's bounds). The bounds 4/3, 21/16 and 9/7 are not formalised; a formalisation of 4/3 is in progress.
>
> To be clear about scope: this is an upper bound for your Problem 1.6 only. It does not decide whether L = 9/7, and it does not resolve Erdős Problem #132. The paper also has smaller results on #132:
> - a layer condition under which Δ₂ occurs at most n times;
> - for convex position, at least three distances of multiplicity in [1, n] for even n ≥ 6 and for 6 ≤ n ≤ 18 (n = 11, 13, 15, 17 computer-assisted);
> - for convex sets with all but w points on one circle, at least (n − 3w + 1)/4 such distances when n + w ≥ 91.
>
> The even case is a parity-sharp version of the argument in your Theorem 1.2.
>
> Preprint: attached (paper.pdf)
> Code, Lean files and certificates: https://github.com/g8r-b8/erdos132-lean
>
> I would be very grateful for any comments or corrections, and especially for pointers to related work I may have missed.
>
> I would also like to post the paper on arXiv (math.CO), and as a first-time submitter I need an endorsement. If one of you would be willing to endorse me, the endorsement code is <ENDORSEMENT CODE>, and it can be entered at https://arxiv.org/auth/endorse. An endorsement only confirms that the paper is appropriate for math.CO, not that it is correct. Of course, please don't feel any obligation.
>
> AI disclosure: I used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting; the paper describes the checks performed.
>
> With best regards,
> Wingate Jones

*Notes:*
- Keep the email short.
- **Endorsement:** arXiv issues the code when you start a submission from your account. Check that at least one of the three qualifies: on https://arxiv.org/abs/2505.04283, click "Which authors of this paper are endorsers?". If none does, remove that paragraph and ask someone else (e.g. Thomas Bloom).
- Attach `paper.pdf` (from the repo or `problems/132/paper/`).
- "Mr Liu": Dingyuan Liu is listed as a PhD student at KIT. If in doubt, use "Dear Felix Clemen, Adrian Dumitrescu and Dingyuan Liu".

---

## (b) To Thomas Bloom (erdosproblems.com)

**To:** `<contact address from https://www.erdosproblems.com (About/contact page)>`
**Subject:** Erdős Problem #132: forum post on CDL Problem 1.6 (bound 4/3)

> Dear Dr Bloom,
>
> I have posted a comment in the #132 forum thread: <link to forum comment>. It gives an upper bound (4/3)n + O(1) for min{μ(Δ₂), μ(δ)}, which is Problem 1.6 of Clemen–Dumitrescu–Liu, the extremal question discussed in that thread. This improves Vesztergombi's 3/2. The proof is in a preprint (<arXiv link>); a weaker bound, (15/11)n + O(1), is fully formalised in Lean 4/Mathlib, sorry-free with standard axioms only (<repository URL>). The 4/3 bound is not formalised; a formalisation is in progress.
>
> This is partial progress related to #132, not a solution of either question in #132. I mention it in case it is useful for the page's references or the formalisation status.
>
> AI disclosure: I used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting.
>
> Best wishes,
> Wingate Jones

*Notes:*
- Send this only after the forum post is live.
- Do not raise the prize here. Prize payment requires journal publication and goes through the Combinatorics Foundation, not the site (see `SUBMISSION_CHECKLIST.md`).

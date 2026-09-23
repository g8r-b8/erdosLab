# DRAFT: NOT POSTED. Do not post until SUBMISSION_CHECKLIST.md is complete.

> Draft comment for https://www.erdosproblems.com/forum/thread/132.
> Before posting, the person posting must have read and understood the proofs in the PDF and be able to
> vouch for them personally (site rule: the poster must understand and verify the mathematics, or supply a
> complete sorry-free Lean formalisation, which we do **not** have for the main theorem). Replace every
> `[PLACEHOLDER]`. Re-check the thread for new comments first (the last one we saw was ienjoymath, 25 Jul 2026).

---

**An upper bound 54/37 < 3/2 for Problem 1.6 of Clemen–Dumitrescu–Liu, plus two partial results on #132**

This is about the $\min\{\mu(\Delta_2),\mu(\delta)\}$ question of Clemen, Dumitrescu and Liu (arXiv:2505.04283,
Problem 1.6), which ienjoymath discussed above. Here $\mu(d)$ is the number of pairs at distance $d$, and $\Delta_2$,
$\delta$ are the second-largest and the minimum distance. The known bounds were $9/7 \le L \le 3/2$: the lower
bound is ienjoymath's construction, and the upper bound is Vesztergombi's $\mu(\Delta_2)\le 3n/2$.

**Main result.** Every $n$-point planar set satisfies $\min\{\mu(\Delta_2),\mu(\delta)\} \le \tfrac{54}{37}n + C_0$ for an absolute constant $C_0$. So $L \le 54/37 \approx 1.4595$.

Sketch:
- Let $S$ be the set of points with a $\Delta_2$-partner. Vesztergombi applied to $S$ gives $\mu(\Delta_2)\le\frac32|S|$, and $\mu(\delta)\le e_\delta(S) + 6(n-|S|)$. So any bound $e_\delta(S)\le k|S|+O(1)$ with $k<3/2$ beats $3/2$; $k=4/3$ gives $54/37$.
- Points of $S$ sit on the boundary of the ball polygon $\bigcap_{w}B(w,\Delta_2)$ or of the hull, and each has an inward normal. All but $O(1)$ of the $\delta$-edges inside $S$ join points with almost equal normals.
- Those edges are either tangential, or "rungs" whose geometry is fixed by an exact identity. An ownership/pairing count bounds rung density by $4/3$. The case $\Delta > 1.94\Delta_2$ is handled separately: there $\mu(\Delta_2)\le n+1$.
- The gap to $9/7$ remains open.

**Also in the note.**
1. *A new class of sets where the answer to the first question is yes.* Let $L_1, L_2$ be the first two convex layers and $m_3$ the number of deeper points. If no hull vertex has 4 points at distance $\Delta_2$ (e.g. no 4 concyclic points), then $\mu(\Delta_2)\le\frac32|L_1|+|L_2|$. So $\Delta$ and $\Delta_2$ both occur at most $n$ times whenever $|L_1|\le 2m_3$ (CDL's Thm 1.3 covers $|L_1|\le m_3$). The Vesztergombi structure facts this needs (degree 2 in the 2-core on $L_2$, degree $\le 4$ on $L_1$) are proved directly.
2. *Convex position, three rare distances.* For $n$ points in convex position, at least **three** distances occur between 1 and $n$ times:
   - for every even $n\ge 6$ (this is CDL's argument with a parity-sharp count; $n=6,8$ already follow from Erdős–Fishburn 1995);
   - for $n=7$ (also from the literature) and $n=9$ (from Erdős–Fishburn's nonagon classification);
   - for $n=11$ and $n=13$, which are new and computer-assisted. Only the ordinal quadrilateral inequality is used, in the spirit of Morić–Pritchard's abstract search. The SAT refutations are checked with drat-trim and lrat-check, and $n=7, 11$ are also proved in Lean 4 + Mathlib via `bv_decide`. The Lean proofs have no `sorry`, but they rely on the `bv_decide` native-evaluation axiom, and they are stated for vertices given as an ordered strictly convex polygon.

   $n=15$ is open (one SAT instance unresolved).

PDF: [PLACEHOLDER: PDF link] · Code, certificates scripts, Lean file: [PLACEHOLDER: repository link]

**AI disclosure.** I used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting; the checks performed are listed in the PDF's appendix. Comments and corrections are very welcome.

---

*Internal notes (delete before posting):*
- Do not claim the prize in the post. The prize needs journal publication (see SUBMISSION_CHECKLIST.md).
- Credit ienjoymath (9/7, and the announced LP note), CDL (Thm 1.2, 1.3, Problem 1.6), and Rafik/Marchetto/Beller for small $n$ where relevant.
- Keep the Lean caveats exactly as stated: ordered-polygon form only; `bv_decide` axiom (compiled-code trust, like `native_decide`); $n=13$ not in Lean. The main $54/37$ theorem is **not** formalised.

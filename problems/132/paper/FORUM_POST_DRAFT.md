# DRAFT: NOT POSTED. Do not post until SUBMISSION_CHECKLIST.md is complete.

> Draft comment for https://www.erdosproblems.com/forum/thread/132.
> Before posting, the person posting must have read and understood the proofs in the PDF and be able to
> vouch for them personally. Site rule: the poster must understand and verify the mathematics, or supply a
> complete sorry-free Lean formalisation. The main theorem now **has** such a formalisation, but a human
> still has to check that the Lean *statement* matches the theorem. Replace every `[PLACEHOLDER]`. Re-check
> the thread for new comments first; see `PREFLIGHT.md`. The last comment, as of 2026-09-23, was ienjoymath's
> on 25 Jul 2026.

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

**Lean formalisation.** The main theorem is fully formalised in Lean 4 + Mathlib:
```
theorem erdos132_main : ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
    (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 54/37 * X.card + C₀
```
- It has no `sorry`, and `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`: no `native_decide` or `bv_decide`.
- Vesztergombi's $\mu(\Delta_2)\le\frac32 n$ and Hopf–Pannwitz are proved in the development too, not assumed.
- The formal proof differs from the written one in three places, and the PDF's appendix describes them. In particular, the formal proof of the mixed-$T$ lemma gives a weaker constant, which only affects $C_0$.

**Also in the note.**
1. *A new class of sets where the answer to the first question is yes.* Let $L_1, L_2$ be the first two convex layers and $m_3$ the number of deeper points. If no hull vertex has 4 points at distance $\Delta_2$ (e.g. no 4 concyclic points), then $\mu(\Delta_2)\le\frac32|L_1|+|L_2|$. So $\Delta$ and $\Delta_2$ both occur at most $n$ times whenever $|L_1|\le 2m_3$ (CDL's Thm 1.3 covers $|L_1|\le m_3$). The Vesztergombi structure facts this needs (degree 2 in the 2-core on $L_2$, degree $\le 4$ on $L_1$) are proved directly.
2. *Convex position, three rare distances.* For $n$ points in convex position, at least **three** distances occur between 1 and $n$ times:
   - for every even $n\ge 6$ (this is CDL's argument with a parity-sharp count; $n=6,8$ already follow from Erdős–Fishburn 1995);
   - for $n=7$ (also from the literature) and $n=9$ (from Erdős–Fishburn's nonagon classification);
   - for $n=11$ and $n=13$, which are new and computer-assisted. Only the ordinal quadrilateral inequality is used, in the spirit of Morić–Pritchard's abstract search. The SAT refutations are checked with drat-trim and lrat-check, and $n=7, 11$ are also proved in Lean 4 + Mathlib via `bv_decide`. The Lean proofs have no `sorry`. They rely on the `bv_decide` native-evaluation axiom (unlike the main theorem), and they are proved both for ordered strictly convex polygons and for `Finset`s in convex position. $n=13$ is in Lean as well.

   $n=15$ is open (one SAT instance unresolved).

   The layer bound in item 1 is also formalised, with standard axioms only.

PDF / arXiv: [PLACEHOLDER: arXiv link] · Code, certificate scripts, Lean files: [PLACEHOLDER: repository link, e.g. https://github.com/<user>/erdos132-lean]

**AI disclosure.** I used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting; the checks performed are listed in the PDF's appendix. Comments and corrections are very welcome.

---

*Internal notes (delete before posting):*
- Do not claim the prize in the post. The prize needs journal publication (see SUBMISSION_CHECKLIST.md).
- Credit ienjoymath (9/7, and the announced LP note), CDL (Thm 1.2, 1.3, Problem 1.6), and Rafik/Marchetto/Beller for small $n$ where relevant.
- Keep the Lean caveats exactly as stated:
  - The main $54/37$ theorem **is** fully formalised: sorry-free, standard axioms only. See `problems/132/lean/README.md`.
  - The convex $n=7,11,13$ results use the `bv_decide` axiom, which means trusting compiled code, as with `native_decide`.
  - $n=9$ and even $n$ are not in Lean. They are hand or literature corollaries.
- Before posting, run `lean4checker` (or the comparator) on the main theorem and report the result in the post if it is clean. See `SUBMISSION_CHECKLIST.md`.
- Do not describe the result as solving #132. It is an upper bound for CDL Problem 1.6 plus partial results.

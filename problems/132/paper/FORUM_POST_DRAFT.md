# DRAFT: NOT POSTED. Do not post until SUBMISSION_CHECKLIST.md is complete.

> Draft comment for https://www.erdosproblems.com/forum/thread/132.
> Before posting, the person posting must have read and understood the proofs in the PDF and be able to
> vouch for them personally. Site rule: the poster must understand and verify the mathematics, or supply a
> complete sorry-free Lean formalisation. The main theorem now **has** such a formalisation, but a human
> still has to check that the Lean *statement* matches the theorem. Replace every `[PLACEHOLDER]`. Re-check
> the thread for new comments first; see `PREFLIGHT.md`. The last comment, as of 2026-09-23, was ienjoymath's
> on 25 Jul 2026.

---

**An upper bound 15/11 for Problem 1.6 of Clemen–Dumitrescu–Liu, plus partial results on #132**

This is about the $\min\{\mu(\Delta_2),\mu(\delta)\}$ question of Clemen, Dumitrescu and Liu (arXiv:2505.04283,
Problem 1.6), which ienjoymath discussed above. Here $\mu(d)$ is the number of pairs at distance $d$, and $\Delta_2$,
$\delta$ are the second-largest and the minimum distance. The known bounds were $9/7 \le L \le 3/2$: the lower
bound is ienjoymath's construction, and the upper bound is Vesztergombi's $\mu(\Delta_2)\le 3n/2$.

**Main result.** Every $n$-point planar set satisfies $\min\{\mu(\Delta_2),\mu(\delta)\} \le \tfrac{15}{11}n + C_0$ for an absolute constant $C_0$. So $L \le 15/11 \approx 1.3636$. In one regime of the proof (roughly: the diameter exceeds $\Delta_2$ by at least $(\tfrac{\sqrt3}{2}+0.03)\delta$, and $\Delta\le1.94\Delta_2$) the bound is $\tfrac43 n + C_0$.

Sketch:
- Let $S$ be the points with a $\Delta_2$-partner and $Q\subseteq S$ those with exactly one. Vesztergombi applied to $S\setminus Q$ gives $\mu(\Delta_2)\le\frac32|S|-\frac12|Q|$.
- Exactly, $\mu(\delta)=e_\delta(S)+\sum_{y\notin S}\frac12(\deg y+m_y)$, with $m_y$ the number of $\delta$-neighbours of $y$ in $S$.
- $e_\delta(S)\le|S|+|Q|+O(1)$: points of $S$ sit on the boundary of the ball polygon $\bigcap_w B(w,\Delta_2)$ or of the hull; almost all $\delta$-edges inside $S$ are tangential (at most $|S|$) or "rungs" between the two boundaries, and a corner lemma shows each rung is paid for either by a $\Delta_2$-degree-1 endpoint or by a missing tangential edge.
- $\deg y+m_y\le 10$ for all but $O(1)$ points $y\notin S$ (they lie inside the ball polygon; where its boundary is flat their $S$-neighbours fit in an open arc of $<240^\circ$), and $\le 8$ in the regime above.
- Weights $8/11$, $3/11$ give $15/11$. The gap to $9/7$ is the $\deg y+m_y\le10$ step, which is locally sharp for small excess.

**Lean formalisation.** The earlier, weaker bound $54/37$ (same set-up, a different count in two regimes and the trivial $\mu(\delta)\le e_\delta(S)+6(n-|S|)$) is fully formalised in Lean 4 + Mathlib:
```
theorem erdos132_main : ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
    (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 54/37 * X.card + C₀
```
- No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`. Vesztergombi's $\mu(\Delta_2)\le\frac32 n$ and Hopf–Pannwitz are proved in the development too.
- **The 15/11 bound is not formalised.** Its proof is in the PDF (checked in independent referee passes and by exact-arithmetic scripts).

**Also in the note.**
1. *Layer condition.* If no hull vertex has 4 points at distance $\Delta_2$ (e.g. no 4 concyclic points), then $\mu(\Delta_2)\le\frac32|L_1|+|L_2|$, so $\Delta$ and $\Delta_2$ are both rare whenever $|L_1|\le 2m_3$ (CDL's Thm 1.3 covers $|L_1|\le m_3$). Formalised in Lean, standard axioms only.
2. *Convex position, three rare distances* for every even $n\ge6$ and every $6\le n\le 18$. $n=11,13,15,17$ are new and computer-assisted: only the ordinal quadrilateral inequality is used; refutations are checked with drat-trim (and lrat-check for $n\le13$); $n=7,11,13$ are also proved in Lean 4 via `bv_decide` (which relies on its native-evaluation axiom). $n=15,17$ are not in Lean.
3. *Almost cocircular convex sets.* If all but $w$ of the points lie on one circle, $n\ge3w$ and $n+w\ge91$, there are at least $(n-3w+1)/4$ rare distances (Kneser's theorem plus Beukers–Smyth on torsion points). So the second question of #132 has a positive answer for convex sets with $w=o(n)$.
4. An exact 8-point set with $\mu(\Delta_2)=\mu(\Delta_3)=9$: "$\Delta_2$ or $\Delta_3$ is rare" is false; we ask whether $\min(\mu(\Delta_2),\mu(\Delta_3),\mu(\Delta_4))\le n$.

PDF / arXiv: [PLACEHOLDER: arXiv link] · Code, certificate scripts, Lean files: https://github.com/g8r-b8/erdos132-lean

**AI disclosure.** I used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting; the checks performed are listed in the PDF's appendix. Comments and corrections are very welcome.

---

*Internal notes (delete before posting):*
- Do not claim the prize in the post. The prize needs journal publication (see SUBMISSION_CHECKLIST.md).
- Credit ienjoymath (9/7, and the announced LP note), CDL (Thm 1.2, 1.3, Problem 1.6), and Rafik/Marchetto/Beller for small $n$ where relevant.
- Keep the Lean caveats exactly as stated:
  - The $54/37$ theorem **is** fully formalised: sorry-free, standard axioms only. See `problems/132/lean/README.md`. The $15/11$ headline is **not** formalised; say so explicitly.
  - The convex $n=7,11,13$ results use the `bv_decide` axiom, which means trusting compiled code, as with `native_decide`.
  - $n=9$, $n=15,17$ and even $n$ are not in Lean. $n=15,17$ are DRAT-certified only; $n=9$ and even $n$ are literature corollaries.
- Before posting, run `lean4checker` (or the comparator) on the main theorem and report the result in the post if it is clean. See `SUBMISSION_CHECKLIST.md`.
- Do not describe the result as solving #132. It is an upper bound for CDL Problem 1.6 plus partial results.

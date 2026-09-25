# Forum post draft for https://www.erdosproblems.com/forum/thread/132

> **Before posting** (checked 2026-09-25: no new comments since ienjoymath, 25 Jul 2026):
> 1. Push the public repo, so the 4/3 Lean files (E132Main43*) and paper v3 are on GitHub. The repo commit is being prepared.
> 2. Site rule: post only after (a) understanding and verifying the maths yourself, or (b) a sorry-free Lean formalisation.
>    Everything claimed **as proved** below is covered by (b). The unformalised results are only pointed to, as
>    "further results in the PDF, not formally verified". Don't upgrade that wording unless you have checked those
>    proofs yourself.
> 3. Delete this header. Everything between the two rules is the post.

---

**An upper bound 4/3 for Problem 1.6 of Clemen–Dumitrescu–Liu (Lean-verified), and partial results on #132**

This concerns the question of Clemen, Dumitrescu and Liu (arXiv:2505.04283, Problem 1.6) that ienjoymath discussed above: how large can $L=\limsup_n \max_{|X|=n}\min\{\mu(\Delta_2),\mu(\delta)\}/n$ be? Here $\mu(d)$ is the number of pairs at distance $d$, and $\Delta_2$, $\delta$ are the second-largest and the minimum distance. The known bounds were $9/7\le L\le 3/2$: the lower bound is ienjoymath's construction, and the upper bound is Vesztergombi's $\mu(\Delta_2)\le 3n/2$.

**Result.** For every finite planar set $X$ with $n\ge2$ points,
$$\min\{\mu(\Delta_2),\mu(\delta)\}\le \tfrac43\,n+C_0$$
for an absolute constant $C_0$. So $L\le 4/3$.

**Lean formalisation.** This is fully formalised in Lean 4 + Mathlib:
```
theorem Erdos132Main.erdos132_main43 : ∃ C₀, ∀ X : Finset Pt, 2 ≤ X.card →
    (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 4/3 * X.card + C₀
```
- It has no `sorry`, and `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
- All modules pass `leanchecker`. Vesztergombi's inequality and Hopf–Pannwitz are proved inside the development, not assumed.
- The definitions of `mult`, `dist2` and `minDist` are in `Erdos132/E132MainDefs.lean`, and the README gives the exact statement.
- The earlier bounds $15/11$ and $54/37$ are formalised in the same repository.

Idea of the proof:
- Let $S$ be the points with a $\Delta_2$-partner. Vesztergombi applied to $S$ controls $\mu(\Delta_2)$.
- The $\delta$-edges inside $S$ lie along the boundary of the ball polygon $\bigcap_w B(w,\Delta_2)$ or of the hull, apart from $O(1)$.
- For the points outside $S$, an exact identity reduces $\mu(\delta)$ to their average degree. That average is at most $8$, because the few local configurations with larger degree force $\Delta-\Delta_2$ into narrow ranges and can pass their excess to lighter neighbours.

**Also formalised (Lean, standard axioms only).** Suppose no hull vertex has 4 points at distance $\Delta_2$ (for example, no 4 concyclic points). Then $\mu(\Delta_2)\le\frac32|L_1|+|L_2|$, where $L_1,L_2$ are the first two convex layers. So $\Delta$ and $\Delta_2$ are both rare whenever $|L_1|\le 2m_3$, with $m_3$ the number of points of depth $\ge3$. This extends CDL's Theorem 1.3, which covers $|L_1|\le m_3$.

**Further results in the PDF (not formally verified).** The PDF also contains:
- sharper bounds for most parameter ranges;
- three rare distances for convex sets with $6\le n\le 18$ (SAT certificates);
- a linear number of rare distances for almost-cocircular convex sets;
- an exact 8-point set in which both $\Delta_2$ and $\Delta_3$ occur 9 times.

These results have not been formally verified.

PDF, Lean files and scripts: https://github.com/g8r-b8/erdos132-lean

**A question for the maintainers.** Has the prize for #132 ever been claimed? And would a result of this kind count as the "nontrivial result" the prize refers to? It is an upper bound for CDL's Problem 1.6 together with the layer condition, not a resolution of either question of #132.

**AI disclosure.** I used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting. Comments and corrections are very welcome.

---

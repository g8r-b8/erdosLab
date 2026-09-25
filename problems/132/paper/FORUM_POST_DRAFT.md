# DRAFT: NOT POSTED. Do not post until SUBMISSION_CHECKLIST.md is complete.

> Draft comment for https://www.erdosproblems.com/forum/thread/132.
> Before posting, the person posting must have read and understood the proofs in the PDF and be able to
> vouch for them personally. Site rule: the poster must understand and verify the mathematics, or supply a
> complete sorry-free Lean formalisation. The headline 4/3 bound does **not** have such a formalisation (only the
> weaker 15/11 and 54/37 bounds do), so the poster must understand and vouch for the 4/3 proof personally. Replace every `[PLACEHOLDER]`. Re-check
> the thread for new comments first; see `PREFLIGHT.md`. The last comment, as of 2026-09-23, was ienjoymath's
> on 25 Jul 2026.

---

**An upper bound 4/3 for Problem 1.6 of Clemen–Dumitrescu–Liu, plus partial results on #132**

This is about the $\min\{\mu(\Delta_2),\mu(\delta)\}$ question of Clemen, Dumitrescu and Liu (arXiv:2505.04283,
Problem 1.6), which ienjoymath discussed above. Here $\mu(d)$ is the number of pairs at distance $d$, and $\Delta_2$,
$\delta$ are the second-largest and the minimum distance. The known bounds were $9/7 \le L \le 3/2$: the lower
bound is ienjoymath's construction, and the upper bound is Vesztergombi's $\mu(\Delta_2)\le 3n/2$.

**Main result.** Every $n$-point planar set satisfies $\min\{\mu(\Delta_2),\mu(\delta)\} \le \tfrac43 n + C_0$ for an absolute constant $C_0$. So $L \le 4/3$. With $\tau(X)=(\Delta^2-\Delta_2^2-\delta^2)/(2\Delta_2\delta)$, the bound is $\tfrac{21}{16}n+C_1$ when $\tau(X)\le\sqrt3/2-0.02$ or $\tau(X)\ge\sqrt3/2+0.03$ (so everywhere except a narrow band around $\sqrt3/2$), and $\tfrac97 n+O(n^{2/3})$ when $\tau(X)>1$. The last bound matches ienjoymath's lower bound, in the sense that sets with $\tau(X)>1$ cannot beat $9/7$ (ienjoymath's construction has $\tau\to0$).

Sketch:
- Let $S$ be the points with a $\Delta_2$-partner and $Q\subseteq S$ those with exactly one. Vesztergombi applied to $S\setminus Q$ gives $\mu(\Delta_2)\le\frac32|S|-\frac12|Q|$.
- Exactly, $\mu(\delta)=e_\delta(S)+\sum_{y\notin S}\frac12(\deg y+m_y)$, with $m_y$ the number of $\delta$-neighbours of $y$ in $S$.
- $e_\delta(S)\le|S|+|Q|+O(1)$: points of $S$ sit on the boundary of the ball polygon $\bigcap_w B(w,\Delta_2)$ or of the hull; almost all $\delta$-edges inside $S$ are tangential (at most $|S|$) or "rungs" between the two boundaries, and a corner lemma shows each rung is paid for either by a $\Delta_2$-degree-1 endpoint or by a missing tangential edge.
- $\deg y+m_y\le 10$ for all but $O(1)$ points $y\notin S$, and **on average at most 8**. The points with $\deg y+m_y\ge9$ come in four local shapes. In each, a boundary neighbour and a diametral neighbour have a height difference that the exact identity $|z-w|=\Delta$ forces to equal $\Delta-\Delta_2$ up to $0.05\delta$; so these shapes need $\Delta-\Delta_2\in[0.75,0.95]\delta$ or $[0.44,0.56]\delta$. Each heavy point then passes its excess to one or two deeper neighbours that are light and not shared.
- Weights $2/3$, $1/3$ give $4/3$. With the $|Q|$ term, $4/3$ is also the limit of the linear combination; for $\tau\ge\sqrt3/2+0.03$ a sharper rung count halves it, which together with average weight 7 gives $21/16$ there. Only the band $\sqrt3/2-0.02<\tau<\sqrt3/2+0.03$ remains at $4/3$.
- For $\tau>1$, no $\delta$-edge joins the diametral points to the ball polygon, and a global Euler-formula argument (remove a shell at depth $\approx n^{1/3}$, then a winding-number argument) gives $\mu_\delta(\text{inside})\le 3|V|-2|S\cap\partial K|+O(n^{2/3})$, hence $9/7$.

**Lean formalisation.** The weaker bounds $15/11$ (`erdos132_main15`) and $54/37$ (`erdos132_main`) are fully formalised in Lean 4 + Mathlib:
```
theorem erdos132_main15 : ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
    (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 15/11 * X.card + C₀
```
- No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`, and the modules pass `leanchecker`. Vesztergombi's $\mu(\Delta_2)\le\frac32 n$ and Hopf–Pannwitz are proved in the development too.
- **The 4/3, 21/16 and 9/7 bounds are not formalised** (a formalisation of 4/3 is in progress). Their proofs are in the PDF; the new parts were checked in independent referee passes (two for the 4/3 step and for 21/16 in Region I, one for each of the two Region II inputs of 21/16, three for the $\tau>1$ argument) and the constants by exact-arithmetic scripts.

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
  - The $15/11$ and $54/37$ theorems **are** fully formalised: sorry-free, standard axioms only. See `problems/132/lean/README.md`. The $4/3$ headline (and $21/16$, $9/7$) is **not** formalised; say so explicitly. Never call the $\tau>1$ result "sharp": it matches the global lower bound, but the $9/7$ constructions have $\tau<1$.
  - The convex $n=7,11,13$ results use the `bv_decide` axiom, which means trusting compiled code, as with `native_decide`.
  - $n=9$, $n=15,17$ and even $n$ are not in Lean. $n=15,17$ are DRAT-certified only; $n=9$ and even $n$ are literature corollaries.
- Before posting, run `lean4checker` (or the comparator) on `erdos132_main15` and report the result in the post if it is clean. See `SUBMISSION_CHECKLIST.md`.
- Do not describe the result as solving #132. It is an upper bound for CDL Problem 1.6 plus partial results.

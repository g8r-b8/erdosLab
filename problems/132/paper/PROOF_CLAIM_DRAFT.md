# Proof-claim draft for https://www.erdosproblems.com/forum/thread/132/submit-proof

> **Before submitting:**
> 1. Push the public repo, so the 4/3 Lean files (E132Main43*) and paper v3 are on GitHub.
> 2. Only Lean-verified results are claimed here (site rule (b)). Unformalised results are pointed to as such.
> 3. Paste each field below into the matching box on the form.

---

## Type
Partial proof.

## Summary
We prove two partial results related to Erdős Problem #132.

(1) **Layer condition, on the first question.** Let $L_1, L_2$ be the first two convex layers of $A$ and $m_3$ the number of points of depth at least 3. If no vertex of the convex hull has four points of $A$ at the second-largest distance $\Delta_2$ (for example, if no four points are concyclic), then $\mu(\Delta_2)\le\frac32|L_1|+|L_2|$. So both the diameter and $\Delta_2$ occur at most $n$ times whenever $|L_1|\le 2m_3$. This extends Clemen–Dumitrescu–Liu's Theorem 1.3, which covers $|L_1|\le m_3$.

(2) **An upper bound of 4/3 for Clemen–Dumitrescu–Liu's Problem 1.6.** For every $n$-point planar set, $\min\{\mu(\Delta_2),\mu(\delta)\}\le\frac43 n+C_0$, where $\delta$ is the minimum distance. The previous bounds were $9/7\le L\le 3/2$: the lower bound is ienjoymath's construction in the comments, and the upper bound is Vesztergombi's.

Both are fully formalised in Lean 4 + Mathlib.

## Notes
- This is a partial result. Neither question of #132 is resolved in general. Result (2) is about a related question of Clemen, Dumitrescu and Liu (arXiv:2505.04283, Problem 1.6).
- **Formalisation.** The formalisation is unconditional. The main theorems are `Erdos132Main.erdos132_main43` (the $4/3$ bound; the earlier $15/11$ and $54/37$ bounds are also formalised) and the layer bound in `E132Layer.lean`. They have no `sorry`, and `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. The modules pass `leanchecker`. Vesztergombi's inequality $\mu(\Delta_2)\le\frac32 n$ and the Hopf–Pannwitz bound are proved inside the development, not assumed. The definitions of `mult`, `dist2` and `minDist` are in `Erdos132/E132MainDefs.lean`.
- **Further results in the PDF, not formally verified.** Sharper bounds for most parameter ranges; at least three rare distances for convex sets with $6\le n\le 18$ ($n=7,11,13$ are in Lean via `bv_decide`; $n=15,17$ rely on DRAT certificates); a linear number of rare distances for almost-cocircular convex sets; and an exact 8-point set in which $\Delta_2$ and $\Delta_3$ both occur 9 times.
- **Credit.** The $9/7$ lower bound is ienjoymath's (comments). The convex-position theorem and Problem 1.6 are from Clemen–Dumitrescu–Liu.
- **AI assistance.** I used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting.

## External link to proof
https://github.com/g8r-b8/erdos132-lean/blob/main/paper/paper.pdf

## External link to formalisation
https://github.com/g8r-b8/erdos132-lean/tree/main/Erdos132

---

# Direct message to the maintainers (Inbox), for the prize question

> Send after the proof claim is visible.

Subject: Erdős #132 prize

Hello,

I have submitted a partial proof claim for #132. It contains a layer condition under which the diameter and the second-largest distance both occur at most $n$ times, and an upper bound of $4/3$ for Clemen–Dumitrescu–Liu's related Problem 1.6. Both are fully formalised in Lean.

Could you tell me whether the $100 prize for #132 has ever been claimed? And would results of this kind count as the "nontrivial result" in [Er97e]? I understand the prize would require journal publication. I'm asking now so that I know whether it is worth pursuing.

Thank you,
Wingate Jones

(AI disclosure: I used an AI assistant for exploration, computation, formalisation and drafting.)

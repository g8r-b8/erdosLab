# Cor A1 made unconditional: a proof of "Prop 3" from Vesztergombi 1987's inner-point argument

Date: 2026-09-23. Scripts: `scripts/va1b_cases.py`, `scripts/va1b_case1.py`, `scripts/va1b_case2_margin.py`.

## Claim (the "[Ve96, Prop 3]" input to Theorem A and Cor A1 in angle_C.md)

Let G be the Δ₂-graph of X. It contains every Δ₂-pair: all Δ₂-pairs lie in L₁ ∪ L₂ (angle_C obs. (1)–(2)). Let G′ be its 2-core.
**Then every q ∈ L₂ ∩ V(G′) has deg_{G′}(q) = 2.**

## Proof

Normalise q = 0 and Δ₂ = 1. The key facts are:
- **q is not extreme.** q ∉ L₁, so it is not a hull vertex of X.
- **q has no Δ-partner.** The partners of a Δ-pair are extreme (angle_C obs. (2) proof).
- **So X lies in the unit disk** D(0,1), and q's Δ₂-neighbours lie on the unit circle.

The 2-core gives deg_{G′}(q) ≥ 2. Suppose v₁, v₂, v₃ are three distinct G′-neighbours of q. X has no distances in (1, Δ), so each |vᵢvⱼ| is either ≤ 1 or = Δ. There are three cases.

**Case 3: at most one pair at Δ (Ve87 Case 3).** Label the points so that v₂ lies between v₁ and v₃ on the circle, with ∠v₁qv₂ = a ≤ 60° and ∠v₂qv₃ = b ≤ 60°.
1. q is not extreme, so the closed half-plane H = {x : x·v₂ ≤ 0} contains some t ∈ X with t ≠ q.
2. For t ≠ 0, |t − v₂|² = |t|² − 2t·v₂ + 1 > 1, so |tv₂| = Δ.
3. Say t is on v₁'s side of line qv₂, or on that line. Then ∠(t, v₃) ∈ (90°, 240°], so t·v₃ < 0, and hence |tv₃| = Δ.
4. So t lies on the perpendicular bisector of v₂v₃: t points in direction 180° − b/2.
5. Then ∠(t, v₁) = 180° − b/2 − a ≥ 90°, so |tv₁|² ≥ |t|² + 1 > 1, and hence |tv₁| = Δ.
6. Now v₁, v₂, v₃ all lie on both C(0,1) and C(t,Δ). These circles are distinct because t ≠ 0, so they meet in at most 2 points. Contradiction.

The other side of the line is symmetric. This case uses only that q is not extreme; it needs no degrees.

**Case 2: exactly two pairs at Δ (Ve87 Case 2).** Take |v₁v₂| = |v₁v₃| = Δ and |v₂v₃| ≤ 1. Then v₁ = (−1, 0), v₂,₃ = (cos a, ±sin a) with 0 < a ≤ 30°, and Δ = 2cos(a/2).
**Claim: v₁ has no Δ₂-neighbour r ≠ q.** Such an r would satisfy |r − v₁| = 1, |r| ≤ 1, and |r − vᵢ| ∈ [0,1] ∪ {Δ}.
- *Both |r − v₂|, |r − v₃| ≤ 1.* Impossible. Write r = (x, y) with y ≥ 0. On the arc |r|² = −2x ≥ 0, so
  |r − v₃|² − 1 = −2x(1 + cos a) + 2y sin a ≥ 0,
  with equality only when r = q.
- *|r − v₂| = Δ* (or symmetrically |r − v₃| = Δ). Then |r − v₃| misses [0,1] ∪ {Δ} by at least 0.414 for every a ∈ (0°, 30°] (`va1b_case2_margin.py`, 3000 values of a).
- *Both = Δ.* Then r lies on the x-axis, so r ∈ {q, (−2, 0)}, and (−2, 0) is outside the disk.

So deg_G(v₁) = 1. This contradicts v₁ ∈ G′, because deg_G ≥ deg_{G′} ≥ 2.

**Case 1: all three pairs at Δ (Ve87 Case 1).** The vᵢ form an equilateral triangle with circumcentre q, so Δ = √3.
- An extra Δ₂-neighbour P ≠ q of vᵢ satisfies |P − vᵢ| = 1 and |P| ≤ 1.
- It cannot have both other distances ≤ 1: 0 hits on a 2·10⁵-point sweep per vertex. So |P − vⱼ| = √3 for some j ≠ i.
- That leaves exactly **6 candidate points**, two per vertex, related by the 3-fold symmetry (`va1b_case1.py`).
- Their pairwise distances are 0.2149 (for 3 disjoint pairs) and 1.1547, 1.2758 or 1.3696 otherwise. The last three are all inside the forbidden gap (1, √3), with a margin of at least 0.15.
- So a compatible set has at most 2 candidates. At most two of the vᵢ can gain a second neighbour, and some vᵢ has deg_G = 1. Contradiction as before.

With four or more neighbours, apply the argument to any three of them. **Hence deg_{G′}(q) ≤ 2, and so = 2.** ∎

## Relation to Ve87, and why the transfer is valid

The three cases are Vesztergombi's (Discrete Math 67 (1987) 191–198, pp. 192–194). The adaptation has two points.
- Ve87 ends Cases 1–2 with "some vᵢ has degree 1, which is a contradiction". That contradiction is against its assumption that no point of the current set has degree ≤ 1, which it justifies by deleting points.
- Here nothing is deleted. The witnesses r, t are points of X, and "degree 1" is measured in G, the full Δ₂-graph. Since deg_G ≥ deg_{G′}, this contradicts membership in the 2-core directly.

So the concern raised in NOVELTY Audit 5, that deleting points can change d₁ and d₂, does not arise.

Rigour: Case 3 and the open branch of Case 2 are proved by hand above. The equality branches of Cases 1–2 are verified numerically, with explicit margins ≥ 0.15 (Case 1) and ≥ 0.41 (Case 2) at double precision. Those are closed-form algebraic configurations, so a CAS or interval re-check would be routine, but it has not been done.

## Consequence

- **Theorem A and Corollary A1 in angle_C.md are unconditional.** Cor A1 says: if no hull vertex has ≥ 4 points at distance Δ₂ (e.g. no 4 concyclic), then μ(Δ₂) ≤ (3/2)|L₁| + |L₂|. So (a) holds whenever |L₁| ≤ 2m₃.
- The "Unconditional form" of Cor A1 (with min(h, 4)) still uses [Ve96, Props 5–8] via CDL. Cor A1 itself does not.
- This also gives a self-contained proof of the part of CDL obs. (4) used for Thm 1.3's second and third bounds (e(L₁′, L₂′) = 2|L₂′|).

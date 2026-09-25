# Route A report: an elementary proof of `core` (Theorem E′, Steps 2–7) by a visible-path argument

Agent: Route A research agent (scripts `l97A_vp_*`).  Date 2026-09-25.  Written proof not refereed.

This is a separate file because `RouteA_report.md` already held another Route A agent's outline (commit 8c2b4e5, "steep-chain decomposition"), and this agent did not overwrite it.

## Verdict

**An elementary proof has been found.** It is not refereed. It proves `core` with a *linear* error:

  **Def(G[Yout]) ≥ 2|A| − E_A(h),  E_A(h) := 71h + 7**  (h = ρ + ½, h < Δ₂/200, |A| > 1000h).

Since 71h + 7 ≤ 1764h² + 223h + 4, this implies the plan's `core` statement (`Eh`) as it stands.

The proof does not use:
- faces or Euler's formula;
- the Jordan curve theorem or (P6);
- winding numbers or Lemma W;
- perimeter, or arc length of general curves;
- the case split (i)/(ii) of §5.2;
- the laminarity count of Step 6.

The only lengths it uses are those of circular arcs, defined as radius × angle.

The paper's global ingredients are replaced by one finite object and three facts about it:
- the object is the **visible path** of the drawing, seen from the inner parallel body K′ along the outward normal rays of K′;
- a **telescoping turning identity**: the relative angle between the path direction and the ray direction is a canonical real lift, and this is what replaces the winding number;
- a **local wedge lemma**;
- a **counting lemma** comparing visible pieces with A-points.

The error is O(h) instead of O(h²), because every normal ray is counted once. This removes the corner multiplicity of Step 6.

Side remark (not checked further): with E = O(h), the shell pigeonhole of Step 0 can be rebalanced. That would give Theorem E′, and hence the τ > 1 theorem, with error O(√n) instead of O(n^{2/3}).

Everything was tested adversarially at 40 digits (mpmath) on 400 random configurations and on the L/M obstruction families; see §4. Angles make exact rational arithmetic impossible for the geometric lemmas. The constants were checked with Fractions (`l97A_vp_constants.py`).

## 1. Setting

- δ = 1, and G is the unit-distance graph.
- H := G[Yout] with isolated vertices removed. An isolated vertex contributes exactly 3 ≥ 2 to Def, so this is harmless: if the bound holds for the rest, it holds for H_out.
- Def(H) = 3V − E = Σ_v (3 − deg v/2).
- h = ρ + ½. Vertices of H have depth < ρ, so every point of the drawing 𝒟 (vertices and edges) has depth < h.
- K′ := {depth ≥ h} = ∩_{w∈X} D(w, R′), with R′ := Δ₂ − h. So 𝒟 ∩ K′ = ∅.
- A = Y ∩ ∂K, and each a ∈ A lies on some C(w, Δ₂). Put n_a := (a − w)/Δ₂. By the chord inequality, every neighbour k of a satisfies (k − a)·n_a < 0.

**Lemma 0 (int K′ ≠ ∅).** Under |A| > 1000h, some point has depth > h. The paper uses Steinhagen and perimeter here; this proof uses neither.

Proof.
1. Suppose instead that every point has depth ≤ h. Let o be a point of maximal depth r ≤ h, and call w *active* if |o − w| = Δ₂ − r. Put u_w := (o − w)/|o − w|.
2. **0 ∈ conv{u_w : w active}.** Otherwise some d has u_w·d < 0 for every active w. Then depth(o + εd) > r for small ε, a contradiction.
3. By Carathéodory in the plane, 0 lies in the convex hull of two antipodal normals or of three normals.
4. D(w, Δ₂) ⊂ {x : (x − o)·u_w ≤ r}. So K lies in a strip of width 2r, or in a triangle with inradius r. The smallest altitude of such a triangle is r(a + b + c)/max side ≤ 3r.
5. So K lies in a strip of width w ≤ 3h. Lemma F, steps 1–9 (chord inequality only), gives diam K ≤ 100w ≤ 300h.
6. **ℓ¹ chain count.** ∂K is the union of an upper concave graph and a lower convex graph over the strip axis. On each graph, the A-points sorted by abscissa have Σ|Δx| ≤ 300h and Σ|Δy| ≤ 2w. Consecutive points are ≥ 1 apart, and |Δx| + |Δy| ≥ 1. So |A| ≤ 2(300h + 6h + 1) < 1000h, a contradiction. ∎

## 2. The proof

### Step 1 — normal coordinates of K′ (elementary convex geometry of an intersection of discs)

(N1) ∂K′ consists of finitely many arcs of circles C(w, R′) and finitely many corners c.
- K′ is strictly convex, so each unit vector ν has a unique support point y(ν) ∈ ∂K′.
- On the normal range of an arc of C(w, R′), y(ν) = w + R′ν.
- A corner c has normal cone N(c) = [ν₁, ν₂], with ν_i = (c − w_i)/R′ for two centres w_i. Its angle ψ_c satisfies sin(ψ_c/2) = |w₁ − w₂|/(2R′) ≤ 0.97·200/199 = 194/199.
- Normal cones of distinct corners have disjoint interiors, so Σ_c ψ_c ≤ 2π.

(N2) Rays r_ν := {y(ν) + tν : t > 0} are pairwise disjoint and cover ℝ² ∖ K′.
- For x ∉ K′ write x = y(ν(x)) + t(x)·ν(x). Then y(ν(x)) = P(x), the nearest point of K′.

(N3) **Local polar structure.** Near any ray, the rays on each side are half-lines through a *pole* on the line of that ray, behind y(ν):
- the pole is w (at distance R′ + t) on an arc range;
- the pole is c on a corner range.

(N4) On a segment σ ⊂ ℝ² ∖ K′ that does not lie on a ray line, ν is continuous and strictly monotone, and ν(σ) is an arc of length < π.
- Orient σ so that ν increases, and let d be its direction.
- Then **ψ := arg d − ν ∈ (0, π)** along σ.
- Moving along σ, ψ decreases exactly as fast as ν increases (d is constant).

(N5) Each ray leaves K at a single exit point e(ν) ∈ ∂K.
- On an arc range, e(ν) = y(ν) + hν ∈ C(w, Δ₂) (offset point). There ν is the normal of K at e(ν).
- On N(c), e(ν) runs over the **collapse arc** Z_c = ∂K ∩ (c + N(c)).
- Every a ∈ A lies on the ray r_{ν(a)} and equals e(ν(a)).
- For a ∉ ∪Z_c, n_a = ν(a).
- For a ∈ Z_c, both n_a and ν(a) lie in N(c), so the angle α_a between them satisfies |α_a| ≤ ψ_c.

(N6) **Collapse length.** len Z_c ≤ κhψ_c with κ = 199/√1965 < 4.49. Here len Z_c := Σ Δ₂·(normal angle) over the K-arcs of Z_c.

Proof.
1. Let H(φ) := (x(φ) − c)·e^{iφ}, where x(φ) ∈ Z_c is the point with K-normal φ, and let G(φ) := (x(φ) − c)·ie^{iφ}.
2. On an arc of C(w, Δ₂) with normals [a, b] one checks explicitly that Δ₂(b − a) = ∫_a^b H + [G]_a^b.
3. At a K-corner, 0 = ∫H + [G].
4. G is continuous along Z_c and vanishes at both ends p_i = c + hν_i.
5. So len Z_c = ∫_{N(c)} H ≤ ψ_c·max_{Z_c}|x − c|.
6. Z_c lies in the kite with vertices c, p₁, T, p₂, bounded by the tangent lines at p_i and the cone. This is the paper's Step 3 containment, without P4. So |x − c| ≤ |T − c| = h/cos(ψ_c/2) ≤ κh. ∎

Hence **Σ_c len Z_c ≤ 2πκh < 28.22h**.

### Step 2 — the visible path (a finite combinatorial object)

Let Φ := {ν(v) : v vertex} = {ν₁ < … < ν_M} (cyclic), and I_i := (ν_i, ν_{i+1}).

(V1) On I_i the set of edges meeting r_ν is constant, and so is their order along the ray.
- An edge meets r_ν iff ν ∈ its ν-arc, whose ends lie in Φ.
- Two edges that swapped order would share a non-vertex point. That is impossible: unit edges do not cross (P1), and no vertex lies inside a unit edge.
- Hence there is a **first-hit edge e_i**, or e_i = ∅. An interval with e_i = ∅ is an *escape interval*. Its measure counts in |E|, and J := #{i : e_i = ∅}.

(V2) At ν_i, let B_i be the first point of 𝒟 on r_{ν_i}, and let L_i := e_{i−1} ∩ r_{ν_i}, R_i := e_i ∩ r_{ν_i}.
- The path at ν_i is L_i → B_i → R_i, the steps being radial jumps. Repeated points are merged.
- Relative angles ψ: on pieces, ψ is as in (N4); an inward jump has ψ = π; an outward jump has ψ = 0.
- **Virtual ends:** if e_{i−1} = ∅, the path "arrives" with ψ = π; if e_i = ∅, it "leaves" with ψ = 0.
- The turning at a corner is κ := ψ_out − ψ_in ∈ [−π, π].

(V3) **Structure of the corners.**
1. If B_i is not a vertex, then B_i = L_i = R_i. Its edge crosses the ray transversally, so it is also the first hit on both sides, and κ = 0.
2. So every corner that is not a vertex (a *foot*) is L_i ≠ B_i, with κ = π − ψ_in > 0, or R_i ≠ B_i, with κ = ψ_out > 0. **Feet have κ > 0.**
3. If e_{i−1} ≠ e_i (or the path dips to a nearer vertex), then L_i or R_i is a vertex, or L_i = R_i is a shared vertex. If both were interior points of their edges, each edge would lie below the other on one side (V1), which is impossible.
4. At the end of an escape interval, B_i is a vertex. Otherwise its edge would be hit inside the escape interval.

(V4) **Counting.**
- A vertex lies on exactly one ray, so it is a corner at most once. Let m be the number of vertex corners.
- A *piece* is a maximal run of intervals with the same edge traversed without a corner. Let n be the number of pieces.
- By (V3), every boundary between pieces, and both ends of every hit arc, carry a vertex corner. So **m ≥ n + J** if J ≥ 1, and m ≥ n if J = 0.

### Step 3 — turning identity (telescoping; replaces Umlaufsatz and winding numbers)

  **Σ_{all corners} κ = Σ_{i: e_i≠∅} |I_i| − πJ** (= 2π when J = 0).

Proof.
1. Inside the corner sequence at ν_i, the κ's telescope to ψ_out(last) − ψ_in(first).
2. If e_i ≠ ∅, then ψ_out(last at ν_i) − ψ_in(first at ν_{i+1}) = ψ_{e_i}(ν_i) − ψ_{e_i}(ν_{i+1}) = |I_i|, by (N4).
3. If e_i = ∅, the same difference is 0 − π = −π. Sum over i. ∎

Since feet have κ > 0: **Σ_{vertex corners} κ_v ≤ 2π − |E| − πJ** (≤ 2π if J = 0).

No topology is involved. The relative angle ψ ∈ [0, π] is a canonical lift, which is exactly what the paper's winding-number argument needed.

### Step 4 — wedge lemma (local)

At a vertex corner v (ν₀ = ν(v)), let W_v be the open arc of directions counter-clockwise from ν₀ + ψ_out to ν₀ + ψ_in + π. Its length is π − κ_v.

**Claim.** For every d ∈ W_v and every small s > 0, the point v + sd lies on a ray r_ν strictly between y(ν) and the first hit of r_ν, or on an escaping ray. In particular, no edge of v points into W_v.

Proof.
1. Use polar coordinates about the pole on the relevant side (N3), with the pole at distance D behind v on the line of r_{ν₀}.
2. A half-line from v with relative angle ψ ∈ (0, π) meets the pole ray at polar angle δ at distance D sin ψ / sin(ψ − δ) from the pole. This is decreasing in ψ.
3. So directions beyond ψ_out (toward −ν₀) give points nearer than the path, and the same holds on the other side of −ν₀ with ψ_in.
4. If the outgoing step is an outward jump (ψ_out = 0), the path on that side is farther out still.
5. The ray segment strictly below v is free, because v is the first hit, or lies below a jump.
6. On a virtual side, all rays escape. ∎

### Step 5 — per-vertex counting (replaces the angle sum of faces)

Neighbours of v are pairwise ≥ 60° apart. Suppose there are k pairwise disjoint open arcs of directions, of lengths λ_j, containing no neighbour.
- A closed arc of length μ holds ≤ 3μ/π + 1 neighbours, so deg v ≤ 3(2π − Σλ_j)/π + k.
- Hence **3 − deg v/2 ≥ (3/2π)·Σ_j (λ_j − π/3)**. This also holds for deg 0.

For a ∈ A, the closed half-plane of directions H⁺_a = {d·n_a ≥ 0} (length π) is free.

### Step 6 — combining at each vertex

- **v ∉ A, corner:** Def_v ≥ (3/2π)(2π/3 − κ_v).
- **a ∈ A, not a corner:** Def_a ≥ 1.
- **a ∈ A, corner, both path directions real:**
  - An A-point is the farthest point of its ray inside K. So the path passes a by pieces, or by one piece and one inward jump (−ν(a), with ν(a)·n_a > 0).
  - Both bounding directions of W_a therefore lie in the open inner half-plane of n_a.
  - W_a cannot contain n_a: by Step 4, a + s·n_a would lie in K, but it lies outside D(w, Δ₂).
  - So W_a ∩ H⁺_a = ∅. Step 5 applies with W_a and H⁺_a, as two free arcs or one free arc of length ≥ π + |W_a|, and gives Def_a ≥ 1 + (3/2π)(2π/3 − κ_a).
- **a ∈ A, endpoint of a hit arc (virtual side):** W_a ∪ H⁺_a is one free arc, so Def_a ≥ 1 + (3/2π)(2π/3 − κ_a) − (3/2π)|W_a ∩ H⁺_a|.
  - |W_a ∩ H⁺_a| ≤ π/2 + |α_a|, because the free part toward the virtual side starts at the ray direction ν(a).
  - A one-ray hit arc counts as two endpoints.

### Step 7 — summation (the main inequality, MI)

Sum over all vertices, using Step 3 and #(A-endpoints) ≤ 2J:

  Def(H) ≥ |A| + (3/2π)[(2π/3)m − Σ_v κ_v] − (3/2π)Σ_{A-endpoints}|W∩H⁺|
      ≥ |A| + m − 3 + (3/2π)|E| + (3/2)J − (3/4)·2J − (3/2π)Σ_{endpoints}|α_a|
      ≥ **|A| + m − 3 − (3/2π)Σ_{endpoints}|α_a|**.

- α_a ≠ 0 only for a ∈ Z_c. There |α_a| ≤ ψ_c and #(A ∩ Z_c) ≤ 1 + len Z_c.
- So (3/2π)Σ|α_a| ≤ (3/2π)Σ_c ψ_c(1 + κhψ_c) ≤ 3 + 6θ*κh < 3 + 36.3h, where θ* = arcsin(194/199) < 1.347.

### Step 8 — counting A against pieces (CL), and assembly

1. **Every A-point lies on a hit ray**, since a itself is a drawing point on r_{ν(a)}. So A is covered by the hit arcs I_j, and the pieces tile each I_j.
2. Define μ_K(I) := Δ₂·|I ∩ arc-ranges| + Σ_c len(e(I ∩ N(c))). This is the length of ∂K swept by the rays of I, as a sum of circular arcs.
3. Consecutive A-points are ≥ 1 apart, and chord ≤ Σ sub-chords ≤ Σ arcs. So #(A on rays of a closed interval I) ≤ μ_K(I) + 1 (≤ μ_K(S¹) when J = 0).
4. **Per piece** (length ≤ 1): on each arc-range subrange [a, b] the rays are radial from w at radius ≥ R′, so the sub-segment has length ≥ 2R′ sin((b − a)/2). Hence Δ₂(b − a) ≤ (Δ₂/R′)(1 + R′⁻²)·|sub-segment|, using y/sin y ≤ 1 + y² for y ≤ 1. So μ_K(piece) ≤ 1 + ε′ + col(piece), with ε′ := (h + Δ₂/R′²)/R′.
5. Summing: **|A| ≤ n + J + ε′·min(n, |A|) + 28.22h**. The min comes from: if n ≥ |A| there is nothing to prove.
6. Also |A| ≤ μ_K(S¹) ≤ 2πΔ₂ + 28.22h, so ε′|A| ≤ 6.46h + 0.03.

**Assembly:** m ≥ n + J ≥ |A| − 34.7h − 0.03. With Step 7:

  **Def(H_out) ≥ 2|A| − 70.96h − 6.03 ≥ 2|A| − (71h + 7).** ∎

The constants are verified exactly (Fractions) in `l97A_vp_constants.py`.

## 3. Formalisation friendliness (Lean infrastructure per step)

| step | content | Lean needs | estimate |
|---|---|---|---|
| Lemma 0 | max-depth point, active normals, Carathéodory-2D, strip, ℓ¹ chain count | compactness (`IsCompact.exists_isMaxOn`), first-order depth increase, finite separation in ℝ²; Lemma F steps 1–9 (chord inequality, in repo style) | 600–900 lines |
| N1–N6 | normal coordinates of ∩ D(w, R′): support point, arcs/corners, poles, ν-monotonicity on segments, exit point, collapse length | nearest point (`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`), `Complex.arg`/angles, sin/cos inequalities, one interval integral of cos/sin (or MVT) for N6 | 1500–2500 lines; the heaviest part |
| V1–V4 | finite event list (sort Φ), first-hit edge, corner classification | `Finset.sort`, P1 non-crossing (already elementary), continuity of hit parameter along an edge | 800–1200 lines |
| Step 3 | telescoping | `Finset.sum_range_sub`-style cyclic telescoping | < 150 lines once V is set up |
| Step 4 | wedge lemma | sine rule monotonicity, local polar coordinates | 400–700 lines |
| Step 5 | points on a circle with 60° separation vs free arcs | angular counting (the `dirMeasure` style of E132ConvexCurve.lean fits well) | 300–500 lines |
| Steps 6–8 | per-vertex bookkeeping, μ_K additivity, chord ≤ arc, assembly | Finset sums, `Real.sin_le`, `Real.sin_lt`, arcsin bounds | 800–1200 lines |

Total: roughly **4.5–7k lines**. This compares with ≥ 10k lines for Route B (polygonal Jordan + Euler with faces + winding numbers). No Mathlib gaps are *structural*: everything is finite sums, inequalities about sin/cos/arg, and the nearest-point map.

Suggested simplifications for Lean:
- Parametrise rays by the normal angle ν ∈ ℝ/2πℤ, avoiding the path as a curve. The "visible path" is just the finite data (Φ, e_i, L_i, B_i, R_i, ψ's).
- Prove Step 3 as a pure identity about that data, and Steps 4–6 as per-vertex inequalities.
- The main risk is (N3)/(N4): monotonicity of ν along a segment, and the pole description at arc/corner boundaries.

## 4. Tests (scripts `problems/132/scripts/l97A_vp_*.py`, run with `.venv/bin/python`)

**`l97A_vp_common.py`** is the harness (mpmath, dps 40, tolerance 1e-25).
- It builds K = ∩D(w, Δ₂), K′ = ∩D(w, Δ₂ − h), the unit graph, the normal coordinates, the finite event structure, and the visible path (L → B → R, virtual ends).
- It checks:
  - (W) the wedge lemma at every vertex corner;
  - ψ ∈ (0, π) on pieces;
  - feet κ > 0;
  - (T) the turning identity;
  - (O) A-neighbours in the open inner half-plane;
  - the per-vertex claims of Step 6, including the endpoint overlap;
  - (MI) the main inequality;
  - (CL) |A| − (n + J);
  - (E) Def ≥ 2|A| − (35h + 4). This is *stronger* than the proved 71h + 7, and was used as a stress level.

**`l97A_vp_random.py N seed`** runs random adversarial configurations.
- K is a disc, a lens (two centres at distance 0.3–1.2Δ₂), or a three-disc intersection.
- Δ₂ ∈ {25, 40, 60, 90} and ρ ∈ {1, 2, 3}.
- A-chains on ∂K: closed rings, open arcs, several arcs. Chords are 1 with probability 0.3–1, otherwise 1 + U(0, 0.05–0.9). A-points are also placed exactly at the corners of K (collapse zones).
- Greedy unit-distance apex growth inside the band, with pendant edges and isolated points.
- Results: 40 trials (seed 1) and 400 trials (seed 2) all pass.
  - Turning identity error < 1e-38.
  - Zero wedge, ψ, feet or per-vertex failures.
  - Worst MI slack about 2.4 (seed 1).
  - Seed 2 (400 trials): worst MI slack 1.11, minimum Def − 2|A| = 1, minimum Def/|A| = 2.083, max |A| − (n + J) = 0.
  - The endpoint-overlap excess |W∩H⁺| − π/2 reached 0.476 > 0. This occurs at A-points in collapse zones, so the |α_a| term of Step 6 is genuinely needed. The per-vertex claim with that term never failed.

**`l97A_vp_families.py`** runs the known obstruction families and dense strips.
- The L family of `r6_gap_L_family.py` (k = 1..6, R = 50, 200; 10 periods).
- M pair-gap rows (`r6_gap_M_pairgap.py` construction), 10 pairs and an almost-closed ring (184 or 938 pairs at R = 60 or 300), one and two layers.
- Dense saturated strips hugging ∂K (disc and lens, closed and open, ρ = 1, 2).
- Results: all pass.
  - Minimum Def − 2|A| = 12.
  - Minimum Def/|A| = 2.5008 (M ring, R = 300).
  - |A| − (n + J) ≤ −1 always.
- In the M ring, A-points are exactly the visible-piece count plus one (m = |A| + 1). The CL step is essentially tight there, and the ½ per A-point is paid exactly by the visible (inner) side, as the intuition says.

**`l97A_vp_constants.py`** runs the exact Fraction checks of E_A(h) ≤ 71h + 7, of 1/cos(θ*) < 4.49, of arcsin(194/199) < 1.347 (Taylor lower bound for sin), of 71h + 7 ≤ E(h), and of the Lemma 0 count.

Local obstructions from §5.5 (L: loses 1 per T-path locally; M: loses |A|/4 locally): the visible-path argument pays these globally. The inner side of the strip is counted once per ray, and neither family comes close to violating MI.

## 5. What remains / caveats

- The written proof is new and unrefereed. The steps that most need a referee are:
  - (N3)/(N4) at arc/corner boundaries;
  - Step 6, the direction set argument that W_a ∩ H⁺_a = ∅ for interior A-corners;
  - the endpoint overlap bound |W ∩ H⁺| ≤ π/2 + |α|.

  All three are checked numerically on every corner of every test configuration (per-vertex check `pv_fail = 0`).
- The numerical tests are 40-digit floating point with 1e-25 tolerances, not exact arithmetic (angles are transcendental). The constants are exact.
- Degenerate coincidences (several vertices on one ray, radial edges) are handled in the proof. They occur in the L/M families (symmetric constructions) and pass.

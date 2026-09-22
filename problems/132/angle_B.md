# Erdős #132, angle B: convex position, number of "rare" distances

Notation: P is a set of n points in strictly convex position, N = C(n,2). For a distance d, m(d) is its multiplicity.
d is *rare* if 1 ≤ m(d) ≤ n. k(P) is the number of rare distances and D(P) the number of distinct distances.
Goal: k(P) → ∞, ideally k(P) ≥ cn.

Scripts in this directory: `search.py` (local search over lattice and cyclotomic pools), `capq.py`, `caplemma.py`
(Cap Lemma interval check), `circinc.py` (circle incidences for R_N), `thmE.py` (sanity check), `mk.py`.

## 1. Counting lemma (exact; the reduction the brief asked me to check)

**Lemma 1.** For any n-point set: k ≥ (D(n+1) − N)/n. For P convex this gives **k ≥ D − ⌊n/2⌋ + 1**.

*Proof.* The frequent distances each have m ≥ n+1 and the rare ones have m ≥ 1, so (D−k)(n+1) + k ≤ N.
- For n = 2m+1, N = mn, so kn ≥ n(D−m) + D and k ≥ D − m + D/n.
- For n = 2m, N = mn − m, so kn ≥ n(D−m) + D + m.

In both cases k ≥ D − m + 1. ∎

So if k(P) ≤ K, then D(P) ≤ ⌊n/2⌋ + K − 1. **A counterexample family must be Altman-near-extremal.** Altman's bound
(D ≥ ⌊n/2⌋) combined with Lemma 1 gives only k ≥ 1. Clemen–Dumitrescu–Liu need Fishburn's classification to get the
second rare distance. The threshold n is exactly critical: in R_n with n odd, every class has multiplicity exactly n.

**Corollary 1 (slack versions, trivial but new as statements?).** For P convex:
- (a) For λ > 1, at least ⌊n/2⌋ − (n−1)/(2λ) distances occur at most λn times. That is linear in n, e.g.
  ≥ n/4 − O(1) distances occur ≤ 2n times.
- (b) For 0 ≤ C ≪ n, at least ⌊n/2⌋ − ⌊n(n−1)/(2(n+C+1))⌋ ≈ (C+1)/2 distances occur ≤ n + C times.

So any additive slack C above n already forces ~C/2 such distances. Only the exact threshold n needs structure.

## 2. Cases where everything is rare

**Prop 2.** If every G_d (the graph of pairs at distance d) has maximum degree ≤ 2, then m(d) ≤ n for all d, so
k = D ≥ ⌊n/2⌋. This holds in particular for **cocircular** P, because a circle about p ∈ Γ meets Γ in ≤ 2 points.
It also holds for any P in which no point is equidistant from 3 others.

Also: subsets of R_N have every class of size |S ∩ (S+j)| ≤ |S| (a special case).

## 3. Cap Lemma and "regular polygon plus t points" (new, proved)

Let A be the vertex set of a regular a-gon on the unit circle, with θ = π/a. Its chords are
c_j = 2 sin(jθ), 1 ≤ j ≤ ⌊a/2⌋, strictly increasing.

**Cap Lemma.** Let a ≥ 6, and let q be a point with A ∪ {q} in strictly convex position. If |q − x| = c_j for some
x ∈ A, then c_j = c_⌊a/2⌋ (a odd), or c_j ∈ {c_{a/2−1}, c_{a/2}} (a even).

*Proof.*
1. Strict convexity forces q into the open "cap" triangle Δ = (x_0, x_1, z) beyond one edge x_0x_1. It must be
   beyond exactly one edge line. Here z is where lines x_{−1}x_0 and x_1x_2 meet: z = R e^{iθ} with
   R = cos θ / cos 2θ (a ≥ 5).
2. For fixed x, the values |q − x| over open Δ form an open interval (lo, hi). hi is the max over the three
   vertices; this is strict by strict convexity of the norm.
3. **Lower bound.** For x = x_{−j} with 1 ≤ j ≤ a/2 − 1, both boundary rays of Δ at x_0 make an angle ≥ 90° with
   x_0 → x. The angles are (a−j−1)θ and π − (j−1)θ. Hence |q−x|² ≥ |x_0−x|² + |q−x_0|², so lo > c_j.
4. **Upper bound.** |z − x_{−j}| ≤ c_{j+1} is equivalent (after trig identities; worked in the notes) to
   sin 3θ ≤ 2 sin((2j+3)θ) cos 2θ.
   - This holds for 1 ≤ j ≤ (a−6)/2, because sin((2j+3)θ) ≥ sin 3θ and 2cos 2θ ≥ 1 when a ≥ 6.
   - For odd a and j = (a−5)/2, it becomes sin 3θ ≤ sin 4θ, which holds for a ≥ 7.
   - So for these j, |q − x_{−j}| ∈ (c_j, c_{j+1}), which contains no chord.
5. **Remaining vertices.**
   - For j = (a−3)/2 (odd a) and j = (a−4)/2, (a−2)/2 (even a), step 3 leaves only the top one or two chords.
   - For the antipodal vertex (odd a), |q−x| ≥ 1 + cos θ > 2cos(3θ/2) = c_{(a−3)/2}.
   - For x_0 and x_1, |q − x_0| < max(c_1, |x_0 z|) = c_1, since |x_0z| = c_1 / (2cos 2θ) ≤ c_1 for a ≥ 6.
   - The other side follows by reflection symmetry. ∎

a = 5 is a genuine exception: q can be at distance equal to a side from x_0. `caplemma.py` confirms the statement
for 6 ≤ a < 600 with exact interval checks.

**Theorem E.** Let P be convex with n points and contain the vertices of a regular a-gon, a ≥ 6, and let
t = n − a ≥ 1. Then **k(P) ≥ (n − 2t − 1)/2 = a − (n+1)/2.**

*Proof.* Take the "safe" chord classes of A: (a−3)/2 of them if a is odd, a/2 − 2 if a is even. For such a class,
e_A = a (at most a suffices). By the Cap Lemma e_{A,T} = 0, so m = a + e_T(d). This is ≤ n unless e_T(d) ≥ t+1.
Since Σ_d e_T(d) ≤ C(t,2), fewer than (t−1)/2 safe classes fail. The diameter of P is rare by Hopf–Pannowitz and
exceeds every safe chord, so it adds 1. ∎

**Corollary E.** A convex n-set that contains a regular a-gon with a ≥ n/2 + K + 1 has ≥ K rare distances.

## 4. Conditional route to k → ∞, and the correct stability statement

By Lemma 1 it suffices to show that convex sets with D ≤ ⌊n/2⌋ + K have ≥ K+1 rare distances.

The naive stability statement "D ≤ n/2 + K ⇒ P contains a regular (n − f(K))-gon" is **false**. R_{n+2} minus two
vertices has D ≤ ⌊n/2⌋ + 1, but its largest regular sub-polygon has ≤ (n+2)/2 vertices.

The plausible version is:

**Stability Conjecture S.** D ≤ ⌊n/2⌋ + K ⇒ |P ∩ V(R_N)| ≥ n − f(K) for some regular N-gon with N ≤ n + f(K).
Fishburn proved it for K = 0.

**S together with an extension of the Cap Lemma** to A ⊂ V(R_N) with ≤ f missing vertices would give
k ≥ n/2 − O_K(1). The extension needs: a point q ∉ V(R_N) lying in a cap of such an A hits (is at chord distance
from) O(1) vertices. Numerics (`circinc.py`, all circle-circle intersection points of R_N with |q| ∈ [0.9, 1.1],
N ≤ 30) give max ≤ 3 hits. Far from the circle, special cyclotomic points hit many (13 for N = 60), but they
cannot be in convex position. Both S and the extended lemma are **open gaps**.

## 5. Negative / sanity findings

- max_i |p_i p_{i+k}| is NOT increasing in k in general. It failed in ~50% of random convex polygons, so it is not
  a route to Altman.
- The minimum distance can occur n+1 times in convex position: a 60° rhombus plus a chain of unit sides. So
  "diameter + min distance" does not give 2 rare distances.
- The quadrilateral inequality gives strict concavity of S_k = Σ_i |p_i p_{i+k}| (anti-Monge), and the star-polygon
  identity Σ_i ∠(p_{i−j} p_i p_{i+j}) = (n−2j)π. These are candidate tools for S, not yet used.
- Energy and isosceles counting cannot work alone. R_n (odd n) makes every numerical inequality tight, so any proof
  must use rigidity.
- Local search over triangular, square-lattice and cyclotomic pools (n ≤ 12) found no convex set with any frequent
  distance: every optimum had k = D. Such sets are far from Altman-extremal, since D ≫ n/2.

## 6. Literature / novelty

- CDL (arXiv 2505.04283, Acta Math. Hungar. 2025) prove only k ≥ 2 (Thm 1.2). Their open problems do not include
  k → ∞ for convex sets.
- The forum thread 132 (5 comments up to Jul 2026) covers small n (7–13) and the (9/7)n construction only.
- Related work searched: Altman 1963/1972; Fishburn 1995 (D = ⌊n/2⌋ classification) plus "Convex nonagons with
  five intervertex distances" (n = 9 only); ELV conjecture Σ_{i≤k} m_i ≤ kn (arXiv 1103.0412); Aggarwal on
  isosceles triangles (1009.2218); Nivasch–Pach–Pinchasi–Zerbib (1207.1266).
- I found no stability theorem for Altman beyond Fishburn and no prior "regular polygon + t points" result.
  Theorem E and the Cap Lemma appear new, though elementary.

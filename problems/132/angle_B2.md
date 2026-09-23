# Erdős #132, angle B2: stability of Altman at K = 1, and "k ≥ 3" for convex sets

(2026-09-23. Continues `angle_B.md`. Notation: P ⊂ R² is a strictly convex n-set, m = ⌊n/2⌋, N = C(n,2),
D = D(P) is the number of distinct distances, D = m + K. For a distance d, μ(d) is its multiplicity.
d is *rare* if 1 ≤ μ(d) ≤ n and *frequent* if μ(d) ≥ n+1. k = k(P) = #rare and F = #frequent, so k + F = D.
R_N is the regular N-gon and R_N^- is R_N with one vertex removed.)

## 0. Summary

| # | Statement | Status |
|---|---|---|
| 1 | Parity-sharp counting: odd n gives k ≥ K+1; even n gives k ≥ K+2 when K ≥ 1 (improves `angle_B` Lemma 1 by one for even n) | **proved** |
| 2 | **Theorem A.** Every convex n-set with n ≥ 6 even has k ≥ 3. For even n ≥ 8, k ≤ 3 forces D = m+1. | **proved** (uses Fishburn 1995 as a black box) |
| 3 | **Theorem B.** Every convex 9-set has k ≥ 3. | **proved** (uses Erdős–Fishburn 1996 as a black box) |
| 4 | Odd n = 2m+1: k ≤ 2 ⇔ (D, k, F) = (m+1, 2, m−1). Every frequent class then has multiplicity 2m+2+e_d, and the identity a + b + Σe_d = m+2 holds, where a and b are the two rare multiplicities. | **proved** |
| 5 | Structure of a hypothetical odd counterexample. C1: no vertex deletion lowers D (no class is a star). C2: no 2 vertices cover both rare classes. C3: no 3 vertices cover both rare classes. C4: every diameter is near-halving. C5: no "fans". | C1, C2, C4, C5 **proved** (m ≥ 4); C3 (m ≥ 6) **conditional** on AE′(6) |
| 6 | **Lemma K** (cocircular stability via Kneser): a set on a circle with \|A\| = q and D ≤ q/2 + K′, where q > 4K′+2, is a vertex subset of some R_N with N ≤ q+2K′+1 | **proved** |
| 7 | **Theorem D.** S1(c) + AE′(h) imply k ≥ 3 for all odd n > n₀(c,h). Hence, with Theorem A, k ≥ 3 for all convex n ≥ n₀. | **conditional** |
| 8 | Conjecture S1: odd K=1 sets are cocircular up to O(1) points. Conjecture AE′: extended Cap Lemma for gapped R_N. Conjecture OS: the one-sided (half-polygon) version. | open; numerical evidence in §6 |
| 9 | Non-cocircular even K=1 example: the subdivided Reuleaux pentagon, n = 10, D = 6. So cocircularity fails for even n at least sporadically. | **new observation** |

**Net effect on #132 (b) for convex sets.** For even n ≥ 6 and for n = 9, there are always at least three distances
occurring at most n times. For odd n ∉ {5, 9}, the missing case is exactly: a convex (2m+1)-gon with m+1 distances,
m−1 of which occur more than n times. Odd n = 5 genuinely fails: R_5 has k = 2.

## 1. Counting lemma, parity-sharp

(D − k)(n+1) + k ≤ N gives k ≥ (D(n+1) − N)/n.
- n = 2m+1, D = m+K: k ≥ K + (m+K)/(2m+1), so **k ≥ K+1** for 1 ≤ K ≤ m+1.
- n = 2m, D = m+K: k ≥ K + 1 + K/(2m), so **k ≥ K+2** for 1 ≤ K < 2m.

`scripts/counting_parity.py` checks the closed forms for n < 400.
`angle_B`'s "k ≥ D − m + 1" is therefore lossy by one for even n. That one unit is what Theorem A uses.

## 2. Theorem A (even n)

**Theorem A.** P convex, |P| = n = 2m ≥ 6. Then k(P) ≥ 3. If n ≥ 8 and k(P) ≤ 3, then D(P) = m+1.

*Proof.*
- Altman gives D ≥ m.
- If D ≥ m+1, §1 gives k ≥ 3. If D ≥ m+2, it gives k ≥ 4.
- If D = m, Fishburn (Comput. Geom. 5 (1995) 65–93; statement as quoted in CDL §2) applies:
  - n = 6: the profile is (6,6,3) or (5,5,5), so k = 3.
  - n ≥ 8: P = R_n with profile (n,…,n,n/2), or P = R_{n+1}^- with profile (n−1,…,n−1). In both cases k = m ≥ 4. ∎

So for even n the whole difficulty is K = 1, i.e. D = m+1, and even there counting already gives k ≥ 3.

## 3. Odd n: reduction, n = 9, and small cases

**Prop B (reduction).** Let n = 2m+1 ≥ 7, P convex, k(P) ≤ 2. Then:
- D = m+1 and k = 2, so F = m−1 frequent classes.
- Writing μ(d) = 2m+2+e_d for frequent d, and a (the diameter) and b for the two rare multiplicities,
  **a + b + Σ e_d = m + 2** exactly.

*Proof.*
- D = m gives R_n (Altman), which has k = m ≥ 3.
- D ≥ m+2 gives k ≥ 3 by §1.
- D = m+1 gives k ≥ 2. Then summing multiplicities: (m−1)(2m+2) + Σe + a + b = m(2m+1). ∎

Every frequent class has average degree above 2, so each of the m−1 frequent graphs G_d has a vertex with 3 vertices at
distance d from it.

**Theorem B.** Every convex 9-gon has k ≥ 3.

*Proof.* Erdős–Fishburn, "Convex nonagons with five intervertex distances", Geom. Dedicata 60 (1996) 317–332: a
convex 9-gon has exactly 5 distances iff it is 9 vertices of R_10 or R_11. Cocircular sets have every class of max
degree ≤ 2, so k = D = 5. D = 4 gives R_9 with k = 4, and D ≥ 6 gives k ≥ 3 by §1. ∎

**Small n.**
- n = 5: R_5 has k = 2, so "k ≥ 3" needs n ≥ 6.
- n = 7: open. Only 7-point convex 4-distance sets with two classes of size ≥ 8 need excluding. The numerical search
  (§6) finds only R_8^- and R_9 minus 2 vertices, all cocircular with k = 4.

## 4. Structure of a hypothetical odd counterexample (n = 2m+1, D = m+1, F = m−1)

Throughout, P is as in Prop B and Δ, ρ are the rare distances.
Cap Lemma (from `angle_B`): if a ≥ 6 and q is in convex position with R_a, then q is at chord distance from R_a only
for the top chord (a odd) or the top two chords (a even).

**C1 (no star).** For m ≥ 4, D(P − v) = m+1 for every vertex v. Equivalently, no distance class of P is a star; in
particular a, b ≥ 2.

*Proof.* Suppose D(P − v) = m. By Fishburn, P − v = R_{2m} or R_{2m+1}^-.
- *Case R_{2m} ∪ {v}:*
  - Every value that is not a chord has all its pairs at v, hence ≤ 2 pairs (circle–circle; v is not the centre).
  - By the Cap Lemma (a = 2m ≥ 8), v adds pairs only to c_{m−1} and c_m.
  - c_j for j ≤ m−2 keeps 2m < 2m+2 pairs, and c_m gets ≤ m+2 pairs.
  - So F ≤ 1 < m−1.
- *Case R_{2m+1}^- ∪ {v}:*
  - Chord classes have 2m−1 pairs, so a frequent class needs 3 pairs at v.
  - Three concyclic points equidistant from v force v to be the centre. The centre is inside the hull, so this is
    impossible. Hence F = 0. ∎

**C2 (no 2-cover).** For m ≥ 4, no two vertices u, v meet every Δ-pair and every ρ-pair.

*Proof.*
- Otherwise P − {u,v} has only the m−1 frequent distances on 2m−1 points. Altman's odd equality case then gives
  P − {u,v} = R_{2m−1}.
- A chord class c_j has 2m−1 pairs and needs 3 more.
- By the Cap Lemma (a = 2m−1 ≥ 7, odd), u and v are at chord distance only for c_{m−1}. So c_j with j ≤ m−2 gets at
  most the single pair uv.
- Non-chord values have ≤ 5 pairs.
- So F ≤ 1. ∎

**C3 (no 3-cover), conditional.** For m ≥ 6, assuming AE′(6) for one-hole polygons R_{2m−1}^- (numerically true for 2m−1 ≤ 59), no three vertices W cover both rare
classes.

*Proof.* P − W has D ≤ m−1 on 2m−2 points, so by Fishburn it is R_{2m−2} or R_{2m−1}^-.
- *Base R_{2m−2}:*
  - c_j with j ≤ m−3 has 2m−2 pairs and needs 4 more, but can get only the ≤ 3 W–W pairs (Cap Lemma).
  - Non-chord values have ≤ 9 pairs.
  - So F ≤ 2 < m−1.
- *Base R_{2m−1}^-:*
  - If the missing vertex is in W, then P ⊇ R_{2m−1} plus 2 points, and C2's argument gives F ≤ 1.
  - Otherwise each chord class has 2m−3 base pairs, so a frequent class needs ≥ 5 pairs touching W.
    Non-chord values have ≤ 9 pairs, so all m−1 frequent classes are chord classes.
  - There are only 3 W–W pairs in total, so Σ over frequent classes of W–base chord pairs ≥ 5(m−1) − 3.
  - AE′ bounds that sum by 3h. So 5(m−1) − 3 ≤ 3h, i.e. m ≤ 1 + (3h+3)/5 = 5.2 for h = 6. This is a contradiction
    for m ≥ 6. ∎

**C4 (diameters near-halving).** This is Altman 1972, Cor. (7), with his Theorem 2 (Canad. Math. Bull. 15 (1972)
329–340; reconstructed in §7). Let AB be any diameter and r the number of vertices strictly on the larger side. Then:
- D ≥ r.
- D ≥ r+1 unless both A and B have a second diameter partner on that side.

Since r + r′ = 2m−1, we get **r ∈ {m, m+1}** for every diameter. If r = m+1, both A and B have degree ≥ 2 in the
diameter graph.

**C5 (no fans).** Suppose the closed larger side of a diameter AB is a "fan", i.e. all its points are at distance
|AB| from A. Then a ≥ m+1, so b ≤ 1, contradicting C1.

These constraints are strong but do not by themselves contradict the configuration. The rare classes have ≤ m+2
pairs in total, are not stars, and have joint vertex-cover number ≥ 3 (≥ 4 given C3).

## 5. Stability program and the conditional theorem

### 5.1 Cocircular stability is Kneser (proved)

**Lemma K.** Let A lie on a circle, |A| = q, D(A) ≤ q/2 + K′, and q > 4K′ + 2. Then A ⊆ V(R_N) for a regular
N-gon on that circle with q ≤ N ≤ q + 2K′ + 1.

*Proof.*
1. Identify the circle with T = R/2πZ. A chord determines a difference up to sign, so |A − A| ≤ 2D + 1 ≤ q + 2K′ + 1.
2. Kneser's theorem in the abelian group T: with H = Stab(A − A), which is finite and equal to μ_N,
   |A − A| ≥ 2|A + H| − |H|.
3. Write |A + H| = tN.
   - H trivial gives q ≤ 2K′ + 2.
   - t ≥ 2 gives (3/2)q ≤ (2t−1)N ≤ q + 2K′ + 1, i.e. q ≤ 4K′ + 2.
4. So t = 1, i.e. A lies in one coset of μ_N. ∎

For K = 1 odd (q = n, K′ = 1/2), a cocircular P is a vertex subset of R_{n+1} or R_{n+2}. N = n is ruled out because it
gives D = m. So Lemma K classifies the *cocircular* part of K = 1 completely; S1 is exactly the missing non-cocircular
part.

### 5.2 Conjectures

**S1(c).** For n ≥ n₀, every convex n-set with D ≤ ⌊n/2⌋+1 has all but ≤ c points on one circle.
- Erdős–Fishburn proved c = 0 for n = 9.
- **Caveat (new):** the subdivided Reuleaux pentagon (5 vertices plus the 5 arc midpoints) is convex, n = 10,
  D = 6 = n/2 + 1, and it is not cocircular: it lies on 2 concentric circles, 5 + 5 (`scripts/reuleaux.py`).
  So for even n, S1 needs sporadic exceptions. It is harmless for k, since every class there is ≤ n and k = 6.
- Subdivided Reuleaux polygons with t = 2 have K = k_R − 1, where the Reuleaux polygon has 2k_R+1 vertices (so K
  grows with k_R). For t = 3, K grows too. So they are not a family counterexample.

**AE′(h) (extended Cap Lemma).** Let A ⊆ V(R_N) with |V(R_N) \ A| ≤ g, and let u lie off the circle with A ∪ {u}
strictly convex. Then u is at a chord distance of R_N from at most h(g) points of A.
- The previous agent's `circinc.py` is the special case g = 0 near the circle.
- Numerics (`aecheck.py`, `aecheck2.py`) enumerate all pairwise circle intersections, which are the only candidates
  with ≥ 2 hits. For N ≤ 60 and ≤ 5 holes in any local pattern, max hits = 6 (at N = 24). The max is 2 for most N.

### 5.3 Theorem D (conditional)

**Theorem D.** Assume S1(c) and AE′(h). Then every convex (2m+1)-set with m > 1 + h + c/2 + O(1) has k ≥ 3.
Combined with Theorem A: k ≥ 3 for all convex n ≥ n₀(c, h).

*Proof.*
1. Take P as in Prop B, so F = m−1. Let C = P ∩ Γ with |C| = 2m+1−w, w ≤ c, and W = P \ C.
2. D(C) ≤ m+1, so by Lemma K, C ⊆ V(R_N) with N ≤ 2m+3. For large m the centre of Γ lies inside conv(C), since
   the holes are few.
3. A non-chord value has all its pairs touching W: ≤ 2 to C per u ∈ W, plus W–W pairs, so ≤ 2w + C(w,2) < 2m+2
   pairs. Hence it is rare, and all m−1 frequent classes are chord classes.
4. Inside C each class has max degree ≤ 2, hence ≤ |C| pairs. So each frequent class needs ≥ w+1 pairs touching W.
5. By AE′, the W–C pairs at chord distance number ≤ wh in total. W–W pairs number ≤ C(w,2).
6. So (m−1)(w+1) ≤ wh + C(w,2), false for m − 1 > h + w/2.
7. If w = 0, P is cocircular and k = D = m+1 ≥ 3. ∎

The counting in steps 4–6 even tolerates w up to ≈ (2−ε)m. The real bottleneck is that AE′ needs C to be nearly all
of R_N.

### 5.4 One-sided version (OS) and why S1 is plausible

Altman's proof lives on *one side of a diameter*.

**Setting.** Q = (B_0, …, B_{r+1}) is convex and B_0B_{r+1} = diam Q. Then D(Q) ≥ r (Altman). In our situation
r ∈ {m, m+1} and D(Q) ≤ m+1 ≤ r+1, so the larger side of every diameter is one-sided-extremal with slack ≤ 1.

**What we can prove.**
- If Q is cocircular with span ≤ π, the classical |X − X|₊ ≥ |X| − 1 (equality iff X is an arithmetic
  progression) shows Q is a regular arc.
- Beyond π, folding gives a subset of an arithmetic progression with ≤ 1 hole.

**Numerics** (`fewdist_search.py … os`, q = r+2 ≤ 10). Slack-1 one-sided configurations found:
- regular arcs;
- cocircular sets folding at > π;
- **fans**: B_0 is the centre of a regular arc through B_1…B_{r+1} with span ≤ 60°, a continuous family, D = r+1.
  The 60° fan is tight, D = r;
- sporadic small cases (q ≤ 7): a fan plus one point, and 7-point sub-chains of the subdivided Reuleaux triangle
  (t = 3) and pentagon (t = 2).

**Conjecture OS.** For r ≥ r₀, D(Q) ≤ r+1 implies that Q is cocircular or a fan.

OS ⇒ (larger side of each diameter is cocircular, fans being excluded by C5) ⇒ S1, provided the small side can be
attached. Attaching it needs an "arc version" of AE′: a point in convex position with a long regular arc that sees
all of it at chord distances lies on the circle.

A useful identity for that: if u sees the consecutive arc points e^{i(j−1)θ}, e^{ijθ}, e^{i(j+1)θ} at chords of
orders k_{j−1}, k_j, k_{j+1}, then

 cos k_{j+1}θ + cos k_{j−1}θ − cos(k_j+1)θ − cos(k_j−1)θ = −(|u|²−1)(1−cos θ),

which is constant in j. So u is on the circle iff this constant vanishes. A Conway–Jones/Lam–Leung analysis of this
4-term relation, repeated over ≥ m consecutive j, looks like the right tool; I did not finish it.

## 6. Numerics (all scripts in `scripts/`)

- `altman_lemma1.py`:
  - Altman's Lemma 1 (|B_sB_v| > min(|B_sB_t|, |B_uB_v|) for s<u, t<v) holds including diameter endpoints: 139,243
    random tests, 0 violations.
  - The variant with s = u is **false** (triangle counterexample), so "consecutive" must mean strict in both indices.
- `pyramid_enum.py`: the *ordinal* content of Lemma 1 does not force constant rows, even in the tight case. For
  r = 3..6 there are 3, 32, 1289 and 205052 ordinal solutions, all but one non-row-constant. Any stability proof must
  use metric rigidity.
- `fewdist_search.py` (DP partition plus least squares, random restarts; *not exhaustive*):
  - n = 7, D = 4 (3000 plus 4000 restarts): only R_8^- (6,6,6,3) and R_9 minus 2 vertices, two gap types. All
    cocircular with k = 4.
  - n = 9, D = 5 (3000 restarts): only R_10^- and R_11 minus 2. This agrees with Erdős–Fishburn, but the search found
    only one of the R_11 gap types, so coverage is incomplete.
  - n = 11, D = 6 (partial run, stopped early): only R_12^- (10,…,10,5) and R_13 minus 2 found. All cocircular with
    k = 6.
  - One-sided runs (q = 6..10, D = q−1 or q−2, partial): every solution was cocircular, a fan, or one of the
    sporadic q ≤ 7 types listed in §5.4. The q = 7 "OTHER" hits were a near-degenerate artefact and the
    Reuleaux-chain type.
- `aecheck.py`, `aecheck2.py`: AE′ max hits ≤ 6 for N ≤ 60 with ≤ 5 holes. The pattern is 2 for most N; larger values
  (3–6) occur for N divisible by 6 or 4 (N = 12, 14, 18, 20, 24, 28, 30, 36, 42).
- `reuleaux.py`: D for subdivided Reuleaux polygons, including the n = 10, D = 6 non-cocircular example.
- `counting_parity.py`: §1 closed forms, plus the multiplicity profiles of R_n, R_{n+1}^- and R_{n+2} minus 2 for
  n ≤ 13.

## 7. Altman 1972, reconstructed (for later work)

Source: E. Altman, *Some theorems on convex polygons*, Canad. Math. Bull. 15 (1972) 329–340. The PDF text was
extracted this session.

**Theorem 1.** Let u_j = Σ_i |A_iA_{i+j}|. Then u_1 < u_2 < … < u_{⌊n/2⌋}, and 2u_k > u_{k+1} + u_{k−1}. The proof is
the quadrilateral inequality summed over i.

**Setup.** Let A_1A_n be a maximal diagonal of the sub-polygon cut off on one side. Its "parallels" are the other
chords, and chords (s,t), (u,v) are *consecutive* if s < u and t < v.

**Lemma 1 (referee's proof via a support line parallel to A_sA_v).** One of two consecutive parallels is shorter than
A_sA_v.

**Theorem 2.** Take a chain of f consecutive interior parallels whose smallest member has degree x (d_1 > d_2 > … are
the distinct lengths). Then f ≤ x − 2 if the diameter is unique in the sub-polygon, and f ≤ x − 1 otherwise. The proof
is by induction via the inscribed chain (s_i, t_{i+1}). f = x − 1 needs another diameter from each endpoint.

**Theorem 3 (D ≥ ⌊n/2⌋).**
- Apply the Corollary to the chain of interior sides on the larger side.
- In case (b) at a common endpoint, choose between the two diameters from that endpoint to get r ≥ ⌊n/2⌋.

## 8. Gaps / next steps

1. **Main gap: S1 (or OS) for large n.** Everything for odd n ≥ 11 (and n = 7) reduces to it. A proof must use metric
   rigidity (§6, pyramid enumeration), and must allow fans and sporadic Reuleaux-type pieces at small r.
2. **AE′** for all N. Candidate route: vanishing sums of roots of unity (Conway–Jones), via the identity in §5.4.
3. **n = 7** could be settled by exact computation: classify 7-point convex 4-distance sets.
4. **Novelty.** Theorem A is a 5-line consequence of Fishburn 1995 plus parity-sharp counting. I found no statement of
   it in CDL (who prove k ≥ 2 only), the forum thread, or the literature scanned in `frontier.md`. That is a quick
   check only, not an audit per PROMPT rule 4.
5. Even n, k ≥ 4 for large n: this needs even K=1 stability, and the n = 10 Reuleaux example shows even K=1 is
   genuinely richer.

# Erdős #132: frontier map (audit date 2026-09-22)

**Problem** (erdosproblems.com/132, status OPEN, $100). Let A ⊂ R², |A| = n. (a) Must there be **two** distances that each occur at least once and at most n times? (b) Must the number of such distances go to infinity? Maybe it is ≥ n^{1−o(1)}.
Erdős offers $100 for "any nontrivial result" [Er97e, *Some of my favourite unsolved problems*, Math. Japon. 1997]. The diameter is always one such distance (Hopf–Pannwitz), so (a) is the same as CDL Conjecture 1.1: "for n ≥ 5, not every non-diameter distance occurs more than n times". For n = 4 it fails: the rhombus made of two equilateral triangles has multiplicities (5,1).

Notation: μ(d) is the multiplicity of distance d, D is the number of distinct distances, Δ > Δ₂ > … > δ are the distances in decreasing order, L₁ and L₂ are the first and second convex layers, and s(A) = #{d : 1 ≤ μ(d) ≤ n}.

## 1. What is proved

| Result | Conditions | Source |
|---|---|---|
| μ(Δ) ≤ n | all planar sets | Hopf–Pannwitz 1934 (Jber. DMV 43, Aufgabe 167) |
| (a) holds | n = 5, 6 | Erdős–Fishburn, *Multiplicities of interpoint distances in finite planar sets*, DAM 60 (1995) 141–147 |
| (a) holds | A in convex position, n ≥ 5 | CDL Thm 1.2 |
| μ(Δ₂) ≤ n (so (a) holds) | min{3/2(\|L₁\|+\|L₂\|), 4/3\|L₁\|+2\|L₂\|, 2\|L₁\|+\|L₂\|} ≤ n | CDL Thm 1.3 |
| μ(Δ₂) ≤ n | Δ/δ ≤ n/(3π) | CDL Cor 1.4 |
| (a) holds | n = 7..13 (n = 11, 12 conditional on Wei's classification of 11-point 5-distance sets, Ars Combin. 102 (2011)) | forum comments + code, not refereed (see §2) |

CDL is Clemen–Dumitrescu–Liu, *On multiplicities of interpoint distances*, arXiv:2505.04283 (v5, 3 Feb 2026), Acta Math. Hungar. 177 (2025) 231–245. https://arxiv.org/abs/2505.04283

**CDL Theorem 1.2 (convex): the whole proof.** Altman: a convex n-set has D ≥ ⌊n/2⌋. If D > ⌊n/2⌋ and every non-diameter distance has μ ≥ n+1, then ⌊n/2⌋(n+1)+1 > C(n,2), a contradiction. If D = ⌊n/2⌋, the extremal sets are classified: odd n gives R_n only (Altman). Even n gives, for n = 6, profiles (6,6,3) or (5,5,5), and for n ≥ 8, R_n or R_{n+1} minus a vertex (Fishburn 1995). Each of these is checked directly.

**CDL Theorem 1.3: the proof.** Vesztergombi's structural facts [Ve96, Props 1–8]:
- Δ-pairs lie in L₁.
- Every Δ₂-pair meets L₁ and lies in L₁ ∪ L₂.
- After repeatedly peeling vertices of degree < 2 from the Δ₂-graph G on L₁ ∪ L₂:
  - L₂′ is independent and every vertex in it has degree exactly 2;
  - each p ∈ L₁′ has at most 2 neighbours in L₂′ and at most 4 neighbours in L₁′;
  - if p has 3 neighbours in L₁′ it has at most 1 in L₂′; if it has 4, it has 0.
- Also used: μ(Δ₂) ≤ 3n/2 in general [Ve87] and μ(Δ₂) ≤ 4n/3 for convex sets [Ve85].

Degree counting then gives e(L₁′) ≤ min{4/3|L₁′|, 2|L₁′| − |L₂′|}.

**Barrier (CDL Prop 1.5).** Neither Δ₂ nor δ is always good. Their construction (regular m-gon, "server" ring, triangular-lattice patch) gives min{μ(Δ₂), μ(δ)} ≥ 9n/8 + o(n). It is also known that μ(Δ₂) > n is possible, up to about 3n/2 [Ve87, Ve96].

**CDL open problems.**
- 1.6: determine limsup_n sup_{|X|=n} min{μ(Δ₂), μ(δ)}/n. Currently 9/7 ≤ L ≤ 3/2.
- 1.11: is max(a₁ − a₂) ≥ n^{1+c/log log n}? This is Erdős #959.
- 5.2: is a(X) = (n−1, …, 1) achieved only by the three families shown?

## 2. Claims since CDL (forum; none refereed)

**Zeraoulia Rafik (28 Jan 2026).** Proves n = 7: D ≥ 4 is impossible by counting, and 7-point 3-distance sets are R₇ or R₆⁺. Reduces n = 8 to the profile {1,9,9,9} (D = 4, unique diametral pair). Note: RG doi 10.13140/RG.2.2.26754.95684.

**Przemek Chojecki (28 Jan 2026).** Closes n = 8 with GPT-5.2 by citing a "classification of 8-point 4-distance sets". **Flaw** (ienjoymath, 25 Jul 2026): no such classification exists in the literature, because sub-maximum k-distance sets are unclassified. The n = 8 case is still true by other routes.

**Marche / J. Marchetto (5 Jul 2026).** Covers 7 ≤ n ≤ 13. Cases n = 7–10 and 13 are unconditional, using exact-arithmetic descent and extension. Cases n = 11, 12 rely on Wei 2011 (which Marchetto re-derives). Code: https://github.com/JuanMarchetto/erdos-132-note. Also contributed a formal statement to google-deepmind/formal-conjectures.

**ienjoymath (25 Jul 2026).**
- Independent proofs for n = 7, 8, 9, 10, 13.
- **New: L ≥ 9/7 for CDL Problem 1.6.** The key idea is an even m-gon: servers sit under the midpoints of antipodal edges and pick up two exact δ-pairs each. Taking m = 2⌈3n/14⌉ plus a Harborth patch at mesh g gives min ≥ 9n/7 − 5√n.
- Conjectures L = 9/7. Claims an LP over Vesztergombi's constraints on which the construction is tight; the "companion note" is not yet out.
- Heavy Claude assistance. https://github.com/mathematiclover1337/erdos-132-note
- The note also records the obstruction at n = 14: it needs 14-point 7-distance sets, which are beyond current classifications.

**Evan Beller, proof-claim #218 (23 Aug 2026), partial, n = 8.**
- Route: profile (9,9,9,1). Deleting either diametral endpoint leaves a 7-point 3-distance set, which is R₇ or R₆⁺. A six-point overlap-rigidity lemma shows the two deletions coincide, which is a contradiction.
- Lean 4 verified, conditional on three literature inputs: Hopf–Pannwitz, g(3) = 7, and the classification of 7-point 3-distance sets.
- Links: https://github.com/EvanBeller/erdos-132. One comment (MalekZ, 24 Aug) points to a "Significance record"; no flaw has been raised.

**Other forum activity.**
- onetwothreefour (23 Jul): typo only.
- No comment by Bloom or a moderator on what counts for the prize.
- The page history shows the CDL paragraph was added 2025-10-20. The problem is still OPEN at $100, i.e. the site does not treat CDL's convex result as closing it.
- FAQ: prizes are paid by the Combinatorics Foundation (Steve Butler) only after publication in a reputable journal. The site owner has no say.

**Literature search 2023–2026.**
- No refereed paper beyond CDL attacks #132 directly. Semantic Scholar shows 0 indexed citations of CDL.
- Related recent work:
  - Bhowmick, *A problem of Erdős about rich distances*, arXiv:2407.01174 / Studia Sci. Math. Hungar. 62 (2025): ⌊n/4⌋ distances with μ ≥ n+1 (this solves #756).
  - The 2026 disproof of the unit-distance conjecture: OpenAI, n^{1+ε}; Sawin and others push the exponent to about 1.03. See *Remarks on the disproof…*, arXiv:2605.20695. Relevance to #132: a single distance can be polynomially rich.
  - Minkowski-grid repeated distances, arXiv:2607.05374.
  - None of these touch the "few distances with μ ≤ n" direction.

## 3. Open sub-questions, ranked (tractability × would-count-as-nontrivial)

1. **(b) for convex sets: s(A) → ∞, or even s(A) ≥ 3 for n ≥ n₀.**
   - Nobody has claimed this. It is a natural next step from CDL Thm 1.2, and a clean Erdős-question result.
   - Counting reduction: s ≥ D − ⌊(n−1)/2⌋ roughly. More exactly, (D−s)(n+1)+s ≤ C(n,2) gives s ≥ K+1 when D = ⌊n/2⌋+K.
   - So a convex counterexample has D = n/2 + O(1), with almost all multiplicities in [n+1, n+O(1)]. The question reduces to a **stability version of Altman/Fishburn**: classify, or bound s for, convex n-gons with ⌊n/2⌋+K distances.
   - Fishburn did K = 1 for n = 9 (*Convex nonagons with five intervertex distances*, Geom. Dedicata). Useful tools: Vesztergombi m_k ≤ kn (convex), m₁+m₂ ≤ 2n, and the Morić–Pritchard "levels" lemma (at most 2k−1 diagonals of length ≥ d_k per level).
2. **Enlarge the "not too convex" class.**
   - For example, prove (a) whenever |L₁| ≥ cn, or when there are O(1) layers. The route is to handle a third candidate distance (Δ₃, δ, or the largest distance from a hull vertex) when μ(Δ₂) > n.
   - This is moderate difficulty. It counts as "nontrivial" if the class is natural, e.g. "all sets with ≤ k convex layers".
3. **(a) for all n ≥ n₀, or even a large class via the μ(Δ₂) > n structure.**
   - When μ(Δ₂) > n, Vesztergombi's structure forces many L₂′ vertices of degree 2 and an L₁′ that looks like a regular polygon (CDL Prop 1.5 geometry). A stability analysis should give a third good distance; the "server" distances g and flank distances are natural candidates.
   - This is the prize-level target. It is hard, but the geometry is very rigid.
4. **Problem 1.6 upper bound < 3/2, or matching 9/7.**
   - Fairly tractable: an LP over Vesztergombi's constraints plus penny-graph degree bounds (hull vertices have δ-degree ≤ 4, so μ(δ) ≤ 3n − |L₁|). My quick check: the trivial LP with μ(δ) ≤ 3n − |L₁| and the three bounds of Thm 1.3 still gives 3/2 at |L₁| = |L₂| = n/2, so a genuinely new constraint is needed.
   - Answers CDL's problem, but **does not by itself** settle (a), since L ≥ 9/7 > 1. Probably judged "related progress", not #132 progress.
5. **n = 14 and beyond.**
   - Needs 14-point 7-distance set classification.
   - Low "nontrivial" value (finite, computational). Also, the problem page states it "cannot be resolved with a finite computation".
6. **(b) in general, or s ≥ n^{1−o(1)}.** Out of reach. Even s ≥ 3 in general is open.

## 4. Classical toolbox

- **Hopf–Pannwitz 1934**: μ(Δ) ≤ n (tight for odd R_n). Erdős #223.
- **Vesztergombi.**
  - [Ve85] *On the distribution of distances in finite sets in the plane*, Discrete Math 57 (1985) 129–145. Convex: μ(Δ₂) ≤ 4n/3, m_k ≤ kn, m₁+m₂ ≤ 2n.
  - [Ve87] *On large distances in planar sets*, Discrete Math 67 (1987) 191–198. General: μ(Δ₂) ≤ 3n/2, m_k ≤ 2kn.
  - [Ve96] *The two largest distances in finite planar sets*, Discrete Math 150 (1996) 379–386. The structural Props 1–8 listed in §1.
  - The 3n/2 and 4n/3 bounds are tight up to additive constants.
- **Erdős–Lovász–Vesztergombi** conjecture (convex): m₁+…+m_k ≤ kn. Known: ≤ (2k−1)n, and for k ≤ 4 with n large, plus m₃ ≤ 3n/2 and m₁+m₃ ≤ 2n. Source: Morić–Pritchard, arXiv:1103.0412.
- **Unit distances in convex position.**
  - Upper bound: O(n log n) (Füredi 1990, 2π n log₂n + O(n)); n log₂n + O(n) (Aggarwal, arXiv:1009.2216); Brass–Pach 9.65 n log₂n.
  - Lower bound: 2n − 7 (Edelsbrunner–Hajnal). Erdős–Moser conjectured 2n.
- **Altman** (Amer. Math. Monthly 70 (1963) 148–157): a convex n-set has D ≥ ⌊n/2⌋, with equality for odd n only at R_n.
- **Fishburn**.
  - *Convex polygons with few intervertex distances*, Comput. Geom. 5 (1995) 65–93: the even-n equality cases (R_n, R_{n+1} minus a vertex; n = 6 has profiles (6,6,3) and (5,5,5)).
  - *Convex nonagons with five intervertex distances*.
  - *Distances in convex polygons* (in *The Mathematics of Paul Erdős*).
- **k-distance sets.** g(2) = 5, g(3) = 7, g(4) = 9, g(5) = 12, g(6) = 13 (Wei 2012). Classifications exist only for maximum sets, plus 11-point 5-distance sets (Wei 2011). For n: a counterexample needs D ≤ 1 + ⌊(C(n,2)−1)/(n+1)⌋ ≈ n/2.
- **Minimum distance** (penny graph).
  - μ(δ) ≤ ⌊3n − √(12n−3)⌋ (Harborth 1974), tight via hexagonal patches.
  - Hull vertices have δ-degree ≤ 4 (at most 3 for small angles), so μ(δ) ≤ 3n − |L₁|.
  - Dumitrescu, *A product inequality for extreme distances* (SoCG 2019): μ(δ)·μ(Δ) ≤ 9n²/8 + O(n) (#957). Erdős–Pach: μ(δ) + μ(Δ) ≤ 3n − c√n.
- **Lefmann–Thiele**: Σ a_k² = O(n³) for convex sets. **Guth–Katz**: Σ a_k² = O(n³ log n) and D ≥ cn/log n in general (too weak to force D > n/2).

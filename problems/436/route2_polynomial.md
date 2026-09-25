# Erdős #436, Λ(5,3): route 2, polynomial and structured-value constructions

Date: 2026-09-25. Scope: try to prove G_5 (THEORY §7.5) with identities or parametric families in
which the three values n, n+1, n+2 have g-values forced to 1. Notation as in THEORY §7 and §9:
g: N → μ_5 is completely multiplicative, f is its additive version (g = ζ^f), and a zero run is n
with g(n) = g(n+1) = g(n+2) = 1. "Split primes" means primes p ≡ 1 mod 5, which are the primes that
split completely in Q(ζ_5).
Labels: **PROOF**, **CITED**, **HEURISTIC**, **OPEN**, as in THEORY §7.

## 0. Verdict

- **No proof of G_5.** The route does not close case C.
- **Partial result, new (Theorem R2.3) [PROOF modulo Tao 1509.05422 Cor 1.5 + THEORY §7].**
  G_5 holds for every g that agrees with some Dirichlet character χ on all split primes outside a
  thin set E, i.e. #{p ∈ E : p ≤ T} = o(T^{1/4}). Any finite E qualifies.
  - g is **arbitrary** on the non-split primes p ≢ 1 mod 5. These are 3/4 of all primes.
  - The class contains case-C functions, e.g. g(p) = 1 for p ≡ 1 and g(p) = ζ otherwise.
  - It is disjoint from the class Γ(E,c), c ≠ 0, of THEORY §9, so it covers new ground.
  - The witness is n = m^5 − 1 with m ≡ 0 mod Q. The algebra forces g(n+1) = 1 and puts all of
    g(Φ_5(m)), g(Φ_10(m)) on split primes, so only the **two-point** condition g(m−1) = g(m+1) = 1
    is left. Tao's logarithmic two-point Elliott theorem gives that condition.
- **Why the route cannot give all of G_5 as it stands.** Four results [PROOF] explain this.
  - R2.1: a single identity is never enough.
  - R2.5: families with bounded unknowns are finite (Thue).
  - R2.4: pigeonhole over any structured family is exactly a finite certificate, which must reach
    beyond the known bound Λ(5,3) ≥ 2·10^9.
  - R2.6/R2.7 (parallel-hyperplane lemma): in every polynomial family, all affine-linear factors of the
    three values are parallel. The analytic input is therefore always either a **one-variable**
    correlation of Elliott type (open for the 12 terms in T, THEORY §7.4) or g at **irreducible
    nonlinear polynomial values** (polynomial Chowla, open even for the parity of Ω(m^2+1)). No family
    can move the problem into the finite-complexity linear-forms regime (Green–Tao, Frantzikinakis–Host)
    where theorems exist.

## 1. What an identity can force

**Lemma R2.1 (universal values) [PROOF].** For N ∈ Q_{>0}, g(N) = 1 for every completely
multiplicative g: Q_{>0} → μ_5 iff N is the fifth power of a rational number.
*Proof.* If v_p(N) ≢ 0 mod 5 for some p, take g(p) = ζ and g(q) = 1 for all q ≠ p. ∎

Two consecutive positive integers are never both fifth powers. So no single triple is a zero run of
every g, and every argument needs input that depends on g: either pigeonhole over many triples
(§3) or analytic information (§4, §5).

Refinement. In the triple (m^5 − 1, m^5, m^5 + 1) the middle value is universal. The best one can
hope for is to make the outer values depend on g only through primes in a restricted class. That is
what §2 does.

## 2. The split-prime class [PROOF modulo citations]

**Lemma R2.2 (cyclotomic divisors) [PROOF, classical].** Let Q be a positive integer with 5 | Q and
m ≡ 0 mod Q. Then Φ_5(m) ≡ Φ_10(m) ≡ 1 mod Q. Every prime factor of Φ_5(m)Φ_10(m) is ≡ 1 mod 5 and
does not divide Q.
*Proof.* Φ_5(0) = Φ_10(0) = 1 gives the congruence. Let p | Φ_5(m). Then p ∤ Q, so p ≠ 5, and
m^5 ≡ 1 mod p. If m ≡ 1 mod p, then Φ_5(m) ≡ 5 mod p, so p = 5, which is impossible. So ord_p(m) = 5
and 5 | p − 1. For Φ_10(m) = Φ_5(−m), apply the same argument to −m. ∎

**Theorem R2.3 [PROOF modulo CITED].** Let g: N → μ_5 be completely multiplicative. Suppose there
are a Dirichlet character χ mod q and a set E of primes with #{p ∈ E : p ≤ T} = o(T^{1/4}), such that
g(p) = χ(p) for every prime p ≡ 1 mod 5 with p ∉ E. Then g has a zero run. More precisely, there are
infinitely many m for which n = m^5 − 1 is a zero run.

*Proof.* If g is in case A or B, THEORY §7.2 and §7.3 give zero runs. So assume g is in case C.
Then every g^a with a ≢ 0 is non-pretentious (THEORY Lemma 7.1(ii)).

Step 1 (choose the modulus). Choose y with 8 Σ_{p∈E, p>y} 1/p < 1/50. This is possible because the
condition on E implies Σ_E 1/p < ∞ (partial summation). Put Q := 5·q·∏_{p∈E, p≤y} p.

Step 2 (the algebra). Let m ≡ 0 mod Q, and suppose no prime of E ∩ (y, ∞) divides
Φ_5(m)Φ_10(m) (call such m *clean*). Then:
- g(m^5) = g(m)^5 = 1;
- every prime factor of Φ_5(m) is split, lies outside E, and does not divide q (Lemma R2.2 and the
  choice of Q). So g(Φ_5(m)) = χ(Φ_5(m)) = χ(1) = 1, since Φ_5(m) ≡ 1 mod q. The same holds for
  Φ_10(m);
- m^5 − 1 = (m−1)Φ_5(m) and m^5 + 1 = (m+1)Φ_10(m).

So n = m^5 − 1 is a zero run iff g(m−1) = g(m+1) = 1.

Step 3 (the two-point count). We use the expansions
- 1[Q | m] = (1/φ(Q)) Σ_{ψ mod Q} ψ̄(−1) ψ(m−1), and
- 1[g(x) = 1] = (1/5) Σ_{a∈Z/5} g^a(x).

They give

  E^log_{m≤x} 1[Q|m] 1[g(m−1)=1] 1[g(m+1)=1]
    = (1/(25 φ(Q))) Σ_{a,b,ψ} ψ̄(−1) E^log_{m≤x} (g^a ψ)(m−1) · g^b(m+1).

- a = b = 0: the term is (1/25) E^log 1[Q|m] → 1/(25Q).
- a ≢ 0: g_1 := g^a ψ satisfies Tao's hypothesis (1.8). For p ∤ Q,
  1 − Re(g^aψ χ' p^{−it})(p) = 1 − Re(g^a · (χ'ψ) p^{−it})(p). So the (1.8) sums for g^aψ and
  (χ', t) differ from those for g^a and (χ'ψ, t) by at most Σ_{p|Q} 2/p. For g^a, (1.8) holds by
  THEORY Lemma 7.2, because g^a is μ_5-valued and NP. Tao 1509.05422 **Cor 1.5** then applies with
  (a_1,b_1) = (1,−1), (a_2,b_2) = (1,1) (a_1b_2 − a_2b_1 = 2 ≠ 0), g_2 = g^b and ω(x) = x. The term
  is o(1).
- a = 0, b ≢ 0: put g_1 = g^b at (a_1,b_1) = (1,1) and g_2 = ψ at (1,−1). The same corollary shows
  the term is o(1).

(Cor 1.5 was checked in the PDF, text re-extracted 2026-09-25. It asks only that g_1, g_2 be
multiplicative with |g_i| ≤ 1, and it puts (1.8) on g_1 alone.) So the set G of m with Q | m and
g(m±1) = 1 has logarithmic density exactly 1/(25Q).

Step 4 (clean m). For p ∈ E with p > y we have p ∤ Q. The condition p | Φ_5(m)Φ_10(m) puts m in at
most 8 classes mod p (at most 4 roots of each quartic). Together with Q | m, that is at most 8
classes mod Qp. Also p ≤ Φ_5(m) ≤ 2m^4. So

  #{m ≤ X : Q | m, m not clean} ≤ Σ_{p∈E, y<p≤2X^4} 8(X/(Qp) + 1)
                                 ≤ (8X/Q) Σ_{p∈E,p>y} 1/p + 8·#E(2X^4) ≤ X/(50Q) + o(X).

A set of upper natural density ≤ δ has upper log density ≤ δ. So G ∖ {not clean} has upper log
density ≥ 1/(25Q) − 1/(50Q) > 0. Every m in it gives a zero run at m^5 − 1. ∎

**Checks.**
- The algebra of Steps 2 and 4 does not depend on g. It was verified exactly on two examples by
  `scripts/route2_split_class.py` (PARI/gp factorisations, 16 s).
  - Example 1: g = 1 on split primes and pseudo-random on all other primes, Q = 5, m = 5k,
    k ≤ 2000. Every Φ_5(m) and Φ_10(m) had only split prime factors and f-value 0. There were 133
    good m, the first being m = 30. All 133 zero runs n = m^5 − 1 were re-verified from the full
    factorisations of m^5 ± 1.
  - Example 2: g = order-5 character mod 11 on split primes, with exceptions E = {31, 41, 61} and
    pseudo-random values on E and on non-split primes. Q = 5·11·31·41·61, k ≤ 1500. There were 81
    good m, the first being m = 63,963,075.
  - The good fractions (0.067 and 0.054) are near the predicted 1/25. At this small scale
    small-prime biases in f(m±1) are expected.
- Case C is not special here: in cases A and B the theorem follows from THEORY §7 alone. Case C
  functions exist in the class. For g = 1 on split primes and g = ζ elsewhere,
  D(g,1;x)^2 ~ (3/4)(1 − cos 72°) log log x. For χ of order 5, g\bar χ is equidistributed on the
  split primes. So g weakly pretends to no χ.

**Remarks.**
- *Disjointness from THEORY §9.* If g(p) = ζ^c (c ≠ 0) for almost all p, then g cannot equal a
  character χ on almost all split primes. Every class a ≡ 1 mod 5, including a = 1, contains
  infinitely many primes, which would force χ(1) = ζ^c. So R2.3 and §9 cover different g.
- *Λ-form.* A run-free completely additive f (one exists iff Λ(5,3) = ∞) is **not** character-like
  on the split primes up to any thin exceptional set. This is a structural constraint on
  counterexamples, not a finite one.
- *Summable E is out of reach [HEURISTIC].* With only Σ_E 1/p < ∞, the "+1" terms in Step 4 cannot
  be controlled. An adversary can put the largest prime factor of Φ_5(m) into E for almost every m,
  because Σ_m 1/P^+(Φ_5(m)) converges for typical sizes. This is THEORY §9.3's remark again.
- *Other centres are worse [PROOF for the prime-divisor claims].*
  - n + 1 = a·m^5 needs g(a) = 1, which Lemma R2.1 makes circular unless a is a fifth power.
  - Putting the fifth power at an end (n = m^5) leaves m^5 + 2, which is irreducible. Its prime
    divisors include every p ≢ 1 mod 5, since x ↦ x^5 is a bijection mod such p.
  - Higher centres m^{5j} add further cyclotomic factors and never remove Φ_5.
  - Any nonconstant polynomial has infinitely many split prime divisors (Chebotarev in the
    compositum of its splitting field with Q(ζ_5)). So some hypothesis on the split primes cannot
    be avoided by a different polynomial.
  - The set of prime divisors of Φ_5 has density 1/4 = 1/deg Φ_5, the minimum possible for a
    degree-4 polynomial (Cameron–Cohen: a transitive group of degree n has ≥ 1/n elements with a
    fixed point).
- *Replacing χ by a "Hecke character on Q(ζ_5)" gains nothing [HEURISTIC, standard CFT].* We have
  g(Φ_5(m)) = G((m − ζ)), where G(𝔞) := g(N𝔞). G is Galois-invariant. For cyclic K/Q,
  Ĥ^{−1}(Gal, C_K) = 0, and so every Galois-invariant idele-class character of K is χ∘N. On degree-1
  primes this is g(p) = χ(p) again.

## 3. Pigeonhole over structured families

**Lemma R2.4 (compactness) [PROOF].** The following are equivalent.
(i) G_5.
(ii) There is a finite set T of triples (n, n+1, n+2), each written as n+i = s_{n,i} w_{n,i}^5 with
     s_{n,i} a product over a finite set S of "atoms", such that for every assignment x ∈ (Z/5)^S
     some triple has all three linear forms ⟨v_{n,i}, x⟩ = 0.
(iii) Λ(5,3) < ∞.
*Proof.* (iii)⇒(ii): take S = primes ≤ Λ+2, the atoms primes, and w = 1 (README: S(R) UNSAT).
(ii)⇒(i): an assignment on S is the restriction of f.
(i)⇒(iii): THEORY Thm 7.5. ∎

So any "Ramsey / linear algebra over Z/5" argument over a family is, after compactness, a finite
UNSAT certificate. Its largest triple must lie beyond the known lower bound Λ(5,3) ≥ 2,000,028,671
(README log, 2026-09-23). There is no shortcut through a small structured family.

**Lemma R2.5 (bounded unknowns ⇒ finitely many triples) [PROOF modulo Thue 1909].** Let S be a
finite set of primes. Only finitely many n ≥ 1 have n and n+1 both in ⟨S⟩·N^5.
*Proof.* Write n = s_0 x^5 and n+1 = s_1 y^5, where the s_i are S-units with exponents in [0,4].
There are finitely many pairs (s_0, s_1). For each pair, s_1 y^5 − s_0 x^5 = 1 is a Thue equation:
the binary form has 5 distinct linear factors over C, and 5 ≥ 3. So it has finitely many integer
solutions. ∎

Consequence. A family whose g-values depend only on g|_S, i.e. lie in a fixed subspace spanned by
f(p), p ∈ S, is finite. The "fifth-power trick" adds only finitely many constraints to the weakened
instance F_y of THEORY §2, and it adds no variables.
[computation] `scripts/route2_thue_scan.py` (18 s) considers S = {2,3,5,7,11,13} and every member
M = s z^5 ≤ 10^18 with z > 1 coprime to S. It finds **no** consecutive pair, and so no triple.
As a sanity check it does find 242 = 2·11^2, 243 = 3^5 for S = {2,11}. For y-smooth instances
the trick is therefore empty in practice.

## 4. Polynomial families: the parallel-hyperplane obstruction

**Lemma R2.6 (parallel factors) [PROOF].** Let P_0, P_1 ∈ C[x_1,…,x_r] with P_1 − P_0 = c ∈ C^×.
If ℓ_0 and ℓ_1 are affine-linear forms with ℓ_0 | P_0 and ℓ_1 | P_1, then ℓ_0 and ℓ_1 have
proportional linear parts.
*Proof.* Otherwise the hyperplanes {ℓ_0 = 0} and {ℓ_1 = 0} meet (r ≥ 2: two non-parallel affine
hyperplanes intersect; r = 1 is trivial). At a common point P_0 = P_1 = 0, which contradicts
P_1 − P_0 = c ≠ 0. ∎

**Corollary R2.7 [PROOF].** Let (P_0, P_1, P_2) be a polynomial family of consecutive values over Q
(P_{i+1} − P_i = 1) in any number of variables. Write P_i = c_i W_i^5 L_i R_i, where L_i is the
product of the affine-linear factors, W_i ∈ Q[x], and R_i has no linear factor. Then:
- all affine-linear factors of L_0, L_1, L_2 have one common direction h (if two members have none,
  there is nothing to prove; otherwise apply R2.6 pairwise). So L_i = ∏_j (α_{ij} h(x) + β_{ij}),
  with h a primitive integral linear form;
- g(P_i(x)) = g(c_i) · ∏_j g(α_{ij} h(x) + β_{ij}) · g(R_i(x)), since g(W^5) = 1;
- more generally, factors of two different members cut out **disjoint** hypersurfaces. In
  particular at most one member can have a homogeneous (conical) factor, and in two variables all
  Bézout intersections of such factors lie on the line at infinity.

What this means.
- The split parts see g only through the one-variable, dilated-shift correlation
  E_h ∏_{i,j} g^{e_i}(α_{ij} h + β_{ij}). That is the infinite-complexity, Elliott-type regime of
  THEORY §7.4 and Prop 9.6 [PROOF that the family has this shape; the analytic difficulty is
  **CITED/OPEN** as in THEORY].
- The finite-complexity theorems need pairwise **non-parallel** forms, so no family reaches them.
  These theorems are: Green–Tao linear equations with Möbius–nilsequences; Frantzikinakis–Host,
  arXiv 1403.0945 (JAMS 2017), application (iii): Chowla's zero mean for aperiodic multiplicative
  functions at certain two-variable polynomials; Browning–Matthiesen and Matthiesen for norm forms
  and linear correlations.
- The nonlinear parts R_i bring polynomial Chowla, which is weaker still (§5).
- Example: m^5 ± 1. L = m ∓ 1 (both in direction m) and R = Φ_5, Φ_10. §2 removes R by
  *assumption* on the split primes. What remains is the two-point correlation in m, which is known.

[HEURISTIC] Consequently the most a family can do is what §2 does: trade uncontrolled values for
(a) short one-variable correlations, which are known only for two points, and (b) g at irreducible
polynomial values, which is controllable only under a hypothesis on g at those values' prime
divisors. Every family must contain values of type (b) or a three-point one-variable pattern. Pure
type (a) with only two-point patterns would need two of the three values to be c·W^5, which is
impossible by Mason–Stothers: c_2 W_2^5 − c_0 W_0^5 = 2 forces 5d ≤ 2d − 1. A general proof of
"every family must contain (b) or a three-point pattern" is **OPEN** (not attempted beyond these
cases).

## 5. Literature on g at polynomial values [CITED]

| source | result | reach for G_5 |
|---|---|---|
| Teräväinen, arXiv 2010.07924 (Amer. J. Math. 146 (2024)) | λ(P(n)) changes sign infinitely often if P splits into linear factors over Q, or is a reducible cubic, or a product of quadratics of a special type, or outside a density-0 set of P (abstract) | Sign changes of λ only, and one polynomial. Nothing for Φ_5 or for μ_5-valued g |
| Helfgott, math/0408142 and math/0501177 | Σ λ(F(x,y)) = o(N^2) for reducible, resp. irreducible, binary cubic forms (abstract) | Two-variable **one-point** averages of λ; Corollary R2.7 prevents conical factors in two members |
| Frantzikinakis–Host, arXiv 1403.0945 (JAMS 30 (2017)) | Structure theorem (periodic + Gowers-uniform) for all bounded multiplicative functions; zero mean for aperiodic f at certain two-variable polynomials (abstract) | Finite-complexity only; excluded for consecutive triples by R2.6 |
| Browning–Sofos–Teräväinen, arXiv 2212.10373 | Polynomial Chowla and Bateman–Horn **on average over polynomials** of fixed degree (abstract) | Averages over P, not a fixed family like Φ_5 |
| Wilson, arXiv 2408.08726 | Moments of Σ λ(f(n)) over random f (abstract) | Same |
| Tao, arXiv 1509.05422, Thm 1.3 / Cor 1.5 (PDF checked) | Two-point log Elliott for g_1 satisfying (1.8), any a_1b_2 ≠ a_2b_1 | **Used** in Theorem R2.3 |
| THEORY §7.6, §9.1 | Three-point log results stop at the 112 non-T terms, and at m = 3 for Ω patterns | The T-terms remain open |

Known status: polynomial Chowla for a fixed irreducible P of degree ≥ 2 is open, even for the
parity of Ω(n^2+1). Nothing is known about Ω(Φ_5(m)) mod 5, so Conjecture W of THEORY §9.2 stays
**OPEN**. We found no "consecutive power residues via identities" argument in the literature that
goes beyond the l = 2 and LLMS-type smooth-number constructions already in novelty_sources/.

## 6. Self-attack

1. *Is Theorem R2.3 vacuous?* No. It contains case-C g (see the Checks in §2), and it is disjoint
   from THEORY §9's classes.
2. *Could Tao's corollary fail because of zeros of ψ?* Cor 1.5 allows any multiplicative g with
   |g| ≤ 1, so zeros are fine. (1.8) for g^aψ reduces to (1.8) for g^a up to Σ_{p|Q} 2/p (§2,
   Step 3).
3. *Is the log density of G a genuine limit?* Yes. Every non-main term is o(1) as x → ∞ (Cor 1.5
   with ω = x), and E^log 1[Q|m] → 1/Q.
4. *The Step 4 union bound.* Primes p > 2X^4 cannot divide Φ_5(m) for m ≤ X. Primes in (y, 2X^4]
   contribute X/(Qp) + 1 per class. The "+1" terms total 8#E(2X^4) = o(X), which is exactly the
   o(T^{1/4}) hypothesis.
5. *Pretentious g.* Handled by THEORY §7.2, which includes the q L^{5j+1} fix from §8 item 4.
6. *Does R2.3 say anything about the general case?* Only the Λ-form in §2. A general run-free f
   is adversarial on the split primes, and there R2.3 gives nothing. **G_5 remains open.**

## 7. Reproducibility

- `python3 problems/436/scripts/route2_split_class.py`: checks Lemma R2.2 and Steps 2 and 4 on two
  explicit examples and lists zero runs n = m^5 − 1 (needs `gp`; 16 s).
- `python3 problems/436/scripts/route2_thue_scan.py`: the fifth-power-cofactor scan of §3 (18 s,
  < 50 MB).

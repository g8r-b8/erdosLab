# Route 1: Hildebrand's elementary method, from pairs to triples (Λ(5,3), G_5)

Date: 2026-09-25. Scope: THEORY.md §7–§9 notation. g: N → μ_5 is completely multiplicative, f = log_ζ g
is completely additive into Z/5, and a **zero run** is n with g(n) = g(n+1) = g(n+2) = 1. G_5 is
Conjecture 7.5 (case C). Labels: **PROOF** (full argument given here), **CITED** (published statement,
checked in the source unless marked), **HEURISTIC**, **OPEN**.

**Verdict: exact point of failure. No proof and no new partial case.** Hildebrand's argument for
pairs has two separate engines:
- **(R)** a Ramsey step on "special sets", which gives a consecutive pair with *some* common
  colour;
- **(S)** a colour-shift step, which moves that colour to 1 using only one-point densities of g in
  arithmetic progressions, plus a pigeonhole.

Both break for triples, at points that can be stated exactly:
- (R) cannot give constant consecutive triples by Ramsey theory alone. The hypergraph of "good
  triples" (the triples that become consecutive after division) is 2-colourable in every finite set,
  by one fixed completely multiplicative ±1 colouring (Prop. 1.3, PROOF). This is Dietzel's
  observation, made precise at the level Hildebrand's proof uses.
- (S) cannot be run with one-point information. No finite configuration has the pigeonhole property
  that triples need (Prop. 2.2, PROOF). Once pairwise information is added as well, the step asks
  for zero runs of g in residue classes, which is the problem itself.
- In case C, (S) *can* be replaced by §7 Lemma 7.3 (diagonal invariance). What is left is (R) for
  triples in density form, which is §7.5 item 3 again. So the route closes into a circle.
- The parity of k enters Hildebrand's scheme only in the pretentious branch (his order-reduction
  step, which corresponds to our case A). That branch is already closed for triples (§7.2). The
  failure is in the non-pretentious branch, and there the obstruction does not depend on k.

## 0. Sources

| source | obtained? | used for |
|---|---|---|
| A. Hildebrand, *On consecutive kth power residues. II*, Michigan Math. J. 38 (1991) 241–253, doi 10.1307/mmj/1029004331 | **yes**. Project Euclid PDF (scanned), read page by page | §1 below; this is the Λ(k,2) < ∞ paper cited on erdosproblems.com/436 as [Hi91] |
| C. Dietzel, arXiv 1309.7506 (2013) and 1810.01518 (2018; Moscow J. Comb. NT 8 (2019)) | yes (text) | elementary Ramsey/Hindman proofs of Hi91 Thm 2; the remark after his Problem 5; Comment 1 |
| Matomäki–Radziwiłł–Tao, arXiv 1509.01545, §§2–4 | yes (text) | the length-3 Liouville argument. MRT attribute Cor. 2.8, Prop. 3.3 and §4 to Hildebrand 1986 |
| Tao–Teräväinen, arXiv 1904.05096, §1.3 | yes (text) | definitions of stable and weakly stable sets; statements of Balog/Hildebrand 1985 and Hildebrand 1989 |
| McNamara, arXiv 2312.08544 | yes (text) | Hildebrand's stable-sets conjecture, and its counterexample for k = 3 at density 1/2 |
| Hildebrand, *On a conjecture of Balog*, PAMS 95 (1985) 517–523 | **no**: ams.org serves a Cloudflare challenge | the stable-sets pair theorem (stated via TT19 and McNamara) |
| Hildebrand, *On consecutive values of the Liouville function*, Enseign. Math. (2) 32 (1986) 219–226 | **no**: e-periodica (pid ens-001:1986:32::102) requires a bot-verification step | the λ patterns of length 3 (described via MRT) |
| Hildebrand, *On consecutive k'th power residues*, Monatsh. Math. 102 (1986) 103–114 (k prime), doi 10.1007/BF01490203 | no (Springer paywall) | cited in Hi91 as [7]; Hi91 reproduces what is needed |
| Hildebrand, *On integer sets containing strings of consecutive integers*, Mathematika 36 (1989) 60–70, doi 10.1112/S0025579300013577 | no (paywall) | the stable-sets threshold d(S) > 1 − 1/(k−1) (stated via TT19 and McNamara) |
| Hildebrand, *Multiplicative properties of consecutive integers*, LMS LN 247 (1997), doi 10.1017/CBO9780511666179.010 | no (CUP) | survey, probably the best exposition of "stable sets" |
| Heath-Brown, *The divisor function at consecutive integers*, Mathematika 31 (1984) | not attempted | special sets (Hi91 [5]) |

Note on the brief: the "stable sets" papers are PAMS 1985 and Mathematika 1989. I found no 1991
Math. Proc. Cambridge paper of Hildebrand on stable sets. The Λ(k,2) paper is Michigan 1991.
PDFs are in the session scratchpad under `lit/`, not in the repo.

## 1. Hildebrand's proof that Λ(k,2) < ∞, written out [CITED, Hi91]

**Theorem (Hi91 Thm 2).** There is c_0(k) such that every completely multiplicative f: N → μ_k has
n ≤ c_0(k) with f(n) = f(n+1) = 1.
(Λ(k,2) ≤ c_0(k) follows by taking f = the k-th power character mod p, extended by f(p^m n) = f(n).)

**Special sets.** S = {n_1 < … < n_r} with n_j − n_i = (n_i, n_j) for all i < j (Heath-Brown).
For every pair i < j, with d = (n_i, n_j):
a_{ij} := n_i/d and a_{ij} + 1 = n_j/d are consecutive integers.
So one special set of size r contains r(r−1)/2 consecutive pairs.

**Step (R): Ramsey (Hi91 Lemma 3, (3.8)–(3.9)).** Pigeonhole makes f(n_i) = ω_0 constant. Ramsey's
theorem, applied to the colouring of pairs by f((n_i, n_j)), makes that value constant too. Then

  f(n_i/(n_i,n_j)) = ω for all i ≠ j   (Hi91 (4.3)),

so each of the r(r−1)/2 pairs is a consecutive pair of the single colour ω.

**Step (S): the shift (Hi91 §4).** Set P = q∏n_i, P_i = P/n_i and n_i(t) = (1 + tP_i)n_i. Then:
- S(t) is special, with the same gcds;
- f(n_i(t)/d) = ω·f(1 + tP_i)   (Hi91 (4.4)).

So it is enough to find t such that **at least two** indices i satisfy f(1 + tP_i) = ω̄   (4.5).
Every pair is good, so *any* two hits suffice. Hildebrand counts Σ_{t≤x} N(t)/t, where N(t) is the
number of hits. Each index contributes the log density of {n ≡ 1 mod P_i : f(n) = ω̄}. By **Hi91
Lemma 2** (an elementary Halász-type dichotomy, proved with Dirichlet series) that density is
≥ δ_2/P_i, unless f^{k_1} agrees with a character χ_1 on all p ≤ x outside a set 𝒫_1 with
Σ_{𝒫_1} 1/p ≤ c_2. With r > 2/δ_2 the average of N(t) exceeds 2, so some t ≤ x^{2/3} has N(t) ≥ 2.
**This is a first-moment pigeonhole. It uses one-point information only.**

**Order reduction (pretentious branch).** If Lemma 2's second alternative holds, then f^{k_1}
pretends to χ_1 with k_1 < k_0, and the argument restarts in F_{k_1}(x, χ_1, 𝒫_1). The special sets
are then built with the extra congruences (3.4)–(3.7): n_i = q^{α_i}m_i with **α_i ≡ 0 mod k (a
k-th-power trick)**, m_i ≡ (m_i, m_j) mod q, and (m_i, 𝒫) = 1. These make f(n_i/(n_i,n_j))^{k_0} =
χ((m_i/(m_i,m_j))) = χ(1) = 1. The sign issue (m_i, m_j) ≡ −1 mod q in (3.15) is removed by
reflecting to S'(t) = {tP − n_{r+1−i}}. The iteration ends because F_0^* = ∅.

**Where the pair structure is used.** Only in two places:
1. Every pair of a special set is good. Hence Ramsey needs only a colouring of *pairs*, and the shift
   needs only *two* hits.
2. Pigeonhole with average N(t) > 2 forces two hits with no correlation input.

Dietzel (1309.7506 Thm 4; 1810.01518 Thm 4) replaces special sets by "block-divisible" sequences
together with Schur/Ramsey (x + y = z with x | y) or Hindman's theorem. He removes Lemma 2 entirely,
so his proofs are pure Ramsey. The Ramsey conclusion is then applied to the coset partition of Q_+ by
A = ker f.

**The Liouville length-3 argument (Hildebrand 1986, as reproduced in MRT 1509.01545 §§2–4) [CITED,
secondary].**
- MRT describe Hildebrand's method as elementary and ad hoc, using the multiplicative properties of
  λ at 2, 3 and 5.
- For +++ (our analogue), MRT §3 derives a chain of exclusions from "no +++". Examples are Cor. 3.2
  and Prop. 3.3 ("essentially due to Hildebrand"). Each step uses λ(p) = −1 for p ∈ {2, 3, 5}.
- The chain ends at "λχ_3 is locally constant", which contradicts a short-interval theorem.
  Hildebrand's own i.o. version is not obtained (see §0). The engine is **binary pigeonhole**: of
  any three ±1 values, two agree (MRT Thm 2.7). An excluded pattern therefore *determines* the
  missing sign.

## 2. Triples: where each step breaks

Call a triple of positive integers **good** if it has the form (dm, d(m+1), d(m+2)), i.e. a 3-AP whose
common difference divides its terms. This is exactly the triple analogue of a pair in a special set.
If g(dm) = g(d(m+1)) = g(d(m+2)) = c, then g(m) = g(m+1) = g(m+2) = c·ḡ(d).
In a special set, a triple i < j < l is good iff n_j − n_i = n_l − n_j.

**Lemma 1.1 [PROOF].**
(a) No set of ≥ 4 integers has all of its triples in arithmetic progression.
(b) A special set contains no 4-term AP.

*Proof.*
(a) If (n_1,n_2,n_3) and (n_1,n_2,n_4) are both APs, then n_4 = 2n_2 − n_1 = n_3.
(b) Take a, a+d, a+2d, a+3d in a special set. The pair (a, a+2d) gives 2d = (a, a+2d) | a. The pair
(a+d, a+3d) gives 2d | a+d. Together, 2d | d, which is impossible. ∎

So there is no "complete" triple structure. The pair argument's key feature (every pair is good) has
no analogue for triples.
(Checked: Hildebrand's inductive special sets of sizes 3–6 contain 1–2 three-term APs and no 4-AP;
`scratchpad/r1/special.py`.)

**Proposition 1.3 (the good-triple hypergraph has property B) [PROOF].** Let g̃ be completely
multiplicative with g̃(3) = 1 and g̃(p) = (p/3) for p ≠ 3. For every set S ⊂ N:
- S_± := {n ∈ S : g̃(n) = ±1} contain no good triple;
- one of them has at least |S|/2 elements.

*Proof.* On a good triple, g̃(d(m+i)) = g̃(d)g̃(m+i). Exactly one of m, m+1, m+2 is divisible by 3.
The other two are ≡ 1 and ≡ 2 mod 3 and coprime to 3, so g̃ takes the values +1 and −1 on them. So
g̃ is not constant on any good triple. ∎
(Checked numerically: g̃ has no constant consecutive triple for m < 10^6, `barrier.py`. Note that
g̃ is the Λ(2,3) = ∞ witness.)

**Corollary 1.4 (step (R) fails for triples) [PROOF].** There is no Ramsey statement of the form
"every 2-colouring of N (or of a finite set S) has a monochromatic good triple". Consequently no
purely Ramsey-theoretic argument (special sets, block-divisible sequences, Hindman, or any
partition-regularity result for arbitrary finite colourings) produces a constant consecutive triple
for g. This is Dietzel's remark after his Problem 5 (1309.7506), restated for the exact configuration
that (R) would need.

Any successful (R3) must use that the colouring comes from a homomorphism into a group of *odd*
order. For μ_5 the needed statement is:

  **G_5^const [OPEN]:** every g: N → μ_5 has m with g(m) = g(m+1) = g(m+2).

This is not a Ramsey theorem. It is the problem itself, up to the colour shift.

**Proposition 2.2 (step (S) fails for triples with one-point input) [PROOF].** Consider any
configuration of Hildebrand type:
- elements n_1, …, n_r;
- shifts n_i(t) = n_i(1 + tP_i) that preserve good triples (true whenever P is a multiple of every
  n_i: differences are unchanged and d | n_i | P);
- hit sets H(t) = {i : g(1 + tP_i) = target_i}.

The only hypothesis Hildebrand's step uses is "each i ∈ H(t) with log-density ≥ δ in t". For δ ≤ 1/2
this cannot force a good triple inside some H(t). Take the random model: pick ε = ±1 with probability
1/2 each, and put H(t) := a random subset of S_ε in which each element is kept with probability 2δ.
- Every index has hit-density δ.
- No H(t) contains a good triple, by Prop. 1.3.

(With μ_5-valued g the natural δ is 1/5.) ∎

With pairwise information added: the joint law of (g(1+tP_i), g(1+tP_j)) is known to be uniform for
NP g. This is Tao 1509.05422 Thm 1.3 for general linear forms a_1n+b_1, a_2n+b_2 with
a_1b_2 ≠ a_2b_1, combined with §7 Lemma 7.2. It still does not help, because of what success on a
good triple *means*. Let e = (i,j,l) be a good triple with difference d. Then success at t says

  g(a(t)) = g(a(t)+1) = g(a(t)+2) = 1,  where a(t) = (n_i/d)(1 + tP_i),

and a(t) runs through the residue class n_i/d mod P/d. So the shift step for triples asks exactly for
**a zero run of g inside one of finitely many residue classes**. That is G_5 with a congruence
condition (compare Prop. 9.4, H(κ)), and it is no easier. The step never replaces three-point
information by lower-order information, which is precisely what it does for pairs.

**Remark 2.3 (where odd k enters Hildebrand's scheme) [PROOF, by inspection of Hi91].** Parity is
used only in the pretentious branch. There, f^{k_0} = χ on the m_i-parts, and one needs χ of the
consecutive quotients to be 1. For triples this branch is our case A, closed by CRT with χ(−1) = 1
(§7.2). The non-pretentious branch is where Prop. 1.3 and Prop. 2.2 act, and they do not depend on
k. So for even k the method fails for triples in the pretentious branch (χ_{−3}, which is Λ(2,3) = ∞);
for odd k it fails in the non-pretentious branch.

## 3. Attempted fixes

**F1. Replace (S) by §7 Lemma 7.3 [PROOF of the reduction; the conclusion is OPEN].**
- For g in case C, the log density of zero runs along any convergent subsequence equals 1/5 of the
  log density of constant triples. So the colour shift is automatic in density form, and needs no
  pigeonhole.
- Cases A and B are closed (§7.2, §7.3). Hildebrand's order reduction is therefore not needed either.
- What remains is (R3) in *density* form: constant triples of positive upper log density. This is
  §7.5 chain item 3, and by Prop. 1.3 Ramsey arguments cannot supply it.
- Can Ramsey at least give positive density? The shifted configurations S(t) give a Ramsey output
  for each t, so ≫ x/P outputs up to x. That would give density if (R3) held for each S(t), which it
  does not.
- **Net: the route closes into §7.5 item 3.**

**F2. The fifth-power trick (n+1 = m^5) [PROOF of the reduction; OPEN].**
- For odd m, n = m^5 − 1 is a zero run iff g(b) = g(b+1) = ḡ(2), where b = (m^5−1)/2.
- More generally, for every even n = 2b: n is a zero run iff g(b) = g(b+1) = ḡ(2) and g(2b+1) = 1.
- For NP g the pair condition is known, with density 1/25 (Tao Cor 1.5 + Lemma 7.2). Hildebrand's
  method with target colour c ω̄ in (4.5) gives the same elementarily; for NP g the second alternative
  of Hi91 Lemma 2 fails for large x, since only finitely many χ_1 of bounded conductor occur.
- The third condition is the problem:
  - Putting the fifth power into the special set requires 2b(t)+1 = (n_i + n_j + 2tP)/d to be a fifth
    power. Then t = t(y) is a quintic polynomial, and Hi91 Lemma 2 would be needed for g along
    1 + t(y)P_i. No one-point density result exists for g on values of irreducible polynomials of
    degree ≥ 2; even the parity of Ω(y^2+1) is open (§9.2, Conjecture W).
  - Without the fifth power, g(2b+1) = 1 is a third linear form (b, b+1, 2b+1). This is the T-set
    problem restricted to even n.
- Note: Hi91 (3.5) already contains a k-th-power trick (α_i ≡ 0 mod k). There it only neutralises
  q in the pretentious branch.

**F3. Hildebrand/MRT length-3 chain (λ, +++) [HEURISTIC].**
- The chain transports exclusions through λ(2m) = −λ(m) and similar identities, and it closes
  because of the binary pigeonhole.
- For g, "no zero run at n" excludes only 1 of the 5 values of g(n+2) given g(n) = g(n+1) = 1. The
  implications therefore do not determine values and cannot be chained. This is the same weakness as
  THEORY §1 Lemma 4 (a prime needs 5 runs, not 3).
- The values g(2), g(3), g(5) are unknown (6 classes for (f(2), f(3)) by §1 Lemma 2). A case split
  over small primes is exactly the SAT/DFS tree of THEORY §2, estimated at about 10^18 nodes.
- MRT's endpoint ("λ pretends to χ_3", with χ_3(−1) = −1) has no μ_5 analogue. By Lemma 7.1 every
  character g can pretend to has χ(−1) = 1, and such g are case A. The obstructing structures in
  case C are non-character local Bohr models (Prop 9.6), which a chain of exact local implications
  does not see.

**F4. Stable sets (Balog–Hildebrand 1985; Hildebrand 1989) [CITED via TT19 / McNamara].**
- Hildebrand 1989: a stable S with lower density d(S) > 1 − 1/(k−1) has all k-point patterns in
  positive density. For k = 3 the threshold is d(S) > 1/2.
- McNamara (2312.08544 Thm 1.6/1.7) shows 1/2 is sharp. His example twists by χ_3 through p^{iT},
  so it is again the χ(−1) = −1 mechanism.
- Our kernel K = {g = 1} has density 1/5 and is *not* stable: p^{−1}K = {g = ḡ(p)}.
- K is weakly stable in TT's sense only when g is constant on primes up to a density-0 set. That is
  the §9 class Γ(E,c), where Prop 9.6 shows TT's method is insufficient.
- Stable sets built from g (for example the level sets of Ω) do not encode g-runs. So neither
  stable-sets theorem applies, and even the proven threshold (1/2) is far above 1/5.

**F5. Higher-uniformity Ramsey inside special sets (van der Waerden for 3-APs in S) [PROOF of
failure].**
- Any 2-colouring of a special set by g̃ has no monochromatic 3-AP (Prop. 1.3). So no "vdW inside
  special sets" statement holds.
- Special sets also have no 4-APs (Lemma 1.1(b)). So they cannot be enlarged into Szemerédi-type
  structures without leaving the special class.

## 4. What is proved here

1. Lemma 1.1, Prop. 1.3 and Cor. 1.4: the good-triple hypergraph is 2-colourable in every set, by the
   single multiplicative colouring g̃. So Hildebrand's step (R) has no triple version. [PROOF]
2. Prop. 2.2: Hildebrand's step (S) cannot be run with one-point densities, and with pairwise
   information it reduces to zero runs in residue classes. [PROOF]
3. Remark 2.3: parity enters Hildebrand's scheme only through the pretentious branch, which for triples
   is already closed. [PROOF by inspection]
4. F1: combined with §7 Lemma 7.3, Hildebrand's route reduces G_5 to §7.5 item 3 and to nothing
   weaker. [PROOF of the reduction]

None of this is a partial proof of G_5. **Honest verdict: route 1 fails. The point of failure is the
triple analogue of Hi91 (4.5), and equivalently of (4.3).**

## 5. Referee attack points

1. **Prop 2.2 is a barrier for a proof *schema*, not for G_5.**
   - It shows that the inputs Hildebrand's step consumes (per-index densities, plus pairwise
     independence) are satisfiable without a good triple.
   - The random model uses only the index hypergraph. It is not claimed to be realised by an actual g.
   - Check that "per-index density ≥ δ" is really the only thing (4.5) uses. It is: the proof sums
     N(t)/t.
2. **Prop 1.3 applies to good triples with a common divisor d.**
   - A generalised scheme could use different divisors, x_i/y_i = m+i with g(x_i) = g(y_i). The
     general statement (any argument valid for all finite-index subgroups of Q_+) also fails, because
     ker g̃ has index 2. But then the barrier is only "must use odd index", which is Dietzel's
     remark. Is anything stronger than that claimed? No.
3. **The claim "for NP g, Hildebrand's method gives pairs of every colour c".**
   - It needs Hi91 Lemma 2 at a single large x for all χ_1 of bounded conductor at once. This holds
     because NP ⇒ D(g^{k_1}, χ_1; x) → ∞ for each of finitely many χ_1 (Lemma 7.1(ii)).
   - Not needed downstream: Tao Cor 1.5 already gives it.
4. **Remark 2.3.** The reading of Hi91 §3 ((3.14), (3.15) and the reflection S'(t)) is from the
   scanned PDF. Re-check that no parity input is hidden in Lemma 2 itself (none is visible: Lemma 2
   is stated for all k).
5. **Sources.** Hildebrand 1985, 1986 (Enseign.) and 1989 were *not* read. §1's account of them
   depends on MRT, TT19 and McNamara. A referee should check that Hildebrand's i.o. proof of +++
   contains no tool beyond binary pigeonhole and λ(p) = −1 that could transfer.
6. **F1 circularity.** Lemma 7.3 depends on the 112 vanishing correlations (TT Cor 1.6, Tao Cor 1.5),
   so it is not elementary. The elementary character of Hildebrand's method is lost in F1 in any case.

## 6. Reproducibility

- `scratchpad/r1/special.py`: builds Hildebrand-inductive special sets and checks speciality, 3-APs,
  4-APs, and g̃-monochromatic 3-APs. Runs in under 1 s.
- `scratchpad/r1/barrier.py`: checks that g̃ has no constant consecutive triple below 10^6 (1 s).
- Hi91 page images: rendered with `gs -sDEVICE=pnggray -r110` into `scratchpad/lit/hi91png/`.

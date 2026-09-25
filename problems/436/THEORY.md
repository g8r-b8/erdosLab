# Erdős #436, Λ(5,3): structure and theory on the finiteness side

Date: 2026-09-23. Scope: finiteness of Λ(5,3), attacked through structure rather than larger SAT runs.
Notation is as in README.md. f is completely additive, f: Z_{>0} → Z/5. A **zero run** at r means
f(r) = f(r+1) = f(r+2) = 0. F_y(X) is the weakened instance: only primes ≤ y, and only runs of three
consecutive y-smooth numbers ≤ X. S(R) is the full instance (every r ≤ R).

**Bottom line: there is no finiteness certificate and none is within reach by case splitting.**
Every tree search that branches on small primes first has to get through about 2·10^14 consistent
assignments to the primes ≤ 97. No ordering we tried changes the ≈10^18 estimate. We have no
sound UNSAT result, so this file claims no bound on Λ(5,3).

Labels used below:
- **[proof]**: a complete argument, given here.
- **[computation]**: an exact run of a sound instance, with the command.
- **[estimate]**: a Knuth random-probe estimate. Statistical, not a proof.
- **[heuristic]**: a plausibility argument, or one that is conditional on unproven conjectures.

## 1. Lemmas

**Lemma 1 (normalisation) [proof].** Take any fixed order of the primes, including a dynamic order
that depends only on values already assigned. We may assume the first nonzero value along that
order is 1.
*Proof.* For u ∈ (Z/5)^*, f ↦ u·f maps completely additive functions to completely additive
functions, and it preserves the zero set (u·a = 0 ⇔ a = 0). So f has a zero run at r iff u·f does.
All values before the first nonzero value are 0, and 0 is fixed by scaling. So f and u·f follow
the same branch up to that point, and some u makes the first nonzero value 1. ∎
(`sdfs.c` and `mrvdfs.c` use this. A dynamic order is allowed because it is a function of the
assigned values.)

**Lemma 2 (the {2,3} layer) [proof].** The only constraints that involve no prime other than 2
and 3 are the runs r = 1 and r = 2. Both say (f(2), f(3)) ≠ (0,0). After Lemma 1 there are
exactly 6 classes of (f(2), f(3)): (0,1), (1,0), (1,1), (1,2), (1,3), (1,4).
*Proof.* A zero run made only of {2,3}-smooth numbers needs two consecutive pairs of 3-smooth
numbers. The consecutive 3-smooth pairs are (1,2), (2,3), (3,4) and (8,9) (Størmer; elementary via
2^a − 3^b = ±1, Levi ben Gershon / Catalan for these bases). So the only such triples are (1,2,3)
and (2,3,4). They give f(2) = f(3) = 0 is forbidden, and (f(2), f(3), 2f(2)) ≠ 0, which is the
same condition. The count: of the 24 pairs ≠ (0,0), 4 have f(2) = 0 and f(3) ≠ 0 (one class after
scaling), and 20 have f(2) ≠ 0 (scale f(2) to 1, which leaves 5 classes). ∎

**Lemma 3 ("f(2) = 0 is not forced") [computation, full sound instance S(R)].** Some classes are
satisfiable. Each one below is witnessed by an explicit f whose first zero run r was recomputed
from the decoded f by `lamenc run`.

| class (f(2), f(3)) | S(10^5) | S(10^6) |
|---|---|---|
| (0,1) | SAT | **SAT**, first run 1,020,605 |
| (1,0) | SAT | **SAT**, first run 1,008,762 |
| (1,1) | SAT, first run 100,180 | unknown: kissat 300 s (default) and 900 s (`--lucky=false`) |
| (1,2) | SAT, first run 102,025 | unknown: kissat 300 s |
| (1,3) | SAT, first run 100,555 | unknown: kissat 300 s |
| (1,4) | SAT, first run 117,475 | unknown: kissat 300 s |

So neither "f(2) = 0" nor "f(3) ≠ 0" can be proved with any bound R ≤ 10^6. The class (1,0) has
an f with no zero run below 1,008,762. That f has f(2) = 1, f(3) = f(5) = … = f(29) = 0. It is the
mirror image of the published models (f(2) = 0, f(3) = 1). The README observation "models always
have f(2) = 0" comes from the solver's lucky phase, not from structure.
The four classes with f(2), f(3) both nonzero are the only candidates for a small structural lemma.
Kissat does not decide them at 10^6 in 300 s. That is not evidence of UNSAT: the lucky phase
fails once units are forced.
Commands:
`lamenc enc 5 3 1000000 s.cnf s.map`, then add the unit clause base(p)+v for each cube literal
(the 6-line helper is in §5), then `kissat -q --time=300`, then `lamenc run 5 3 8000000 s.map out`.

**Lemma 4 (k-core deletion) [proof].** In any sub-instance of F_y(X) or S(R), a prime q that lies
in fewer than k = 5 runs can be deleted together with those runs. The result is equisatisfiable.
*Proof.* Fix every value except f(q). Each member of a run is affine in f(q) with coefficient
e_q mod 5, and that coefficient is nonzero for at least one member. So "all three members vanish"
holds for at most one value of f(q). Fewer than 5 runs forbid at most 4 values, so some value
remains. Iterate. ∎
*Effect [computation]:* none. The 5-core of F_100(10^9), F_300(10^8) and F_1000(10^9) is the whole
instance: every prime lies in ≥ 5 runs (`python kcore.py 5 1000 runs.txt`). The rule does explain
why k = 5 is so much weaker than k = 3. Wiping out one prime needs 5 runs forbidding 5 distinct
values, not 3.

**What was not provable.** The task suggested lemmas like "f(2) = 0 is forced" or constraints on
f(5), f(7). Lemma 3 shows these are false up to R = 10^6, at least for the two classes above.
No lemma collapses the top of the tree.

## 2. Tree-size estimates (task 2)

`scripts/mrvdfs.c` is new. It is a DFS with forward checking over all runs: a run constrains a
prime as soon as that prime is the last unassigned one in the run. It supports three orders:
- `inc`: increasing primes, the same as `sdfs.c`;
- `mrv`: fewest remaining values;
- `mrvdeg`: MRV, ties broken by the number of runs where the prime is one of the last 2
  unassigned.

It also supports `--fix` cubes and the Knuth estimator.
Validation [computation]: on k = 3, F_300(10^8), `--order inc` reproduces `sdfs` exactly (31,538
nodes, UNSAT). `--order mrv` refutes it in 8,306 nodes. On F_200(10^8), both find the unique model.

### 2.1 k = 5, F_1000(10^9) (247,734 runs) [estimate]

| order / cube | est. nodes | sd of mean | probes | mean death depth |
|---|---|---|---|---|
| baseline `sdfs` (README) | 1.1e18 | 1.4e17 | 3000 | – |
| `inc` | 1.3e18 | 6.8e17 | 300 | 31.9 |
| `mrv` | 3.2e18 | 3.1e18 | 300 | 34.8 |
| `mrvdeg` | 1.6e18 | 1.2e18 | 300 | 34.8 |
| `inc`, cube f(2)=0, f(3)=1 | 6.3e17 | 2.0e17 | 1000 | 30.7 |
| `inc`, cube f(2)=1 | 5.7e17 | 1.5e17 | 1000 | 30.4 |
F_2000(10^9): see §2.3 (no change).

MRV and degree tie-breaking do not help. All domains stay at size 4–5 for the first ~25 levels, so
MRV falls back to picking small primes. The two f(2) branches are the same size. Imposing
f(2) = 0 (if it were a lemma) would save a factor of 2 at most.

### 2.2 Why: the top of the tree is intrinsic [estimate]

The only constraints that involve primes ≤ 97 alone are the 787 runs of 100-smooth triples (a
finite set, by Størmer). The number of normalised assignments to the 25 primes ≤ 97 that satisfy
all of them is estimated at

- F_50(10^9) (208 runs, 15 primes): **1.57e9** models, against 5^15/4 = 7.6e9 assignments;
- F_100(10^9) (787 runs, 25 primes): **2.03e14** models (sd 1.3e12, 200,000 probes, 94% of
  probes reach a leaf).

Any DPLL/DFS proof that assigns the primes ≤ 97 first must reach every one of these ≈ 2·10^14
consistent partial assignments, because nothing below depth 25 can prune them earlier. A proof
could do better only by using larger primes before the small ones are all fixed. MRV looks for
exactly that and finds nothing: no large prime becomes constrained early.
Even with perfect pruning below depth 25, 2·10^14 leaves at ~10^6 nodes/s/core is ≈ 6 core-years.
The realistic ≈ 10^18 is ≈ 3·10^4 core-years.
Commands: `smoothruns 100 1000000000 3 > r100.txt` and
`mrvdfs 5 3 100 r100.txt --order inc --knuth 200000`.

### 2.3 Other runs
- **Raising y does not help [estimate].** F_2000(10^9) (`smoothruns 2000 1e9 3`, 454 MB RSS):
  - `inc`: est 1.29e18 (sd 6.8e17), identical to F_1000(10^9). With the same seed the probes make
    the same choices and die at mean depth 31.9 (primes ≈ 131). They never reach a prime > 1000,
    so the extra runs never fire.
  - `mrv`: est 2.5e18 (sd 1.5e18), mean death depth 35.1.

  The tree size is set by the small-prime layer, not by y.
- **Full-instance cube f(2) = f(3) = 1 at R = 10^6:** kissat `--lucky=false`, 900 s: unknown
  (rc 0). This is the hardest-looking of the 6 classes, but "unknown" is not evidence of UNSAT.

## 3. The algebraic angle (task 3) [computation on toy/residual instances + heuristic]

Encoding (`scripts/nullstellensatz.py`). Work over F_k with x_p^k = x_p. Each run gives
P_r = ∏_m (1 − L_m^{k−1}), which is the indicator that all three members vanish.
F_y(X) is UNSAT iff 1 = Σ g_r P_r in F_k[x]/(x^k − x). The Nullstellensatz degree is
max(deg g_r + deg P_r). Equivalently, F_k^n is covered by the linear subspaces
V_r = ker L_1 ∩ ker L_2 ∩ ker L_3 (codimension ≤ 3). The first-moment count is useless, because
the count needed to cover is only ≈ 125 subspaces.

Experiments. All are dense exact linear algebra over F_k. Only k = 3 is small enough.
- **Toy pair instances (l = 2), k = 3.** F_13 (6 primes, 68 pairs) and F_17 (7 primes, 108 pairs)
  are UNSAT. Their Nullstellensatz degree is 4 = deg P_r. The trivial bound is 2n = 12 or 14.
  MRV-DFS refutes both in 3 nodes, so these toy cases are easy for every method.
- **k = 3 triples, residual instances.** F_300(10^8) has 62 primes. We fixed all but 3–6 primes,
  either at random or to a local-search "near model" (194 violated runs). Every residual is
  refuted at degree 2. These residuals are trivially easy (unary constraints) and say nothing
  about the full instance.
- **Degree-0 multipliers (1 = Σ c_r P_r with constants c_r).** This would be a certificate that
  can be checked by linear algebra at any n. It does not exist even for the toy pair instance
  F_13 (the sampled system is infeasible, which is exact: see `ns_core.py`). For F_300(10^8),
  11,500 unknowns need more than 11,500 sample points (≈ 10^12 operations), which we did not run.
- **UNSAT cores.** A deletion-minimal core of F_300(10^8) for k = 3 was still 7,852 of the 11,500
  runs after the 512- and 64-block passes. We stopped it there.

**Verdict: dead end at this scale [heuristic].**
- A Nullstellensatz/PC refutation of degree D over 168 variables has about C(168+D, D) monomials.
  It is feasible only for D ≲ 4.
- For k = 5 the axioms alone have degree 12.
- Every sub-instance on primes ≤ 500 is satisfiable (F_500(10^9) is SAT). So any refutation must
  use constraints on ≳ 95 variables at once, and a large UNSAT core is needed even for k = 3.
- Expansion-type lower bounds for PC (Alekhnovich–Razborov) would then predict a large degree.
  We did not prove such a lower bound.
- Degree-0 (linear) certificates fail already on the toy instance.

We see no route by which algebra beats case splitting here.

## 4. A structural route that could work (analytic reformulation) [heuristic, conditional]

By compactness (README), Λ_comb(5,3) < ∞ iff **every** completely multiplicative g: N → μ_5 takes
the value 1 at three consecutive integers. Put g = ζ^f and 1_{g(n)=1} = (1/5) Σ_j g(n)^j. Then the
logarithmic density of zero runs is

  δ(g) = (1/125) Σ_{(a,b,c) ∈ F_5^3} lim (1/log x) Σ_{n≤x} g^a(n) g^b(n+1) g^c(n+2) / n

(taken along a subsequence where all 125 limits exist). Sort the 124 nontrivial (a,b,c):
- **one nonzero (12):** mean value of g^a. It is 0 when g is non-pretentious (Halász).
- **two nonzero (48):** two-point log correlations. They are 0 when g is non-pretentious
  (Tao 2016, two-point log Elliott). g^a is non-pretentious iff g is, because 5 is prime.
- **three nonzero, a+b+c ≢ 0 mod 5 (52):** the product g^{a+b+c} is non-pretentious, so the
  correlation is 0 (Tao–Teräväinen, Duke 2019, "structure of logarithmically averaged
  correlations": the correlation vanishes when the product does not weakly pretend to be a
  Dirichlet character).
- **three nonzero, a+b+c ≡ 0 mod 5 (12):** for example (1,1,3) and (1,2,2). The product is
  trivial, and **no current theorem controls these.** This is the "even-order" part of Elliott's
  conjecture.

The count checks: 12 + 48 + 52 + 12 = 124.

So:
- (i) **Conditional on the logarithmic 3-point Elliott conjecture**, every non-pretentious g has
  δ(g) = 1/125 > 0, so it has zero runs. Unconditionally, it would be enough that the 12 bad
  correlations sum to more than −1.
- (ii) The **pretentious case** is where g pretends to a Dirichlet character χ with χ^5 pretending
  to 1. For odd order χ(−1) = 1, which is exactly what defeats the k = 2 counterexample (χ_3).
  README's CRT argument already handles g equal to a finite product of such characters.
  Klurman's asymptotics for correlations of pretentious functions (Compositio 2017) turn the
  general pretentious case into a product of local densities. Proving that these densities are
  positive is plausibly elementary. **We have not done it.**

If (ii) were written down, the result would be "Λ(k,3) < ∞ for every odd k, conditional on the
3-point log-Elliott conjecture". It would say nothing unconditional about Λ(5,3). The same
obstruction appears for k = 3, where Λ(3,3) = 23532 is known only by machine: there the
uncontrolled correlations are (1,1,1) and (2,2,2).

## 5. Reproducibility

```
cd problems/436/scripts
cc -O2 -o mrvdfs mrvdfs.c -lm
./smoothruns 1000 1000000000 3 > r1000.txt       # 247,734 runs, ~30 s
./mrvdfs 5 3 1000 r1000.txt --order inc --knuth 300          # also mrv, mrvdeg; --fix 2=1
./mrvdfs 3 3 300 r300_1e8.txt --order mrv                    # k=3: UNSAT, 8,306 nodes
python3 kcore.py 5 1000 r1000.txt
python3 nullstellensatz.py 3 300 r300_1e8.txt --nfree 5 --seeds 4
python3 ns_core.py ns 3 13 p2_13.txt --deg 0 --points 729 --l 2   # p2_13 = smoothruns 13 1e8 2
# full-instance cube (Lemma 3):
./lamenc enc 5 3 1000000 s.cnf s.map
python3 - s.cnf s.map 2=1,3=0 c.cnf <<'EOF'
import sys; cnf,mp,spec,out=sys.argv[1:5]
base={int(a):int(b) for a,b in (l.split() for l in open(mp))}
u=[base[int(p)]+int(v) for p,v in (t.split('=') for t in spec.split(','))]
f=open(cnf); h=f.readline().split(); g=open(out,'w'); g.write(f"p cnf {h[2]} {int(h[3])+len(u)}\n")
g.writelines(f); g.writelines(f"{x} 0\n" for x in u)
EOF
kissat -q --time=300 c.cnf > c.out; ./lamenc run 5 3 8000000 s.map c.out
```

## 6. Verdict and most promising next step

- **No certificate.** No sound UNSAT was obtained, so no bound on Λ(5,3) is claimed.
- **Lemmas.** The proved ones are small: normalisation, the six {2,3} classes, and k-core
  deletion. The hoped-for "f(2) = 0 forced" is **false up to 10^6**; both f(2) = 0 and f(2) ≠ 0
  admit f with no zero run below 10^6.
- **Estimates.** Better orders leave the tree at ≈ 10^18. The ≈ 2·10^14 models of the 100-smooth
  layer are a floor for any small-primes-first case split.
- **Algebra.** Nullstellensatz / linear certificates look like a dead end at this scale.
- **Most promising route.** The analytic reformulation in §4. Proving the pretentious case
  (Klurman asymptotics + local positivity) unconditionally is a concrete, self-contained task. It
  would reduce finiteness of Λ(k,3) for all odd k to one named conjecture: 3-point log-Elliott
  with trivial product. On the computational side, the only remaining lever is CDCL clause
  learning, which could beat the 2·10^14 floor in principle. The CDCL runs so far show no sign of
  it (> 45 min per 3-prime cube on F_1000). A cloud cube-and-conquer should first be
  Knuth-estimated per cube.

## 7. Case analysis via the Elliott literature (2026-09-25)

Scope: which completely multiplicative g: N → μ_5 are **unconditionally** known to have a zero run
g(n) = g(n+1) = g(n+2) = 1, and what exactly is left. By compactness (README), Λ(5,3) < ∞ iff every
such g has one zero run. One n per g is enough, so positive density along *some* sequence of scales
is more than we need.
All theorem numbers below were checked against the arXiv PDFs (text extracted with pypdf, 2026-09-25).
Nothing was quoted from memory.
Labels: **PROOF** (a full argument is given here), **CITED** (a published theorem, cited by arXiv id
and number), **HEURISTIC**, **OPEN**.

**Status check (2026-09-25).** erdosproblems.com/436 still says "open, and cannot be resolved with
a finite computation" (last edited 25 Oct 2025). None of the papers read settles Λ(k,3) < ∞ for any
odd k ≥ 5. **The literature does not settle Λ(5,3).**

### 7.0 Notation and the expansion

- D(f,h;x)^2 = Σ_{p≤x} (1 − Re f(p) \bar h(p))/p is the Granville–Soundararajan distance.
  D(f,h;y,x) is the same sum over y < p ≤ x.
- g is **pretentious** if D(g, χ n^{it}; ∞) < ∞ for some Dirichlet character χ and some t ∈ R.
  Otherwise g is **non-pretentious (NP)**. This is KMT Definition 1.1.
- g **weakly pretends** to χ if D(g,χ;x)^2 = o(log log x). This is Tao–Teräväinen's notion in
  1708.02610, §1.2, with t = 0.
- Set C(a,b,c)(x) := E^log_{n≤x} g^a(n) g^b(n+1) g^c(n+2), for (a,b,c) ∈ (Z/5)^3. Then
  E^log_{n≤x} 1[zero run at n] = (1/125) Σ_{(a,b,c)} C(a,b,c)(x).
  This is exact, because g(n) ∈ μ_5 for every n ≥ 1.
- The 124 nontrivial terms fall into four groups: 12 one-point, 48 two-point, 52 three-point with
  a+b+c ≢ 0, and the set **T** of 12 three-point terms with a,b,c ≠ 0 and a+b+c ≡ 0. The six
  conjugate pairs in T are
  (1,1,3)~(4,4,2), (1,2,2)~(4,3,3), (1,3,1)~(4,2,4), (2,1,2)~(3,4,3), (2,2,1)~(3,3,4),
  (2,4,4)~(3,1,1).

**Lemma 7.1 (twists and powers) [PROOF].** Let g: N → μ_5 be completely multiplicative.
(i) If g is pretentious, the t in its definition is 0, and χ^5 is principal. In particular
    χ(−1) = 1 and χ(p) ∈ μ_5 for p ∤ q.
(ii) For j ≢ 0 mod 5, g^j is pretentious iff g is. Likewise, g^j weakly pretends to some character
    iff g does.
*Proof.* (i) The triangle inequality D(f_1f_2, h_1h_2) ≤ D(f_1,h_1) + D(f_2,h_2) holds for
1-bounded functions. It gives D(1, χ^5 n^{5it}; ∞) ≤ 5 D(g, χ n^{it}; ∞) < ∞, because g^5 ≡ 1.
Now Σ_{p≤x} Re(ψ(p)p^{-iu})/p = log|L(1+1/log x+iu, ψ)| + O(1), and this is bounded above unless
L has a pole at 1+iu, that is, unless ψ is principal and u = 0. Since Σ 1/p diverges, ψ = χ^5 is
principal and 5t = 0.
Also χ(−1)^5 = 1 and χ(−1) = ±1, so χ(−1) = 1.
(ii) Take j j' ≡ 1 mod 5. Then g = (g^j)^{j'} pointwise, and D(f^m, h^m) ≤ m D(f,h). ∎

So "pretentious" for g means exactly this: there is a χ of order dividing 5 with
Σ_{p: g(p) ≠ χ(p)} 1/p < ∞. (For p ∤ q, g(p)\bar χ(p) ∈ μ_5, and 1 − Re ζ^j ≥ 1 − cos 72° for j ≠ 0.)

**Lemma 7.2 (NP ⇒ Tao's hypothesis (1.8)) [PROOF from standard inputs].** Let g: N → μ_k be
completely multiplicative and NP. Then for every χ and every A ≥ 1,
inf_{|t|≤Ax} D(g, χ n^{it}; x) → ∞.
*Proof.* The standard inputs (Vinogradov–Korobov, Mertens) are:
- (F1) For fixed ψ and 1 ≤ |u| ≤ x^2 (any |u| ≤ x^2 if ψ is non-principal):
  Σ_{p≤x} Re ψ(p)p^{-iu}/p ≤ (2/3 + o(1)) log log x.
- (F2) For |u| ≤ 1: Σ_{p≤x} cos(u log p)/p = log min(log x, 1/|u|) + O(1).

Since g^k ≡ 1, D(g, χ n^{it}; x) ≥ k^{-1} D(1, χ^k n^{ikt}; x).
- If χ^k is non-principal, or |kt| ≥ 1: by (F1) the right side is ≥ k^{-1}((1/3 − o(1)) log log x)^{1/2}.
- If χ^k is principal and |kt| log x ≥ T: by (F2) the right side is ≥ k^{-1}(log T − O(1))^{1/2}.
- If |kt| log x < T: D(g,χn^{it};x) ≥ D(g,χ;x) − D(1,n^{it};x) ≥ D(g,χ;x) − (log(1+T) + O(1))^{1/2}.

Now choose T = T(x) → ∞ so slowly that log(1+T(x)) ≤ D(g,χ;x)^2/4. This is possible because
D(g,χ;x) → ∞ (g is NP). All three bounds then tend to ∞. ∎
(Tao 1509.05422, below Cor. 1.5, and Tao–Teräväinen 1904.05096, eq. (6.4), make the same VK remark
for λ and for ζ^{ω(n)}.)

### 7.1 The case split

Every g falls in exactly one of three classes. Weak pretension to χ n^{it} with t ≠ 0 is impossible
for μ_5-valued g (the weak analogue of Lemma 7.1(i), proved in §8 item 1b).

| case | definition | status | reference |
|---|---|---|---|
| **A** pretentious | D(g,χ;∞) < ∞ for some χ (so χ^5 = χ_0) | **closed**, zero runs of positive lower natural density | **PROOF** (§7.2), elementary |
| **B** NP, weakly pretentious | D(g,χ;∞) = ∞ ∀χ, but D(g,χ;x)^2 = o(log log x) for some χ | **closed**, zero-run density → 1/125 along a set of scales of log-log density 1 | **CITED** KMT 2304.05344 Thm 4.1 + Lemma 6.1 (the engine of Thm 1.6), §7.3 |
| **C** strongly NP | limsup D(g,χ;x)^2/log log x > 0 ∀χ | 112 of 124 terms → 0 at all scales. The 12 terms in T are **OPEN** | **CITED** TT 1708.02610 Cor 1.6; Tao 1509.05422 Cor 1.5 + Lemma 7.2 (§7.4) |

Our empirical near-counterexample (g(p) = ζ for almost all p > 100) lies in **case C**:
D(g,χ;x)^2 ≍ log log x for every χ. So does g = ζ^{Ω(n)}. This is exactly the uncovered class.

### 7.2 Case A (pretentious) [PROOF]

Let g pretend to χ mod q, with χ^5 = χ_0. Let E = {p | q} ∪ {p ∤ q : g(p) ≠ χ(p)}. Then Σ_{p∈E} 1/p < ∞.
Choose y > q with Σ_{p∈E, p>y} 1/p < 1/6. Put S = E ∩ [1,y] and L = ∏_{p∈S} p.
Pick j with q | L^{5j}, and set n_0 = L^{5j} − 1.

Step 1: g' has a zero run at n_0. Let g' be completely multiplicative with g' = g on S and g' = χ off S.
- n_0 + 1 = L^{5j}, so g'(n_0+1) = g'(L)^{5j} = 1, because values lie in μ_5.
- n_0 ≡ −1 and n_0 + 2 ≡ 1 mod every p ∈ S. So they are coprime to S, and g' = χ on them.
  Since q | L^{5j}, n_0 ≡ −1 mod q and n_0 + 2 ≡ 1 mod q.
  So g'(n_0) = χ(−1) = 1 and g'(n_0+2) = χ(1) = 1.
- (This is the README's CRT observation. It is where "k odd" enters: for even k, χ(−1) = −1 is
  possible.)

Step 2: transfer to g. Let M = q·L^{5j+1} (the factor q is needed when q is not squarefree; §8 item 4). Take any n ≡ n_0 mod M such that none of n, n+1, n+2 has a
prime factor in E ∖ S.
- The S-parts of n+i are the same as for n_0 + i: they are 1, L^{5j}, 1.
- The S-free parts are ≡ −1, 1, 1 mod q (for i = 1: n+1 = L^{5j}(1 + qL·t')), and all their primes
  lie outside E.
- So g(n+i) = g'(n+i) = g'(n_0+i) = 1.

Step 3: count. For X large, the number of bad n ≤ X in the class is
≤ Σ_{p∈E, y<p≤X+2} 3(X/(Mp) + 1) ≤ X/(2M) + 3π(X+2).
Here p > y > q is coprime to M. So the zero runs of g have lower natural density ≥ 1/(2M) > 0.
The same proof works verbatim for μ_k-valued g with k odd. ∎

Remarks.
- Klurman's formula (1603.08453, Thm 1.3, stated there for pairs) would give the exact density as an
  Euler product, but positivity is easier by the construction above.
- THEORY §4(ii) said this case was "plausibly elementary, not done". **It is now done.**

### 7.3 Case B (NP but weakly pretentious) [CITED + short deduction]

KMT Definition 1.5 (**moderately NP**): f is NP and, for some A,
(1/log log X)·inf_{|t|≤X^A, q≤(log X)^A} D(f, χ n^{it}; X)^2 → 0.
Weak pretension to a fixed χ implies this (take A = 1). The proof of KMT Lemma 6.1 shows the converse
up to a twist: moderately NP ⇒ weakly pretends to a fixed χ n^{it}. So for μ_5-valued g:
case B = moderately NP.

Deduction. Let g be in case B.
1. **KMT Lemma 6.1** gives χ, t and η(x) → 0 such that
   S = {x : D(g, χ n^{it}; x^{η(x)}, x) ≤ η(x)} has δ_loglog(S) = 1. This is a limit, not an upper
   density.
2. Let f_i = g^{e_i}, e_i ∈ {1..4}, with χ_i = χ^{e_i} and t_i = e_i t. By the triangle inequality,
   D(f_i, χ_i n^{it_i}; x^ε, x) ≤ 4η(x) ≤ ε for x ∈ S large.
3. D(f_1, χ_1 n^{it_1}; x) → ∞, because g^{e_1} is NP (Lemma 7.1(ii)).
4. **KMT Theorem 4.1** (1, 2 or 3 functions, a_j = 1, distinct h_j) then gives
   limsup_{x∈S} |(1/x) Σ_{n≤x} f_1(n+h_1)⋯| ≪ (log 1/ε)^{1/2} ε, for every ε. (KMT need h_j ∈ N:
   use shifts (1,2,3); this changes the averages by O(1/x).)

So all 124 nontrivial Cesàro correlations → 0 along the single set S. Hence
(1/x)#{n ≤ x : zero run} → 1/125 along S, and g has infinitely many zero runs.

We avoid quoting KMT Thm 1.6 as stated. Its conclusion is "δ^+_loglog(X) = 1" with X depending on
{f_1,…,f_k}, and upper-density-1 sets for different (a,b,c) need not intersect. The proof, which
we re-derived above, gives one S of full density for all powers of g at once.

This class contains KMT's "Liouville-like" functions:
- KMT §2.1, Thm 2.1: (−1)^{Ω_P(n)} with P of relative density 0 in the primes and Σ_P 1/p = ∞.
- **Their "Liouville-like" means g(p) = 1 for almost all p (a sparse sign set). That is the opposite
  of our g(p) = ζ for almost all p. Thm 2.1 does not reach case C.**
- KMT Thm 1.7 (powers, needs (d, e_1+…+e_k) = 1) and Cor 1.4 (real-valued, odd k) also do not
  reach T: for d = 5, T is exactly where 5 | e_1+e_2+e_3.

### 7.4 Case C (strongly NP): what is controlled [CITED], what is not [OPEN]

For g in case C, every g^s with s ≢ 0 fails to weakly pretend to any χ (Lemma 7.1(ii)).
- **12 one-point terms, 36 two-point terms with a+b ≢ 0, 52 three-point terms with a+b+c ≢ 0:**
  C → 0 as x → ∞ (log averages, at all scales). Reference: Tao–Teräväinen 1708.02610, **Cor 1.6**
  (the product g_0⋯g_k does not weakly pretend to any χ ⇒ E^log → 0). For the one-point terms,
  Halász also applies.
- **12 two-point terms with a+b ≡ 0** (for example g(n)\bar g(n+1)): C → 0. Reference: Tao
  1509.05422, **Cor 1.5**. Its hypothesis (1.8) on g^a holds by Lemma 7.2. (Cor 1.5 in fact covers
  all 48 two-point terms.)
- **The 12 terms in T:** no theorem applies. TT Cor 1.6 needs a non-weakly-pretentious product, but
  the product here is g^0 = 1. KMT Thm 4.1 needs small truncated distance, which fails in case C.
  KMT Thm 1.7 needs (5, a+b+c) = 1. Frantzikinakis–Host 1804.08556 (Thm 1.2: superlinear block
  complexity; Thm 1.5: structure of Furstenberg systems) gives no specific pattern.
  **So the §4 count "12 uncontrolled terms" is confirmed**, with two corrections:
  - "non-pretentious" in §4 must be read as "not weakly pretentious" (case C). Case B is handled by
    KMT instead.
  - The trivial-product two-point terms need Tao Cor 1.5 plus Lemma 7.2, not TT.

**Lemma 7.3 (diagonal invariance) [PROOF, given the citations above].** Let g be in case C. Take any
sequence x_m → ∞ along which the log-averaged law ν of (g(n), g(n+1), g(n+2)) on μ_5^3 converges.
- Then ν(ζu, ζv, ζw) = ν(u, v, w).
- Hence δ_log(zero runs) = (1/5) δ_log{n : g(n) = g(n+1) = g(n+2)} along x_m.
- It also equals (1/125)(1 + 2 Re Σ_{6 reps of T} C(a,b,c)).

*Proof.* ν̂ is supported on {0} ∪ T, which lies in the plane a+b+c = 0. Translating by (1,1,1)
multiplies ν̂(a,b,c) by ζ^{a+b+c} = 1. ∎

So the question is whether the "difference process" d_1 = f(n+1) − f(n), d_2 = f(n+2) − f(n+1)
(with g = ζ^f) hits (0,0). Known: d_1, d_2 and d_1 + d_2 are each uniform on Z/5 (the two-point
results).

**Lemma 7.4 (the known Fourier constraints cannot close the gap) [PROOF].** Let ν be uniform on the
25 triples (x, x+t, x+3t+1), for x, t ∈ Z/5.
- ν̂(a,b,c) ≠ 0 only for (a,b,c) = (2c,2c,c) with c ≠ 0. These four points are in T. So ν meets
  every constraint known in case C (all 112 vanishing terms).
- ν(0,0,0) = 0, since that would need t = 0 and 3t+1 = 0.

So any proof for case C must use arithmetic input beyond the vanishing of the 112 correlations.
This is the same "local Bohr set" obstruction that Tao–Teräväinen 1904.05096 describe:
- Their Thm 1.8 needs δ_1+δ_2+δ_3 > 1, and Thm 1.9 is the critical case = 1. Below 1, local Bohr
  sets can avoid the pattern (their discussion before §1.4, and Remark 2.5).
- Here each level set {g = 1} has density 1/5, so the sum is 3/5 < 1.

Why k = 3 is different. The TT proof of Thm 1.3 (ω, Ω mod 3 patterns) works because for k = 3, T is
the line spanned by (1,1,1). So the pattern density depends only on ω(n)+ω(n+1)+ω(n+2) mod 3, and the
critical-density Thm 1.9 applies. It also needs g(p) constant (weak stability), and applies to ζ^ω,
not to general μ_3-valued g. For k = 5, T is not a line and each density is 1/5.
[HEURISTIC: the "Elliott literature" route does not even reprove Λ(3,3) < ∞. That is known only by
LLMS's machine proof.]

### 7.5 The exact remaining gap

**Conjecture G_5 [OPEN].** Every completely multiplicative g: N → μ_5 that weakly pretends to no
Dirichlet character (Σ_{p≤x}(1 − Re g(p)\bar χ(p))/p ≠ o(log log x) for every χ) has some n with
g(n) = g(n+1) = g(n+2) = 1.

**Theorem 7.5 [PROOF modulo the cited theorems].** G_5 ⟺ Λ(5,3) < ∞.
- (⇐) is the Chebotarev lower bound of the README (Λ = Λ_comb for odd k): a g with no zero run
  is realised on primes ≤ R+2 by arbitrarily large p (§8 item 9).
- (⇒) holds because cases A and B are closed (§7.2, §7.3) and G_5 is case C.

Sufficient analytic forms of G_5, each implying the next:
1. The log 3-point Elliott conjecture for the 12 exponent patterns in T.
2. limsup_x Re Σ_{(a,b,c)∈T} E^log_{n≤x} g^a(n) g^b(n+1) g^c(n+2) > −1.
3. {n : g(n) = g(n+1) = g(n+2)} has positive upper log density (Lemma 7.3).
4. G_5.

**Conditional theorem for all odd k [PROOF modulo X].** Let X be the logarithmic three-point Elliott
conjecture for consecutive shifts, in Tao's corrected form:

> **X.** If f_0, f_1, f_2: N → D are multiplicative and at least one f_i satisfies (1.8) of
> 1509.05422 (inf_{|t|≤Ax} D(f_i, χ n^{it}; x) → ∞ for all χ and all A), then
> E^log_{n≤x} f_0(n) f_1(n+1) f_2(n+2) → 0.

Then X ⇒ Λ(k,3) < ∞ for every odd k. (A routine combination, presumably folklore; §8 item 12.)
*Proof.* Let g: N → μ_k.
1. H = {j ∈ Z/k : g^j pretentious} is a subgroup, H = mZ/k with m | k.
2. For j ∉ H, g^j is NP and μ_k-valued, so it satisfies (1.8) by Lemma 7.2. By X, every term (a,b,c)
   with some coordinate ∉ H vanishes.
3. The terms with (a,b,c) ∈ H^3 sum to (k/m)^3 E^log 1[G(n) = G(n+1) = G(n+2) = 1], where
   G := g^m: N → μ_{k/m} is pretentious and k/m is odd.
4. By §7.2, G has zero runs of positive lower density δ_G. So the zero runs of g have log density
   ≥ δ_G/m^3 > 0 at every scale. ∎

For k prime, X can be weakened to G_k (the analogue of G_5): the cases A and B arguments are
unconditional for any prime k. For composite k we did not check case B, because mixed
pretentious/NP powers occur there.
X is open. It contains the 2-point log-Chowla-type "trivial product" case in three-point form.
Even the 4-point log Chowla for λ is open.

### 7.6 Sources read (arXiv, 2026-09-25)

| arXiv id | paper | used |
|---|---|---|
| 1509.05422 | Tao, log-averaged Chowla/Elliott, two-point | Thm 1.3, Cor 1.5 |
| 1708.02610 | Tao–Teräväinen, Duke 2019 | Thm 1.2, Cor 1.6, Cor 1.13 |
| 1710.02112 | Tao–Teräväinen, odd order log Chowla | Thm 1.1 (λ only; subsumed by the above for our purpose) |
| 1904.05096 | Tao–Teräväinen, value patterns | Thms 1.3, 1.8, 1.9; §6 proof of Thm 1.3 |
| 2304.05344 | Klurman–Mangerel–Teräväinen | Def 1.1, 1.5; Thms 1.2, 1.6, 1.7, 2.1, 4.1; Lemma 6.1 |
| 1603.08453 | Klurman, Compositio 2017 | Thm 1.3 (pretentious asymptotics; not needed) |
| 1804.08556 | Frantzikinakis–Host | Thms 1.2, 1.5 (no pattern information) |
| 1509.01545 | Matomäki–Radziwiłł–Tao, sign patterns | Thm 1.6 (±1 only; pigeonhole fails for 5 colours, cf. Lemma 7.4) |

PDFs and text extracts are in the session scratchpad, not in the repo.

## 8. Referee report on §7 (2026-09-25)

*(2026-09-25, later: the fixes in items 1b, 4, 5a, 8, 9 and 12 have been folded into §7.)*

Adversarial referee pass on §7 as of commit 190b03d. §7 itself is left unchanged; fixes are given here.
Sources re-extracted with pypdf in the session scratchpad: KMT 2304.05344 (Def 1.1, 1.5, Thm 1.6,
Thm 4.1, Lemma 6.1 and its proof, proof of Thm 1.6), TT 1708.02610 (definition of weak pretension,
Thm 1.2, Cor 1.6), Tao 1509.05422 (Thm 1.3, Cor 1.5, (1.8)). **Not re-checked in this pass:**
TT 1904.05096 (Thms 1.3, 1.8, 1.9, Remark 2.5), Klurman 1603.08453 Thm 1.3, Frantzikinakis–Host,
MRT 1509.01545. §7 uses these only in remarks and heuristics, and no PROOF step depends on them.

**Summary.** No step is WRONG in a way that affects a conclusion. Case A has a real gap for
non-squarefree conductors. It is fixed by one change of modulus (item 4). Two statements say more
than their proofs cover: the t ≠ 0 exclusion for *weak* pretension (item 1b) and the "trivial" (⇐)
direction of Theorem 7.5 (item 9). Both have one-paragraph fixes. **Theorem 7.5 (G_5 ⟺ Λ(5,3) < ∞)
and the conditional theorem (X ⇒ Λ(k,3) < ∞ for all odd k) both survive.**

| # | item | verdict | details |
|---|---|---|---|
| 1a | Lemma 7.1(i), (ii) | CORRECT | D(1, χ^5 n^{5it}; ∞) ≤ 5 D(g, χn^{it}; ∞) < ∞ is fine (GS triangle inequality for 1-bounded functions, g^5 ≡ 1). The distance is the full series D(·;∞), with fixed χ and t. Uniformity in x is not needed. Σ_{p≤x} Re ψ(p)p^{-iu}/p = log\|L(1+1/log x+iu, ψ)\| + O(1) is bounded above unless (ψ principal, u = 0). Since Σ1/p = ∞, this forces 5t = 0 and χ^5 = χ_0. χ(−1) = 1 is correct. (ii) is correct. |
| 1b | §7.1: "Lemma 7.1(i) rules out weak pretension to χn^{it}, t ≠ 0" | CORRECT WITH FIX | Lemma 7.1(i) is stated and proved only for D(·;∞) < ∞. The weak version needs its own two lines. **Fix:** if D(g, χn^{it}; x)^2 = o(log log x) with χ, t fixed, then D(1, χ^5 n^{5it}; x)^2 ≤ 25·o(log log x). If χ^5 is non-principal or 5t ≠ 0, then Σ_{p≤x} Re χ^5(p)p^{-5it}/p = log\|L(1+1/log x+5it, χ^5)\| + O_{χ,t}(1) = O(1), so D(1, χ^5n^{5it}; x)^2 = log log x − O(1). That is a contradiction, so t = 0 and χ^5 = χ_0. Nothing downstream depends on this, because B and C are defined with t = 0, and TT's "weakly pretend" is also t = 0. |
| 2 | Lemma 7.2 (NP ⇒ Tao (1.8)) | CORRECT | Checked against 1509.05422: (1.8) is inf_{\|t\|≤Ax} D(g_1, χn^{it}; x)^2 → ∞ for every fixed χ and every A ≥ 1, which is exactly what the lemma proves. The three regimes are exhaustive. Regime 1 needs \|kt\| ≤ kAx ≤ x^2, which holds for x ≥ kA. In regime 3, D(χn^{it}, χ; x)^2 = D(1, n^{it}; x)^2 + O_q(1), and the O(1) is absorbed. T(x) depends on χ, which is allowed. (F1) (VK: log\|L(1+σ+iu, ψ)\| ≤ (2/3+o(1)) log log \|u\|) and (F2) are standard. |
| 3 | §7.1 partition A / B / C | CORRECT | C ("limsup D(g,χ;x)^2/log log x > 0 ∀χ") is exactly TT's "does not weakly pretend to any χ". TT define weak pretension as D^2 = o(log log x), so its negation is limsup > 0, and TT Cor 1.6 still concludes a full limit. A pretentious g weakly pretends to its χ, so C ⊂ NP and A, B, C partition all g. |
| 4 | Case A (§7.2) | **CORRECT WITH FIX (real gap when q is not squarefree)** | Step 2 claims "the S-free parts are ≡ n_0 + i mod q". This holds for i = 0, 2 (n ≡ n_0 mod M and q \| L^{5j} \| M). **It fails for i = 1:** n+1 = L^{5j}(1 + L·t'), and 1 + Lt' is only ≡ 1 mod L, not mod q. **Counterexample:** q = 25, χ of order 5 mod 25, g = χ on p ≠ 5. Then S = {5}, L = 5, j = 1, n_0 = 3124, M = 5^6. The admissible n = n_0 + M has n+1 = 5^5·6 with 2, 3 ∉ E, so g(n+1) = χ(6). But 6 has order 5 in (Z/25)^*, and an order-5 character is non-trivial on the order-5 subgroup, so χ(6) ≠ 1. **Fix:** take M := q·L^{5j+1}. Then n+1 = L^{5j}(1 + qL·t') has S-free part ≡ 1 mod q, so g(n+1) = g(L)^{5j}·χ(1) = 1. Steps 1 and 3 are unchanged: primes p > y > q do not divide M, and the bound X/(2M) + 3π(X+2) still gives lower natural density ≥ 1/(2M). Everything else checks. g(n+i) = 1 itself is obtained (not merely g = χ). Primes p \| q lie in S because y > q, and they are handled by the S-parts. Primes in S are ≤ y. An infinite E with Σ_E 1/p < ∞ is handled by the union bound over p > y (tail < 1/6). If S = ∅, the construction degenerates harmlessly (L = 1, M = q). The "verbatim for odd k" remark holds with 5 → k. |
| 5 | Case B (§7.3), KMT fit | CORRECT | Checked in the PDF. **Lemma 6.1** hypothesis: for every ε, the scales with inf_{\|t\|≤x^A, q≤(log x)^A} D^2 ≤ ε log log x have positive lower log density. Case B gives all large x (with A = 1, once q_χ ≤ log x). The **conclusion is a true δ_loglog = 1**: the proof ends with δ^−_loglog(N∖D) = 1. Thm 1.6 states only δ^+ = 1, and §7 is right not to use Thm 1.6 as stated. **Theorem 4.1** hypotheses: fixed χ_j, t_j (here χ^{e_j}, e_j t); max_j D(f_j, χ_j n^{it_j}; x^ε, x) ≤ ε; max_j D(f_j, χ_j n^{it_j}; x) ≥ 1/ε; ε ∈ (1/log log x, 1/2); a_i h_j ≠ a_j h_i. All hold on the single set S from Lemma 6.1 applied to g alone. For x ∈ S large, η(x) ≤ ε/4 gives [x^ε, x] ⊂ [x^η, x], and D(g^e, ·; x^ε, x) ≤ eη ≤ ε. S does not depend on ε, so all 124 terms → 0 along one S. Two minor points. (a) KMT take h_j ∈ N, so use shifts (1,2,3) and shift n by 1, which changes Cesàro means by O(1/x). (b) Thm 4.1's implied constant depends on the fixed χ_j, t_j, h_j, which is fine. The claim "case B = moderately NP" is also right: (6.3) of the proof gives weak pretension to a fixed χn^{it}, and item 1b then forces t = 0. The deduction does not need it. |
| 6 | Case C citations, Lemma 7.2 use, "112 controlled / 12 open" | CORRECT | TT Cor 1.6 (1708.02610): 1-bounded multiplicative g_0..g_k, product not weakly pretending to any χ, any shifts, ω_m ≤ x_m → ∞, full limit = 0. This fits the one-point terms, the two-point terms with a+b ≢ 0, and the three-point terms with a+b+c ≢ 0 (the product is g^{a+b+c}, covered by Lemma 7.1(ii)). Tao Cor 1.5 with g_1 = g^a (NP ⇒ (1.8) by Lemma 7.2) fits the two-point terms with a+b ≡ 0. **Term-by-term enumeration** of (Z/5)^3∖0: one-point 12; two-point sum ≢ 0: 36; two-point sum ≡ 0: 12; three-point sum ≢ 0: 52; T: 12, namely {(1,1,3),(1,2,2),(1,3,1),(2,1,2),(2,2,1),(2,4,4),(3,1,1),(3,3,4),(3,4,3),(4,2,4),(4,3,3),(4,4,2)}. This matches the six conjugate pairs of §7.0. 12+36+12+52 = 112 ✓. |
| 7 | Lemma 7.3 (diagonal invariance) | CORRECT | "Joint law" is well defined only along subsequences, and the lemma says so. Existence of such subsequences follows from compactness of the simplex on μ_5^3 (finite). Stronger than stated: every sequence x → ∞ has a sub-subsequence along which the identity holds, so δ_x(zero runs) − (1/5)δ_x(diagonal) → 0 for the full log averages. Hence the limsup and liminf versions both hold. The formula (1/125)(1 + 2Re Σ_{6 reps} C) is correct, because T is closed under negation and C(−v) = conj C(v). |
| 8 | Lemma 7.4 (the 25-point measure) | CORRECT (typo) | Verified numerically. ν̂ = ζ^c·1[a+b+c=0]·1[b+3c=0], so its support is exactly {0} ∪ {(2c,2c,c)} = {(2,2,1),(4,4,2),(1,1,3),(3,3,4)} ⊂ T. So ν satisfies exactly the 112 vanishing conditions. It has 25 distinct atoms and no mass at (0,0,0). **Typo:** "t = 0 and 2t+1 = 0" should read "t = 0 and 3t+1 = 0". The conclusion "the 112 facts alone cannot close case C" is correct as stated. It concerns only this finite Fourier data. TT Thm 1.2(iii) isotypy, and dilation relations between different shift patterns, are extra arithmetic input that ν ignores. |
| 9 | Theorem 7.5 (G_5 ⟺ Λ(5,3) < ∞) | CORRECT WITH FIX (wording) | (⇒): cases A, B are unconditional (with item 4's fix), and G_5 is case C. So every f: N → Z/5 has a zero run. The sets {f : no zero run at r ≤ R} are clopen, nested and nonempty, so their intersection over R would be a run-free f. Hence Λ_comb(5,3) < ∞, and Λ ≤ Λ_comb by the elementary README bound. ✓ **(⇐) is not "trivial".** It needs the README Chebotarev direction: if g has no zero run, Chebotarev in Q(ζ_5, q_i^{1/5}) gives arbitrarily large p with f_p = u·f on primes ≤ R+2, so Λ(5,3) = ∞. (Independence of the q_i mod 5th powers in Q(ζ_5): [Q(ζ_5):Q] = 4 is prime to 5, so a norm argument applies. For general odd k, use Schinzel's abelian-radical theorem.) **Fix:** replace "trivial" by "by the Chebotarev lower bound in README (Λ = Λ_comb for odd k)". |
| 10 | §7.5 chain 1 ⇒ 2 ⇒ 3 ⇒ 4 | CORRECT | Σ_T C is real (conjugation-closed). By Lemma 7.3 the diagonal log density is (1/25)(1 + Σ_T C) + o(1). So limsup Re Σ_T > −1 ⇒ positive upper log density of the diagonal ⇒ positive upper log density of zero runs ⇒ at least one zero run. |
| 11 | Conditional theorem (X ⇒ Λ(k,3) < ∞, k odd) | CORRECT | (1) H = {j : g^j pretentious} is a subgroup: 0 ∈ H; g^{a+b} pretends to the product of the twisted characters (triangle inequality); g^{−a} = conj(g^a). So H = mZ/k with m \| k. (2) If some coordinate j ∉ H, then g^j is NP and μ_k-valued, so (1.8) holds by Lemma 7.2 and X kills the term. This covers mixed terms such as (a,b,c) with a ∈ H∖0 and b ∉ H, since X lets any one position carry (1.8). (3) Σ_{(a,b,c)∈H^3} g^a(n)g^b(n+1)g^c(n+2) = Σ_{a',b',c' ∈ Z/(k/m)} G^{a'}(n)G^{b'}(n+1)G^{c'}(n+2) = (k/m)^3·1[G-run at n], with G = g^m ∈ μ_{k/m}. The factor is right. After dividing by k^3, δ_x(g-runs) = m^{−3} δ_x(G-runs) + o(1) at every scale. (4) G is pretentious (m ∈ H), k/m is odd, and Case A (fixed) applies to μ_{k/m}-valued G, giving lower natural (hence lower log) density δ_G > 0. So the lower log density of g-runs is ≥ δ_G/m^3. It is not necessary that the G-runs found in Case A are g-runs. The averaging identity already gives the density of g-runs, and g-runs ⊂ G-runs trivially. The edge case m = k (G ≡ 1) gives density 1/k^3. The compactness step is as in item 9 (for the upper bound only; no Chebotarev needed). |
| 12 | Novelty / overclaim | CAUTION (no error) | A brief search found no explicit statement of "log-Elliott ⇒ Λ(k,3) < ∞ for odd k". The argument is a routine combination of the pretentious/NP dichotomy with CRT on the pretentious side. The same template appears for ±1 runs in KMT §2.2/§9 (Hudson's conjecture, density version) and in You, arXiv 2404.04981 ("under Elliott's conjecture" constructions of length-k functions). **Recommendation:** in any public text, present the conditional theorem as "we record the (presumably folklore) deduction" rather than as a new result. The genuinely new content of §7 is the *unconditional* reduction Theorem 7.5 (cases A and B closed), together with the exact identification of the 12-term gap and Lemma 7.4. §7's own "the literature does not settle Λ(5,3)" is accurate. |

**Net effect on §7's claims.**
- Case A: proof valid after replacing M = L^{5j+1} by M = qL^{5j+1}.
- Case B: valid as written (modulo the h ∈ N shift remark).
- Case C bookkeeping: 112 controlled, 12 open, confirmed.
- Theorem 7.5: holds, with (⇐) credited to Chebotarev.
- Conditional theorem for all odd k: holds.
- Lemma 7.4 typo: 2t+1 → 3t+1.

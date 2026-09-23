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

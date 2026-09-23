# Erdős #132, angle B3: convex n = 7 and n = 11 (and 13), via an ordinal SAT/exhaustive search

(2026-09-23. Continues `angle_B2.md`; same notation. P is a strictly convex n-set, m = ⌊n/2⌋, D = D(P),
μ(d) = multiplicity, *rare* = 1 ≤ μ ≤ n, *frequent* = μ ≥ n+1, k = #rare, F = #frequent.)

## 0. Summary

| # | Statement | Status |
|---|---|---|
| 1 | **Thm 7.** Every strictly convex 7-set has k ≥ 3. | **proved, twice**: (a) corollary of published results (Altman + Erdős–Fishburn 1995 §3, which quotes Fishburn's DIMACS report 92-17); (b) independent computer proof from counting + the quadrilateral inequality only. Proof (b) has an exhaustive pure-Python search and a checked DRUP refutation. |
| 2 | **Thm 11.** Every strictly convex 11-set has k ≥ 3. | **proved (computer-assisted)**: counting + quadrilateral inequality + a SAT refutation. The refutation is found by 4 solvers and checked by our own RUP checker (§4). **Not implied by the literature**: r₂⁽ⁿ⁾ is unknown for n ≥ 9. |
| 3 | **Thm 13.** Every strictly convex 13-set has k ≥ 3. | **proved modulo trusting the solver on one instance**. Everything is certified except (13,7,5), which CaDiCaL and Glucose both report UNSAT; its DRUP check was stopped unfinished (Python checker too slow; needs drat-trim). |
| 4 | n = 15 | D ≤ 7 cases refuted (CaDiCaL). The hard case (15,8,6) was unresolved after more than 20 min of CaDiCaL at commit time. |
| 5 | **Ordinal phenomenon.** For 7 ≤ n ≤ 13 the whole statement follows from the *ordinal* quadrilateral inequality alone. No circle/triangle rigidity and no Altman/Fishburn is needed. It also reproves Altman's D ≥ ⌊n/2⌋ ordinally for n ≤ 15. It fails at n = 5, 6: ordinal counterexample colourings exist there, and geometry must be used. | computational observation; Conjecture Q-ORD (§5) |
| 6 | Reconfirmations without the Fishburn / Erdős–Fishburn classifications: n = 9 (B2 Thm B), and even n = 8, 10, 12 (B2 Thm A). | computer (SAT; n = 9 also DRUP-checked) |

**Net effect on #132 (b), convex case.** k ≥ 3 now holds for every convex n with 6 ≤ n ≤ 13:
- even n: B2 Thm A;
- n = 7: this note, and already in the literature;
- n = 9: B2 Thm B, and this note;
- n = 11, 13: this note.

For odd n ≥ 15 the question is still the single K = 1 configuration of B2 Prop B.

## 1. The ordinal model

Label P = (p_0, …, p_{n−1}) in convex cyclic order. Let d_1 < … < d_D be the distinct distances, and colour each
pair {i,j} with c(ij) = t where |p_ip_j| = d_t. Colour D is the diameter.

**Lemma Q (quadrilateral inequality).** For i < j < k < l (cyclic order), the diagonals ik, jl satisfy
|ik| + |jl| > |ij| + |kl| and |ik| + |jl| > |jk| + |li|.

*Proof.* The diagonals of the strictly convex quadrilateral p_ip_jp_kp_l meet at an interior point O. Then
|ik| + |jl| = (|iO| + |Oj|) + (|kO| + |Ol|) > |ij| + |kl|, strictly, because O is not on segment ij or kl.
The other inequality is the same argument. ∎

*Ordinal form.* Sort the two diagonal colours as x_1 ≤ x_2 and the two colours of one pair of opposite sides as
y_1 ≤ y_2. Then it is **not** the case that x_1 ≤ y_1 and x_2 ≤ y_2. Otherwise the matching x_1↔y_1, x_2↔y_2 gives
|ik| + |jl| ≤ |ij| + |kl| (or the other pair).

Special case: two vertex-disjoint diameter pairs must cross (Hopf–Pannwitz's key step). This is **not** added
separately, and **Hopf–Pannwitz is not assumed**: the diameter is not required to be rare.

**Lemma T (triangle rigidity; used only as an optional extra constraint).** For a pair {i,j}, let w ≠ w′ lie on
the same open boundary arc between i and j, hence strictly on the same side of line p_ip_j. Then
(c(iw), c(jw)) ≠ (c(iw′), c(jw′)). A point is determined by its distances to p_i, p_j and a side of the line.

**Lemma R (reduction to profiles).** Let N = C(n,2). If k ≤ 2, then:
- at least D − 2 colour classes have size ≥ n+1;
- D ≤ D_max(n), the largest D with (D−2)(n+1) + 2 ≤ N.

For n = 7, 11, 13, 15, D_max = 4, 6, 7, 8. For n = 2m+1 in general, D_max = m+1, which is B2 §1.

*Proof.* Rare classes number ≤ 2, and each class has ≥ 1 pair. So (D−2)(n+1) + 2 ≤ N. ∎

So to prove k ≥ 3 for a given odd n, it suffices to show the following. **For every 2 ≤ D ≤ D_max, no colouring of
the pairs of a convex n-gon with exactly D colours (all used) satisfies Lemma Q and has ≥ D−2 classes of size
≥ n+1.** (D = 1 is impossible for n ≥ 4.) We call such a colouring a *(n, D, F = D−2) ordinal counterexample*.
Where Altman is available (D ≥ m), the D < m cases can be skipped. We check them anyway, so no citation is
needed.

Lemma Q is necessary for geometric realisability. So "no ordinal counterexample" is a complete proof, and no
realisation or algebraic step is required. **No floating point enters any proof below.** Floats appear only in the
sanity script `b3_validate.py`.

## 2. Theorem 7

**Theorem 7.** Every strictly convex 7-point set has at least 3 distances occurring at most 7 times.

**Proof (a), from the literature.**
- Erdős–Fishburn, *Intervertex distances in convex polygons*, DAM 60 (1995) 149–158, §3, quote Fishburn,
  *Convex polygons with few vertices*, DIMACS report 92-17 (1992). The maximum second-largest multiplicity in a
  convex n-gon is r₂⁽ⁿ⁾ = 1, 3, 5, 6, 7, 8 for n = 3, …, 8. So in a convex heptagon at most one distance occurs
  more than 7 times, i.e. k ≥ D − 1.
- Altman (Amer. Math. Monthly 70 (1963)) gives D ≥ 3, with D = 3 only for R_7. R_7 has profile (7,7,7), so k = 3.
- D ≥ 4 gives k ≥ 3. ∎

The r₂⁽⁷⁾ = 7 value rests on an unrefereed technical report, quoted in a refereed paper. The same paper, Thm 1,
gives M₇(4) = {R₈ − 1, the four R₉ − 2}, all cocircular. With B2 Prop B (D = 4, two classes ≥ 8), this gives a
second literature proof: cocircular sets have every class ≤ n.

**Proof (b), self-contained (computer-assisted).** By Lemma R with D_max = 4, it suffices that there are no
(7,2,0), (7,3,1) or (7,4,2) ordinal counterexamples.
- `scripts/b3_enum.py 7 D` is a plain backtracking search over all 4^21 (resp. 3^21, 2^21) colourings. Constraints
  are checked as soon as their pairs are assigned, and the result is reduced by the dihedral group.
- It finds **0 colourings** for D = 2, 3, 4. With Lemma T switched off (`noT`), the D = 4 search visits 6.86·10⁶
  nodes and also finds 0. So **Lemma Q alone suffices**.
- Cross-checks:
  - `b3_sat.py 7 D D−2`: UNSAT with CaDiCaL 1.5.3, Glucose 4, MiniSat 2.2 and Lingeling, under both clause
    encodings.
  - `b3_drup_check.py 7 4 2 Q`: Glucose's DRUP proof (712 lemmas) is verified by our own RUP checker. ∎

Remark: with F = 1, colourings exist for (7,4,1) (e.g. profile (8,6,4,3)). So "at most one frequent class" is
*not* an ordinal consequence of Q. Fishburn's r₂⁽⁷⁾ = 7 is stronger than what we reprove: we reprove only the
k ≥ 3 consequence.

## 3. Theorems 11 and 13

**Theorem 11.** Every strictly convex 11-point set has at least 3 distances occurring at most 11 times.

*Proof.* Lemma R with D_max = 6. Ordinal counterexamples do not exist for any of:
- (11,2,0), (11,3,0), (11,4,0) — no Q-colouring at all with ≤ 4 colours (an ordinal Altman);
- (11,5,3);
- (11,6,4).

All five are UNSAT (table in §4). Each refutation is certified by a DRUP proof from Glucose 4, checked by the
independent checker in `b3_drup_check.py`. ∎

Two notes on the certificates:
- The (11,6,4) certificate is for the Q-only encoding, so again **Lemma Q alone suffices**.
- Note that (11,6,3) is SAT, e.g. profile (12,9,12,12,6,4). So one frequent class fewer is realisable ordinally,
  and the method is tight at "k ≥ 3".

**Theorem 13.** Every strictly convex 13-point set has at least 3 distances occurring at most 13 times.

*Proof.* Lemma R with D_max = 7. The following are all UNSAT (CaDiCaL):
- (13,D,0) for D = 2, …, 5;
- (13,6,4), under two encodings;
- (13,7,5), under both the Q+T and the Q-only order encodings. ∎

Status:
- (13,6,4) is certified by DRUP.
- (13,7,5) is so far solver-only; §6 has the details.

### What this does not rely on

Nothing about the realisation space is used: no Fishburn, no Erdős–Fishburn, no Altman, no Hopf–Pannwitz, no Cap
Lemma. The only geometric input is Lemma Q (and optionally Lemma T).

## 4. Computations

All scripts are in `scripts/`. `b3_run_all.sh` reproduces everything. Run with `uv run --with python-sat python <script> …`.
- `b3_enum.py` needs only the standard library.
- Times are on an 8-core laptop.

| instance (n, D, F) | encoding | result | solvers | DRUP check (`b3_drup_check.py`) |
|---|---|---|---|---|
| (7,2,0), (7,3,1), (7,4,2) | {direct, order} × {Q+T, Q-only} | UNSAT: 48/48 solver runs | all 4 solvers + `b3_enum` (0 colourings; for (7,4,2) with and without T) | verified; (7,4,2): 704 lemmas (Q+T), 712 (Q-only) |
| (7,3,0) | — | SAT: exactly 1 dihedral class, the R₇ pattern (`b3_enum`, `b3_validate`) | | |
| (7,4,1) | Q-only | SAT (e.g. (5,8,3,5)) | | |
| (9,2,0), (9,3,0), (9,4,2), (9,5,3) | direct, order, Q-only | UNSAT | glucose, minisat, lingeling (direct), cadical (Q-only / order) | (9,5,3) verified, 3661 lemmas |
| (9,5,2) | | SAT, (10,4,10,5,7) | | |
| (11,2..4,0) | direct, order, Q-only | UNSAT | all 4 | verified (1, 6, 54 lemmas) |
| (11,5,3) | direct, order, Q-only | UNSAT | all 4 | verified, 522 lemmas |
| (11,6,4) | direct (437,890 clauses), order, Q-only | UNSAT (8–114 s) | all 4 | **verified**: Q-only 35,508 lemmas (903 s); Q+T 24,928 lemmas (604 s) |
| (11,6,3) | | SAT, (12,9,12,12,6,4) | | |
| (13,2..5,0) | order, Q+T and Q-only | UNSAT (≤ 1 s) | cadical | — |
| (13,6,4) | direct, order, Q-only order | UNSAT (106 s / 6 s / 3 s) | cadical, glucose | **verified**, Q-only, 5,534 lemmas (119 s) |
| (13,7,5) | order Q+T / order Q-only | UNSAT (102 s / 81 s) | cadical, glucose (446,686-line proof) | check running at commit time (Python checker, est. hours) |
| (15,2..6,0) | order Q+T and Q-only; (15,6,0) also direct | UNSAT (≤ 142 s) | cadical | — |
| (15,7,5) | order Q+T | UNSAT (83 s) | cadical | — |
| (15,8,6) | order Q+T (7.3·10⁵ clauses); the direct encoding (5·10⁶ clauses) was abandoned | unresolved (> 20 min CaDiCaL; run stopped) | | |
| even: (6,2,0), (8,2..3,0), (8,4,2), (10,2..4,0), (10,5,3), (12,2..5,0), (12,6,4) | direct Q+T | UNSAT (≤ 68 s) | cadical | — |
| (6,3,1) | | SAT, (9,3,3) — ordinal counterexample; geometry (Fishburn / Erdős–Fishburn) needed at n = 6 | | |
| (5,2,0), (5,3,1) | | SAT (R₅ pattern, etc.) | | |

**Encoding** (`b3_sat.py`). Variables x[e,c]; exactly-one colour per pair; Lemma T clauses; Lemma Q clauses.
- *Direct* Q: forbid each dominated 4-tuple of colours.
- *Order* Q: literals y[e,t] ⇔ c(e) ≥ t, then forbid "c(a) ≤ t ≤ c(b) and c(a′) ≤ u ≤ c(b′)" for both
  diagonal↔side matchings. This is equivalent, because sorted domination holds iff some matching dominates.
- Every colour is used.
- Selector f_c → (#pairs of colour c ≥ n+1) via sequential counters, and Σ f_c ≥ F.

**Validation of the encoding / constraints.**
1. `b3_validate.py`:
   - every 7-subset of V(R_N), 7 ≤ N ≤ 16 (11,440 sets), and every 11-subset of V(R_N), N ≤ 15, satisfies all
     constraints, with exact integer chord-index ranks;
   - so do 3000 (n = 7) and 500 (n = 11) random generic convex polygons;
   - the (7,3,0) enumeration returns exactly the R₇ colouring.
2. Every SAT model printed by `b3_sat.py` is re-checked against the independent constraint code of `b3_enum.py`
   (all OK; 10 instances in the log).
3. `b3_enum` (backtracking, no SAT) and `b3_sat` (4 solvers × 2–3 encodings) agree on every n = 7 instance.
4. `b3_drup_check.py selftest`: the RUP checker rejects a bogus empty proof of a satisfiable instance, a proof with
   one lemma negated, and a truncated proof, and it accepts the genuine one.
5. Deletions in the DRUP proof are ignored. This is sound, because every retained clause is implied by the CNF.

## 5. The ordinal phenomenon and general odd n

**Conjecture Q-ORD.** For every n ≥ 7, every colouring of the pairs of a convex n-gon by an ordered colour set that
satisfies the ordinal quadrilateral inequality has at least 3 colour classes of size ≤ n.

Verified for 7 ≤ n ≤ 13. For n = 15, every case except (15,8,6) is verified; that one is unresolved so far.

Q-ORD would prove "k ≥ 3" for all convex sets with n ≥ 7, and Theorem A of B2 would not be needed. It is a purely
extremal-combinatorial statement about "anti-Monge" colourings of K_n in cyclic order. Its "ordinal Altman" part
(no Q-colouring with < ⌊n/2⌋ colours) is also verified, with Q alone, for odd n ≤ 15 ((n, D, 0) UNSAT for all D ≤ m−1). This is consistent
with Altman's proof, whose Lemma 1 is essentially an ordinal consequence of convexity.

Why Q-ORD is plausible, and where it could fail:
- **Tightness.** F = D−3 is SAT at (9,5,2) and (11,6,3). So Q-ORD cannot give k ≥ 4 at these n.
- **Small n.** At n = 6, (6,3,1) is SAT with profile (9,3,3). Geometry kills it: Fishburn's M₆(3) has profiles
  (6,6,3), (5,5,5) and R₇−1. So Q-ORD genuinely needs n ≥ 7.
- **Literature caveat.** Erdős–Fishburn 1995 Thm 2 build a convex 25-gon with r₁ ≥ r₂ = 26 > n. So two frequent
  classes can coexist in convex position. That is compatible with k ≥ 3 but shows the frequent structure grows.
  An ordinal proof for large n must allow F ≈ m−1 frequent classes, all ordinally consistent.

**What blocks n = 15 and beyond computationally.**
- The instances grow like C(n,4)·D² clauses (order encoding), about 7·10⁵ at (15,8,6), and the hard instance is
  always (n, m+1, m−1).
- Solve times rise about 10× per step of 2 in n: (11,6,4) ~6 s, (13,7,5) ~100 s, (15,8,6) > 20 min so far.
- Symmetry breaking (dihedral lex-leader) and cube-and-conquer would buy a few more n. They cannot reach all n,
  which needs a human proof of Q-ORD.
- A natural first target is the structure the SAT solver exploits. `b3_core.py` extracts a deletion-minimal set of
  4-subsets whose Q-constraints already refute an instance:
  - (7,4,2) needs **25 of the 35** quadrilaterals;
  - (7,3,1) needs 14 of 35.

  So there is no small local obstruction, and a human proof of Q-ORD will have to be global, e.g. Altman-style
  chain/summation arguments made ordinal.

## 6. Black boxes, trust, gaps

- **n = 7:** no black box in proof (b) beyond the ~150-line enumerator, and a checked DRUP certificate as well.
  Proof (a) cites Altman 1963 and Fishburn's DIMACS 92-17, via Erdős–Fishburn 1995.
- **n = 11:** trusts the CNF encoder `b3_sat.build`, which is short, and cross-validated as in §4. The solver is
  *not* trusted: the DRUP proofs are checked by `b3_drup_check.py`, a ~100-line forward RUP checker that we wrote.
  It is not a formally verified checker such as cake_lpr or drat-trim. **Gap:** re-check with drat-trim, and/or dump
  the CNF and proof files, which were not saved to the repo (the proof for (11,6,4) is ~60k lines).
- **n = 13:** (13,≤5,0) and (13,6,4) are certified or trivial. (13,7,5) has solver trust only: CaDiCaL and
  Glucose, two encodings. **Gap:** finish `b3_drup_check.py 13 7 5 Q` (446k proof lines; the Python checker needs
  hours), or better, run drat-trim.
  - Note: the (13,2..5,0) instances were run with CaDiCaL only and not DRUP-checked. Altman covers them anyway
    (D ≥ 6 for n = 13).
- **n = 15:** the (15,≤7,·) instances rest on solver trust only. (15,8,6) is open.
- **Encoding soundness** is the one non-mechanised step: the claim that the CNF says exactly "Lemma Q (+T) +
  profile". §4 lists the checks.
- **Novelty.** Thm 7 is a corollary of known results (Audit 3 in `NOVELTY.md`). Thms 11 and 13 are, as far as the
  four Erdős–Fishburn/Fishburn papers and the forum material go, new. Neither r₂⁽¹¹⁾ ≤ 11 nor a classification of
  convex 11-gons with 6 distances is known: Erdős–Fishburn's Cor. 1 leaves f(11) open. The ordinal reduction (Q
  alone suffices) is, to our knowledge, not in the literature. This was not audited per PROMPT rule 4.

## 7. Independent re-certification with drat-trim (2026-09-23, parent session)

`scripts/b3_drat_trim.py` rebuilds each CNF with `b3_sat.build(..., order_Q=True)` and writes it with a Glucose 4
DRUP proof. The proof is then checked by **drat-trim**, the standard backward checker (Heule,
github.com/marijnheule/drat-trim, built from source). drat-trim also emits an **LRAT** proof (`-L`), which is
re-checked by **lrat-check** from the same repo. LRAT is the format that Lean's verified SAT-checking
infrastructure consumes.

| instance | lemmas | drat-trim | lrat-check |
|---|---|---|---|
| (7,4,2) Q | 714 | s VERIFIED | VERIFIED |
| (11,2,0) TQ | 3 | s VERIFIED | VERIFIED |
| (11,3,0) TQ | 8 | s VERIFIED | VERIFIED |
| (11,4,0) TQ | 56 | s VERIFIED | VERIFIED |
| (11,5,3) TQ | 524 | s VERIFIED | VERIFIED |
| (11,6,4) Q | 35,510 | s VERIFIED | VERIFIED |

Negative control: a truncated (11,6,4) proof gives `s NOT VERIFIED`. So **Theorem 11 is certified by two
independent checkers**, trusting only the encoder `b3_sat.build`. CNF, proof and LRAT files are regenerated
deterministically by the script; they are not stored in git because of their size.

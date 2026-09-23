# Λ(5,3) lower bound by warm-started local search (2026-09-23)

**Result: Λ(5,3) ≥ 100,009,485** (previous best: 5,750,107, from kissat on S(5,750,000)).
The certificate is a completely additive f: Z_{>0} → Z/5 whose first zero triple f(r)=f(r+1)=f(r+2)=0
is at r = 100,009,485. By the reduction in README.md ("Definition ↔ combinatorial model", lower
bound via Chebotarev, k odd), this gives Λ_comb(5,3) ≥ 100,009,485 and hence Λ(5,3) ≥ 100,009,485.
A model found by any method gives a valid lower bound. Nothing here gives an upper bound: a failure of
the local search says nothing about Λ.

## Method
The full-instance CDCL route stalls above 5.75M: all earlier SAT results came from kissat's
0-conflict "lucky" phase, and real search on the 6.8M-var CNF runs at ~10 conflicts/s. So I did not
use a SAT solver. Instead, `scripts/warmls.c` does a special-purpose local search on the prime values
directly:

- State: f(p) ∈ Z/5 for every prime p ≤ N = R+2. Composite values follow by additivity. The objective
  is the number of bad r ≤ R (zero triples).
- Warm start: prime values from a previous model (map + "v"-line model). Primes not listed get
  f(p) = 1, the same convention as `lamenc run`.
- Move: pick a random bad window r. The candidates are the primes p ≥ PMIN dividing r, r+1 or r+2
  with v_p ≢ 0 (mod 5). Candidates are scanned from the largest down. One pass over the multiples
  of p scores all four deltas: each window meeting a multiple of p becomes bad for at most one delta.
  First-improvement: once an improving move is found, primes < 1000 are skipped.
- Escaping local minima: breakout clause weighting. If no candidate has negative *weighted* gain for
  window r, the weight of r is bumped and no move is made. Also a short tabu per prime. No random
  noise (noise=0 worked best; random moves on small primes do heavy damage).
- Chaining: `scripts/warmchain.sh` runs warmls for an increasing list of R. Each run is warm-started
  from the previous result. Each result is decoded by two independent programs (below), and a line
  is appended to `logs/probes/status.tsv`.
- Memory is ~5 bytes per unit of N (int32 largest-prime-factor sieve + f). Weight, bad-set and tabu
  arrays are calloc'd and touched lazily; RSS was ~1.9 GB at R = 1.5e8.

## Verification
Every reported result was decoded twice, from the same output files (synthetic map "p base" for
all primes ≤ N with f(p) ≠ 1, and a "v"-line model):
1. `scripts/lamenc run 5 3 LIM map model`: the existing decoder (largest-prime-factor recursion,
   primes not in map := 1).
2. `scripts/checkf.py 5 3 LIM map model`: an independent numpy implementation (smallest-prime-factor
   sieve, vectorised additive extension). It shares no code with lamenc.c or warmls.c and rejects
   any prime with 0 or ≥ 2 true value literals.
Both print the first zero triple r ≤ LIM. They agreed at every step. Before this, checkf.py was also
checked against lamenc on the original 5.75M kissat model (both give 5,750,107).
warmls also has a debug mode (`WARMLS_DEBUG=1`). It checks after every move that the predicted gain
equals the actual change in the bad count. It was run on the R = 6.0M step without mismatches.

The certificate for the best bound is in `logs/warmstart/k5l3_first100009485.{map,model}.gz`
(sha256 of the uncompressed files: map 8c99e31f…85ac, model 512ab412…39d2). To reproduce the check:
`gunzip -k *.gz; scripts/lamenc run 5 3 101000000 k5l3_first100009485.map k5l3_first100009485.model`
→ `100009485` (and the same with `python3 scripts/checkf.py`).

## Chain (each row is warm-started from the row above; times are wall clock on a loaded 8-core Mac)
| target R | initial bad windows in (prev, R] | steps | time | first zero run (both decoders) |
|---|---|---|---|---|
| 6,000,000 (from the kissat 5.75M model) | 619 | 6,525 | 107 s (debug mode) | 6,000,730 |
| 6,500,000 | 913 | 894 | 4 s | 6,500,096 |
| 7,000,000 | 952 | 893 | 3 s | 7,000,020 |
| 7,600,000 | 1,111 | 1,033 | 5 s | 7,600,716 |
| 8,500,000 | 1,683 | 1,569 | 2 s | 8,500,058 |
| 10,000,000 | 2,869 | 9,426 | 100 s | 10,000,150 |
| 12,000,000 | 3,298 | 7,414 | 89 s | 12,000,195 |
| 15,000,000 | 3,890 | 5,308 | 42 s | 15,000,075 |
| 20,000,000 | 5,641 | 5,703 | 27 s | 20,000,330 |
| 30,000,000 | 9,086 | 18,501 | 461 s | 30,000,887 |
| 45,000,000 | 9,591 | 7,894 | 41 s | 45,000,953 |
| 70,000,000 (seed 3, PMIN 100) | 12,260 | 27,397 | 481 s | 70,005,949 |
| 100,000,000 (seed 5, PMIN 300) | 9,392 | 16,100 | 154 s | **100,009,485** |

Rows up to 45M: seed 1, PMIN 30. At 70M, seed 1 / PMIN 30 got stuck at 1 bad window for 20+ min
and was killed; seed 2 / PMIN 30 was also stuck when seed 3 / PMIN 100 finished.
RESULTS_ABOVE_1E8

## Observations
- After warm starting, the new range (R_prev, R] contains only ~1/400 (at 6M) down to ~1/2000 (at 70M)
  bad windows. Almost all of them are fixed in a single move by changing one large prime factor,
  which has few multiples and therefore almost no side effects.
- All the time goes into the last 1–5 windows, and they are always *smooth* windows (every prime
  factor of r, r+1, r+2 ≤ ~5000; e.g. r = 117,951,525 = 3³·5²·17·19·541, r+1 = 2·7⁵·11²·29,
  r+2 = 163·769·941). Every move on such a window touches ≥ 10⁵ other windows. Breakout weighting
  eventually escapes; the time to do so varies strongly by seed (41 s to 480+ s at the same scale).
- The values on primes ≤ 100 were never changed (PMIN ≥ 30, and nothing below 100 was ever the
  best move). The 5.75M model's f(p) for p ≤ 100 extends to at least 1e8. Of the 208,450 primes
  ≤ 2.875M, 40,372 changed value by the 45M step (26 of them below 1000). Effectively, the P0 = 100
  "fix small primes" warm start is satisfiable up to ≥ 1e8.
- Why the SAT-with-unit-clauses variant (fix f(p) for p ≤ P0 in the CNF) was not run: the local
  search passed the whole target range (5.8M–7.6M) in seconds, so a SAT experiment would add nothing
  to the bound. The encoder's CNF is ~1 GB at R = 7.6M (and ~13 GB at 1e8), so it cannot scale into
  the range reached here within the disk and RAM limits.

## What this does and does not say
- The lower bound is rigorous given the two decoders and the (already documented) reduction.
- The ease of extension (the growth of first-run with R is limited only by run time and RAM) is weak
  heuristic evidence that Λ(5,3) is very large or infinite. It is not evidence of anything provable.
  Local search can never show S(R) UNSAT.

## Next steps
1. Longer chains above 1e8 need a segmented (lpf-free) version of warmls/checkf/lamenc run.
   Memory is now dominated by the 4-byte lpf sieve; factoring on demand plus a segmented pass for f
   would give ~1 byte per N.
2. Speed up the smooth-window tail: compound moves (change a small prime, then greedily repair the
   windows it breaks, and accept the pair if the net gain is negative), or a small exact sub-solve.
   For the sub-solve, fix everything except the primes dividing the stuck windows plus the
   large-prime factors of the windows they would break, and hand that small CNF to CaDiCaL.
3. The structure is striking: f = 0 on most p ≤ 100, and fixes come from large primes. It might
   suggest an explicit infinite family (a construction with no zero triple at all would give Λ(5,3) = ∞).

# Λ(5,3) lower bound by warm-started local search (2026-09-23)

**Result: Λ(5,3) ≥ 2,000,028,671** (previous best: 5,750,107, from kissat on S(5,750,000)).

The certificate is a completely additive f: Z_{>0} → Z/5. Its first zero triple f(r)=f(r+1)=f(r+2)=0
is at r = 2,000,028,671. The f is given by its values on primes: primes not listed have f(p) = 1.
By the reduction in README.md ("Definition ↔ combinatorial model": for k odd, every assignment of
prime characters occurs, by Chebotarev), this gives Λ_comb(5,3) ≥ 2,000,028,671, and hence
Λ(5,3) ≥ 2,000,028,671. A model found by any method gives a valid lower bound. Nothing here gives an
upper bound, and a failure of the search says nothing about Λ.

Certificate: `logs/warmstart/k5l3_first2000028671.{map,model}.gz`. The map has lines "p base" and
the model has "v" lines, the same format as lamenc/kissat. f(p) = v iff literal base+v is true.
sha256 of the uncompressed files:
- map: 85e3c19a85f728621858a9274b12c58ea333cff635a533dad4036fa43367f02e
- model: 1bfef1c5e36144acc5a89c9ccceaee180580183f2476b15455e97841550af800

To check it:
```
gunzip -k logs/warmstart/k5l3_first2000028671.*.gz
scripts/segcheck 5 3 2001000000 k5l3_first2000028671.map k5l3_first2000028671.model   # 2000028671, ~2 min, 16 MB
python3 scripts/checkf.py 5 3 2001000000 k5l3_first2000028671.map k5l3_first2000028671.model  # 2000028671, ~5 min
```
(`cc -O2 -o scripts/segcheck scripts/segcheck.c` first; `lamenc run` needs ~5 bytes per n, i.e. ~10 GB here.)

## Method
Why not SAT: the full-instance CDCL route stalls above 5.75M. All earlier SAT results came from
kissat's 0-conflict "lucky" phase, and real search on the 6.8M-var CNF runs at ~10 conflicts/s.
The planned SAT warm start (unit clauses or phases for p ≤ P0) was therefore not run: the local
search below passed the whole 5.8M–7.6M target range in seconds. The CNF is also ~1 GB at 7.6M and
would be ~300 GB at 2e9.

Two levels of local search work directly on the prime values:

1. **`scripts/warmls.c`, the full instance up to R.** It works on the values f(p) for primes p ≤ N = R+2;
   composite values follow by additivity. The objective is the number of zero triples r ≤ R.
   - Warm start from a previous map/model.
   - Each step picks a random bad window r. The candidate moves are primes p ≥ PMIN dividing r, r+1 or
     r+2 with v_p ≢ 0 (mod 5), scanned from the largest prime down. One pass over the multiples of p
     scores all four deltas, first-improvement.
   - At local minima: a compound "kick" (a worsening move plus greedy strictly improving repairs,
     rolled back if not a net gain), then breakout weighting (raise the window's weight).
   - Memory is ~1.2 bytes per N: f array, prime bitset, segmented recomputation of f, trial-division
     factoring, and hash maps for the sparse per-window and per-prime data. R = 2e9 fits in ~2.4 GB.
2. **`scripts/smoothfix.py`, the small primes.** Every stall of level 1 was a window of three
   consecutive y-smooth numbers, e.g. r = 193,750,000 = 2⁴·5⁸·31, r+1 = 373·521·997,
   r+2 = 2·3³·43·181·461. Fixing it needs a prime ≤ ~1000, and at N ~ 1e8 that prime has ~1e5
   multiples, so level 1 cannot afford the move (breakout and kicks both stalled for 30–40 min).
   smoothfix runs min-conflicts with breakout on f(p), p ≤ y = 3000 (430 primes), against all
   3000-smooth triples r ≤ X (from `smoothruns`, 1.4M–2.7M triples). This is the F_y(X) instance of
   README.md. It starts from the current values and breaks ties toward changing large primes. Then
   warmls runs with PMIN = 3001, so primes ≤ 3000 stay fixed. The smooth windows are then all good
   up to X, and the collateral damage (6–18k bad windows) is repaired with large primes in seconds.

`scripts/warmchain.sh` chains warmls over a list of R. Each run is warm-started from the previous
result and double-decoded, and one line per step goes to `logs/probes/status.tsv`.

## Verification
Every reported bound was decoded by two programs from the same output files. Each program prints the
least r ≤ LIM with a zero triple:
- A: `scripts/lamenc run` (the original decoder, largest-prime-factor table) for R ≤ 5e8.
  Above 5e8 it was replaced by `scripts/segcheck` (new C code, segmented trial division by prime
  powers ≤ √N plus binary search in the map; O(segment) memory).
- B: `scripts/checkf.py` (numpy, segmented; its default mode is independent of lamenc.c and warmls.c).

Cross-validation of the verifiers:
- checkf and segcheck reproduce `lamenc run` on the original kissat models (1.5M, 2.25M, 3.375M,
  5.0625M, 5.75M → 5,750,107) and on 6,000,730, 300,001,271 and 500,003,685.
- checkf's segmented path equals its whole-range sieve path on 30 random f.
- `WARMLS_DEBUG=1` checks after every move and every kick rollback that the predicted change in the
  bad count equals the actual one. It ran with no mismatch at 6e6 and 7e6 (full runs) and at 3e7 (stopped unfinished after ~10 min).
- The committed .gz certificate was round-tripped through segcheck (2000028671).

## Chain
Each row is warm-started from the row above. Times are search wall-clock (verification is extra) on a
shared 8-core Mac.

| target R | start | initial bad windows | steps | search time | first zero run (A and B agree) |
|---|---|---|---|---|---|
| 6.0M | kissat 5.75M model | 619 | 6,525 | 107 s (debug) | 6,000,730 |
| 6.5M | | 913 | 894 | 3 s | 6,500,096 |
| 7.0M | | 952 | 893 | 2 s | 7,000,020 |
| 7.6M | | 1,111 | 1,033 | 3 s | 7,600,716 |
| 8.5M | | 1,683 | 1,569 | 2 s | 8,500,058 |
| 10M | | 2,869 | 9,426 | 99 s | 10,000,150 |
| 12M | | 3,298 | 7,414 | 88 s | 12,000,195 |
| 15M | | 3,890 | 5,308 | 42 s | 15,000,075 |
| 20M | | 5,641 | 5,703 | 27 s | 20,000,330 |
| 30M | | 9,086 | 18,501 | 460 s | 30,000,887 |
| 45M | | 9,591 | 7,894 | 40 s | 45,000,953 |
| 70M | seed 3, PMIN 100 | 12,260 | 27,397 | 480 s | 70,005,949 |
| 100M | seed 5, PMIN 300 | 9,392 | 16,100 | 152 s | 100,009,485 |
| 150M | seed 5, PMIN 300 | 11,215 | 39,310 | 746 s | 150,005,898 |
| 200M | smoothfix y=3000, X=3e8 (12 violated → 18 primes changed); PMIN 3001 | 8,363 | 6,620 | 4 s | 200,011,716 |
| 300M | | 8,386 | 6,682 | 6 s | 300,001,271 |
| 400M | smoothfix y=3000, X=1e9 (16 violated → 16 changed) | 8,724 | 6,765 | 8 s | 400,006,178 |
| 500M | | 4,124 | 3,532 | 7 s | 500,003,685 |
| 700M | | 6,752 | 5,426 | 17 s | 700,026,741 (A = segcheck from here) |
| 1.0e9 | | 7,830 | 6,165 | 31 s | 1,000,007,372 |
| 1.5e9 | smoothfix y=3000, X=2.1e9 (14 violated → 9 changed) | 12,618 | 8,691 | 42 s | 1,500,097,130 |
| 2.0e9 | | 6,222 | 5,043 | 41 s | **2,000,028,671** |

Rows up to 45M used seed 1 and PMIN 30. Runs that stalled and were killed (all logged in status.tsv):
- 70M: seed 1 and seed 2 with PMIN 30.
- 200M before the smooth fix: seeds 11 and 13, stuck at the two 1000-smooth zero triples
  170,225,196 and 193,750,000.
- 200M after the smoothfix at y=1000, X=1e9 with PMIN 1009: stuck at windows like r = 91,448, whose
  only candidate ≥ 1009 is 1129. Enlarging the kick (KICKMAX 400) did not help. Raising y to 3000 did.

## Observations
- After a warm start, the new range contains few bad windows: ~1/400 of the new range at 6M, and
  <1/10⁴ at the top. Almost all of them are fixed in one move by changing one large prime factor,
  which has few multiples and almost no side effects.
- The hard part is the finite, Størmer-type set of consecutive smooth triples. Once the small primes
  (≤ 3000) avoid every zero among 3000-smooth triples up to X, extending to R ≤ X took under a minute
  per step even at 2e9. Each smoothfix needed only 9–18 changed small primes, found in seconds.
- Primes ≤ 37 kept the kissat model's values throughout (f(2)=0, f(3)=1, f(5)=…=f(17)=0, f(19)=1,
  f(23)=f(29)=f(31)=0, f(37)=1). By 2e9, 7 primes in (37, 100] had changed (41, 47, 53, 59, 71, 83,
  89, all 0 → 1), as had 111 primes ≤ 3000 and 109,800 of the 208,450 primes ≤ 2.875M.
- The earlier P0 question: with this method, the model's values on p ≤ 100 were a valid warm start
  up to 1.5e8 with no changes at all, and on p ≤ 37 up to 2e9.

## What this does and does not say
- The lower bound is rigorous, given the documented reduction and the two agreeing decoders.
- Extending the bound was easy and fast at every scale tried (no stall that raising y did not cure).
  That is weak heuristic evidence that Λ(5,3) is very large or infinite. It is not evidence of
  anything provable, and local search can never show S(R) UNSAT.

## Next steps
1. Going past 2^31 needs 64-bit window indices in warmls (badlist) and more RAM (~1.2 bytes per N).
   Alternatively, add a windowed mode that only keeps f on (R_prev − margin, R]: it would need
   segmented recomputation, since a prime's multiples span the whole range. smoothfix at X > 2e9
   would also need a leaner (CSR) representation (3.1 GB peak at 2.7M triples).
2. The two-level structure (a finite smooth core plus an easy large-prime layer) suggests the real
   question is whether F_y(∞) (finite by Størmer) is satisfiable for every y with consistent choices.
   If some y makes F_y(∞) UNSAT, that proves Λ(5,3) < ∞. The README estimates ~1e18 nodes for y ≤ 1000.
   The smoothfix solutions found here show F_3000(2.1e9) is SAT, hence also F_1000(1e9)
   (every 1000-smooth triple is 3000-smooth). This settles the README's unresolved F_1000(1e9)
   cube runs: they were SAT, not UNSAT.
3. The structure of f on small primes (0 on most p ≤ 37, 1 on most larger primes) might suggest an
   explicit infinite construction, which would give Λ(5,3) = ∞.

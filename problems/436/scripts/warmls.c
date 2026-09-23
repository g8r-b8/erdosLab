// warmls: warm-started local search (min-conflicts repair) for S(R), k = 5 (any odd k), l = 3.
//
// Goal: find a completely additive f: Z_{>0} -> Z/k with no l-run of zeros f(r)=...=f(r+l-1)=0
// for any r <= R, starting from an existing SAT model (e.g. the kissat model of S(5,750,000)).
// Any such f gives Lambda_comb(k,l) >= (first zero run of f) >= R+1, hence (Chebotarev, k odd)
// Lambda(k,l) >= R+1.  Only primes <= N = R+l-1 matter.
//
// Search space: the values f(p) in Z/k for primes p <= N (f(n) for composites follows by additivity,
// f(n) = f(P(n)) + f(n/P(n))).  Objective: number of "bad" r <= R (zero runs).  Move: change f(p) for
// one prime p >= PMIN dividing some member of a bad run; the effect of every delta in Z/k is scored
// in a single O(N/p) pass over the multiples of p.  Min-conflicts with noise + tabu tenure.
//
// Usage:
//   warmls K L R MAP MODEL OUTMAP OUTMODEL [PMIN] [SEED] [MAXSTEPS] [NOISE_PERMILLE]
//     MAP/MODEL   : lamenc map ("p base") + solver model ("v ..." lines) for the warm start;
//                   primes absent from MAP start at value 1 (same convention as `lamenc run`).
//     OUTMAP/OUTMODEL: result in the same format (synthetic map: every prime <= N with f(p) != 1,
//                   base = K*i+1; model = "v" lines with the true literal base+f(p)), so it can be
//                   decoded by `lamenc run K L LIM OUTMAP OUTMODEL` and by scripts/checkf.py.
//   Progress lines go to stderr.  Exit 0 if a run-free f up to R was found, 1 otherwise.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef struct {
  int K, L;            // modulus and run length (L = 3 supported)
  long R, N;           // runs r <= R are forbidden; N = R + L - 1
  int32_t *lpf;        // largest prime factor, lpf[n] for 2 <= n <= N
  uint8_t *f;          // f[n] in Z/K for 1 <= n <= N (f[1] = 0)
  uint8_t *fp;         // shadow copy not needed; f[p] holds prime values
  long *badlist;       // list of bad r
  long *badpos;        // position of r in badlist, or -1
  long nbad;
  uint32_t *tabu;      // tabu[p] = step until which p may not be changed (indexed by prime)
  long pmin;
  uint64_t rng;
} State;

/* sieve_lpf
 * TODO: fill lpf[n] = largest prime factor of n for 2 <= n <= N.
 * What's missing: body.
 * Acceptance: lpf[p] == p iff p prime; lpf[12] == 3; lpf[1] unused.
 * Depends on: nothing.
 */
static int32_t *sieve_lpf(long N) {
  (void)N;
  fprintf(stderr, "NotImplemented: sieve_lpf\n"); exit(3);
}

/* load_warm
 * TODO: set f[p] for every prime p <= N from MAP/MODEL (true literal base+v => f(p) = v);
 *       primes not in MAP get 1.
 * What's missing: body (read "p base" lines; read "v" lines of the model; tolerate primes > N in MAP).
 * Acceptance: on the 5.75M model, recomputing f and finding the first zero run gives 5,750,107
 *             (same as `lamenc run`).
 * Depends on: sieve_lpf.
 */
static void load_warm(State *s, const char *map, const char *model) {
  (void)s; (void)map; (void)model;
  fprintf(stderr, "NotImplemented: load_warm\n"); exit(3);
}

/* compute_f
 * TODO: f[n] = f[lpf[n]] + f[n/lpf[n]] mod K for composite n, increasing n.
 * What's missing: body.
 * Acceptance: f completely additive on [1, N].
 * Depends on: sieve_lpf, load_warm.
 */
static void compute_f(State *s) {
  (void)s;
  fprintf(stderr, "NotImplemented: compute_f\n"); exit(3);
}

/* init_bad
 * TODO: build badlist/badpos: r in [1, R] is bad iff f[r] = ... = f[r+L-1] = 0.
 * What's missing: body.
 * Acceptance: nbad == number of zero runs <= R; first bad r equals first zero run.
 * Depends on: compute_f.
 */
static void init_bad(State *s) {
  (void)s;
  fprintf(stderr, "NotImplemented: init_bad\n"); exit(3);
}

/* score_prime
 * TODO: for prime p, fill gain[d] (d = 1..K-1) = (#bad after f(p) += d) - (#bad now), considering
 *       every r whose window [r, r+L-1] contains a multiple of p (f(m) changes by v_p(m)*d).
 * What's missing: body. For p >= L each window contains at most one multiple, so one pass over
 *       multiples suffices; for p < L handle windows directly (evaluate each affected window).
 * Acceptance: applying the move with gain g changes nbad by exactly g (checked in debug mode).
 * Depends on: init_bad.
 */
static void score_prime(State *s, long p, long gain[]) {
  (void)s; (void)p; (void)gain;
  fprintf(stderr, "NotImplemented: score_prime\n"); exit(3);
}

/* apply_move
 * TODO: f(p) += d: update f[m] for all multiples m of p (by v_p(m)*d) and the bad set for all
 *       affected windows.
 * What's missing: body.
 * Acceptance: after apply, init_bad on a fresh recomputation gives the same nbad (debug check).
 * Depends on: score_prime (same window logic), bad-set add/remove helpers.
 */
static void apply_move(State *s, long p, int d) {
  (void)s; (void)p; (void)d;
  fprintf(stderr, "NotImplemented: apply_move\n"); exit(3);
}

/* search
 * TODO: min-conflicts loop: pick a random bad r; candidate primes = distinct primes >= pmin dividing
 *       r..r+L-1 whose v_p is not divisible by K; score all (p, d); with probability noise pick a
 *       random candidate move, else the best non-tabu move (aspiration if it reaches nbad = 0 ...);
 *       apply; set tabu. Stop at nbad == 0 or maxsteps. Log progress to stderr every ~1 s.
 * What's missing: body.
 * Acceptance: returns 0 when nbad reaches 0.
 * Depends on: score_prime, apply_move.
 */
static int search(State *s, long maxsteps, int noise_permille) {
  (void)s; (void)maxsteps; (void)noise_permille;
  fprintf(stderr, "NotImplemented: search\n"); exit(3);
}

/* write_result
 * TODO: write synthetic map (prime, base = K*i+1) for primes <= N with f(p) != 1 and a model file
 *       with "v" lines listing the true literals base+f(p).
 * What's missing: body.
 * Acceptance: `lamenc run K L LIM OUTMAP OUTMODEL` reports first run > R.
 * Depends on: search.
 */
static void write_result(State *s, const char *omap, const char *omodel) {
  (void)s; (void)omap; (void)omodel;
  fprintf(stderr, "NotImplemented: write_result\n"); exit(3);
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: warmls K L R MAP MODEL OUTMAP OUTMODEL [PMIN] [SEED] [MAXSTEPS] [NOISE_PERMILLE]\n"); return 2; }
  State s; memset(&s, 0, sizeof s);
  s.K = atoi(argv[1]); s.L = atoi(argv[2]); s.R = atol(argv[3]); s.N = s.R + s.L - 1;
  s.pmin = argc > 8 ? atol(argv[8]) : 2;
  s.rng = argc > 9 ? strtoull(argv[9], 0, 10) * 2654435761ULL + 1 : 88172645463325252ULL;
  long maxsteps = argc > 10 ? atol(argv[10]) : 100000000L;
  int noise = argc > 11 ? atoi(argv[11]) : 20;
  s.lpf = sieve_lpf(s.N);
  load_warm(&s, argv[4], argv[5]);
  compute_f(&s);
  init_bad(&s);
  int rc = search(&s, maxsteps, noise);
  write_result(&s, argv[6], argv[7]);
  return rc;
}

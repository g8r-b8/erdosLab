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
  uint16_t *lpf;       // smallest prime factor of n (fits: N < 65536^2), 0 if n is prime
  uint8_t *f;          // f[n] in Z/K for 1 <= n <= N (f[1] = 0)
  int32_t *badlist;    // list of bad r (N < 2^31)
  int32_t *badpos;     // 1 + position of r in badlist, or 0 (calloc: pages touched lazily)
  long nbad;
  uint32_t *w;         // breakout weight of window r is 1 + w[r] (calloc: lazy)
  uint32_t *tabu;      // tabu[p] = step until which p may not be changed (indexed by prime)
  long pmin;
  uint64_t rng;
} State;

static int window_bad(const State *s, long r) {
  for (long j = r; j < r + s->L; j++) if (s->f[j]) return 0;
  return 1;
}
static void bad_add(State *s, long r) {
  if (s->badpos[r]) return;
  s->badlist[s->nbad++] = (int32_t)r; s->badpos[r] = (int32_t)s->nbad;
}
static void bad_del(State *s, long r) {
  long i = s->badpos[r] - 1; if (i < 0) return;
  long last = s->badlist[--s->nbad];
  s->badlist[i] = (int32_t)last; s->badpos[last] = (int32_t)(i + 1); s->badpos[r] = 0;
}
static uint64_t rnd(State *s) { s->rng ^= s->rng << 13; s->rng ^= s->rng >> 7; s->rng ^= s->rng << 17; return s->rng; }

/* sieve_lpf
 * fill lpf[n] = smallest prime factor of composite n (0 for primes), 2 <= n <= N < 65536^2.
 * (Was an int32 largest-prime-factor table; uint16 spf halves memory to 2 bytes per n.)
 * What's missing: body.
 * Acceptance: lpf[p] == 0 iff p prime; lpf[12] == 2; lpf[1] unused.
 * Depends on: nothing.
 */
static uint16_t *sieve_lpf(long N) {
  if (N >= 65536L * 65536L) { fprintf(stderr, "N too large for uint16 spf\n"); exit(4); }
  uint16_t *lpf = calloc(N + 1, sizeof(uint16_t));
  if (!lpf) { perror("lpf"); exit(4); }
  for (long p = 2; p * p <= N; p++) if (!lpf[p]) for (long j = p * p; j <= N; j += p) if (!lpf[j]) lpf[j] = (uint16_t)p;
  return lpf;
}

/* load_warm
 * set f[p] for every prime p <= N from MAP/MODEL (true literal base+v => f(p) = v);
 *       primes not in MAP get 1.
 * What's missing: body (read "p base" lines; read "v" lines of the model; tolerate primes > N in MAP).
 * Acceptance: on the 5.75M model, recomputing f and finding the first zero run gives 5,750,107
 *             (same as `lamenc run`).
 * Depends on: sieve_lpf.
 */
static void load_warm(State *s, const char *map, const char *model) {
  long N = s->N;
  s->f = calloc(N + 1, 1);
  if (!s->f) { perror("f"); exit(4); }
  for (long p = 2; p <= N; p++) if (!s->lpf[p]) s->f[p] = 1;
  long cap = 1 << 20, cnt = 0, p, b, maxv = 0;
  long *ps = malloc(cap * sizeof(long)), *bs = malloc(cap * sizeof(long));
  FILE *mp = fopen(map, "r"); if (!mp) { perror(map); exit(4); }
  while (fscanf(mp, "%ld %ld", &p, &b) == 2) {
    if (cnt == cap) { cap *= 2; ps = realloc(ps, cap * sizeof(long)); bs = realloc(bs, cap * sizeof(long)); }
    ps[cnt] = p; bs[cnt] = b; cnt++; if (b + s->K > maxv) maxv = b + s->K;
  }
  fclose(mp);
  uint8_t *val = calloc(maxv + 2, 1);
  FILE *md = fopen(model, "r"); if (!md) { perror(model); exit(4); }
  char tok[64];
  while (fscanf(md, "%63s", tok) == 1) {
    char *e; long x = strtol(tok, &e, 10);
    if (*e) continue;
    if (x > 0 && x <= maxv) val[x] = 1;
  }
  fclose(md);
  long nset = 0;
  for (long i = 0; i < cnt; i++) {
    int got = -1, nt = 0;
    for (int v = 0; v < s->K; v++) if (val[bs[i] + v]) { got = v; nt++; }
    if (nt != 1) { fprintf(stderr, "prime %ld has %d true values\n", ps[i], nt); exit(4); }
    if (ps[i] <= N) { s->f[ps[i]] = (uint8_t)got; nset++; }
  }
  free(val); free(ps); free(bs);
  fprintf(stderr, "loaded %ld prime values (<= N) from %s\n", nset, map);
}

/* compute_f
 * f[n] = f[q] + f[n/q] mod K for composite n (q = lpf[n]), increasing n.
 * What's missing: body.
 * Acceptance: f completely additive on [1, N].
 * Depends on: sieve_lpf, load_warm.
 */
static void compute_f(State *s) {
  s->f[1] = 0;
  for (long n = 2; n <= s->N; n++) {
    long P = s->lpf[n];
    if (P) s->f[n] = (uint8_t)((s->f[P] + s->f[n / P]) % s->K);
  }
}

/* init_bad
 * build badlist/badpos: r in [1, R] is bad iff f[r] = ... = f[r+L-1] = 0.
 * What's missing: body.
 * Acceptance: nbad == number of zero runs <= R; first bad r equals first zero run.
 * Depends on: compute_f.
 */
static void init_bad(State *s) {
  s->badpos = calloc(s->R + 1, sizeof(int32_t));
  s->badlist = malloc((s->R + 1) * sizeof(int32_t));
  if (!s->badpos || !s->badlist) { perror("bad"); exit(4); }
  s->nbad = 0;
  for (long r = 1; r <= s->R; r++) {
    if (window_bad(s, r)) bad_add(s, r);
  }
  long first = 0;
  for (long i = 0; i < s->nbad; i++) if (!first || s->badlist[i] < first) first = s->badlist[i];
  fprintf(stderr, "R=%ld N=%ld initial bad windows: %ld (first %ld)\n", s->R, s->N, s->nbad, first);
}

static int vp(long m, long p) { int e = 0; while (m % p == 0) { m /= p; e++; } return e; }
// bitmask over d in Z/K of "window r is all-zero after f(p) += d"
static unsigned window_mask(const State *s, long r, long p) {
  unsigned mask = (1u << s->K) - 1;
  for (long j = r; j < r + s->L && mask; j++) {
    int e = (j % p == 0) ? vp(j, p) % s->K : 0;
    unsigned mj = 0;
    for (int d = 0; d < s->K; d++) if ((s->f[j] + e * d) % s->K == 0) mj |= 1u << d;
    mask &= mj;
  }
  return mask;
}

/* score_prime
 * for prime p, fill gain[d] (d = 1..K-1) = (#bad after f(p) += d) - (#bad now), considering
 *       every r whose window [r, r+L-1] contains a multiple of p (f(m) changes by v_p(m)*d).
 * What's missing: body. For p >= L each window contains at most one multiple, so one pass over
 *       multiples suffices; for p < L handle windows directly (evaluate each affected window).
 * Acceptance: applying the move with gain g changes nbad by exactly g (checked in debug mode).
 * Depends on: init_bad.
 */
static void score_prime(State *s, long p, long gain[]) {
  for (int d = 0; d < 2 * s->K; d++) gain[d] = 0;
  long last = 0;
  for (long m = p; m <= s->N; m += p) {
    long lo = m - s->L + 1; if (lo <= last) lo = last + 1; if (lo < 1) lo = 1;
    long hi = m < s->R ? m : s->R;
    for (long r = lo; r <= hi; r++) {
      unsigned mask = window_mask(s, r, p);
      int b0 = mask & 1;
      if (mask == 0 || mask == (1u << s->K) - 1) continue;
      for (int d = 1; d < s->K; d++) { int x = (int)((mask >> d) & 1) - b0; gain[d] += x; gain[s->K + d] += x * (1 + (long)s->w[r]); }
    }
    if (hi > last) last = hi;
  }
}

/* apply_move
 * f(p) += d: update f[m] for all multiples m of p (by v_p(m)*d) and the bad set for all
 *       affected windows.
 * What's missing: body.
 * Acceptance: after apply, init_bad on a fresh recomputation gives the same nbad (debug check).
 * Depends on: score_prime (same window logic), bad-set add/remove helpers.
 */
static void apply_move(State *s, long p, int d) {
  for (long m = p; m <= s->N; m += p) s->f[m] = (uint8_t)((s->f[m] + vp(m, p) * d) % s->K);
  long last = 0;
  for (long m = p; m <= s->N; m += p) {
    long lo = m - s->L + 1; if (lo <= last) lo = last + 1; if (lo < 1) lo = 1;
    long hi = m < s->R ? m : s->R;
    for (long r = lo; r <= hi; r++) { if (window_bad(s, r)) bad_add(s, r); else bad_del(s, r); }
    if (hi > last) last = hi;
  }
}

static void dump_window(const State *s, long r) {
  fprintf(stderr, "bad r=%ld:", r);
  for (long j = r; j < r + s->L; j++) {
    fprintf(stderr, " %ld=", j); long n = j; int firstf = 1;
    while (n > 1) { long q = s->lpf[n] ? s->lpf[n] : n; int e = 0; while (n % q == 0) { n /= q; e++; }
      fprintf(stderr, "%s%ld^%d(f=%d)", firstf ? "" : "*", q, e, s->f[q]); firstf = 0; }
  }
  fputc('\n', stderr);
}

/* search
 * min-conflicts loop: pick a random bad r; candidate primes = distinct primes >= pmin dividing
 *       r..r+L-1 whose v_p is not divisible by K; score all (p, d); with probability noise pick a
 *       random candidate move, else the best non-tabu move (aspiration if it reaches nbad = 0 ...);
 *       apply; set tabu. Stop at nbad == 0 or maxsteps. Log progress to stderr every ~1 s.
 * What's missing: body.
 * Acceptance: returns 0 when nbad reaches 0.
 * Depends on: score_prime, apply_move.
 */
static int search(State *s, long maxsteps, int noise_permille) {
  s->tabu = calloc(s->N + 1, sizeof(uint32_t));
  s->w = calloc(s->R + 1, sizeof(uint32_t));
  if (!s->w) { perror("w"); exit(4); }
  if (!s->tabu) { perror("tabu"); exit(4); }
  long best = s->nbad; time_t t0 = time(0), tl = t0;
  long cand[64]; long gain[32];
  long step; int dbg = getenv("WARMLS_DEBUG") != 0;
  for (step = 1; step <= maxsteps && s->nbad > 0; step++) {
    long r = s->badlist[rnd(s) % s->nbad];
    int nc = 0;
    for (int pass = 0; pass < 2 && nc == 0; pass++)
      for (long j = r; j < r + s->L; j++) {
        long n = j;
        while (n > 1) {
          long q = s->lpf[n] ? s->lpf[n] : n; int e = 0; while (n % q == 0) { n /= q; e++; }
          if ((pass || q >= s->pmin) && e % s->K) {
            int dup = 0; for (int i = 0; i < nc; i++) if (cand[i] == q) dup = 1;
            if (!dup && nc < 64) cand[nc++] = q;
          }
        }
      }
    if (nc == 0) { fprintf(stderr, "window %ld has no changeable prime\n", r); return 1; }
    // largest primes first (cheapest to score, fewest side effects)
    for (int i = 1; i < nc; i++) for (int j = i; j > 0 && cand[j] > cand[j-1]; j--) { long t = cand[j]; cand[j] = cand[j-1]; cand[j-1] = t; }
    long bp = 0; int bd = 0; long bg = 1L << 40; int ties = 0;
    for (int i = 0; i < nc; i++) {
      if (bg < 0 && cand[i] < 1000) break;  // improving move found; skip expensive small primes
      score_prime(s, cand[i], gain);
      for (int d = 1; d < s->K; d++) {
        long g = gain[s->K + d];
        if (s->tabu[cand[i]] > (uint32_t)step && s->nbad + gain[d] >= best) continue;
        if (g < bg) { bg = g; bp = cand[i]; bd = d; ties = 1; }
        else if (g == bg && rnd(s) % (++ties) == 0) { bp = cand[i]; bd = d; }
      }
    }
    if (!bp || bg >= 0) {  // local minimum for this window: breakout (raise its weight), sometimes move anyway
      s->w[r]++;
      if (!bp || (long)(rnd(s) % 1000) >= noise_permille) continue;
    }
    long before = s->nbad, pg = 0;
    if (dbg) { score_prime(s, bp, gain); pg = gain[bd]; }  // unweighted
    apply_move(s, bp, bd);
    if (dbg && s->nbad - before != pg) { fprintf(stderr, "gain mismatch p=%ld d=%d pred=%ld got=%ld\n", bp, bd, pg, s->nbad - before); exit(5); }
    s->tabu[bp] = (uint32_t)(step + 5 + rnd(s) % 10);
    if (s->nbad < best) best = s->nbad;
    if ((step & 255) == 0 && time(0) - tl >= 10) {
      tl = time(0);
      long first = 0;
      for (long i = 0; i < s->nbad; i++) if (!first || s->badlist[i] < first) first = s->badlist[i];
      fprintf(stderr, "t=%lds step=%ld nbad=%ld best=%ld first_bad=%ld\n", (long)(tl - t0), step, s->nbad, best, first);
      if (s->nbad <= 3) for (long i = 0; i < s->nbad; i++) dump_window(s, s->badlist[i]);
    }
  }
  long first = 0;
  for (long i = 0; i < s->nbad; i++) if (!first || s->badlist[i] < first) first = s->badlist[i];
  fprintf(stderr, "END t=%lds steps=%ld nbad=%ld best=%ld first_bad=%ld\n", (long)(time(0) - t0), step - 1, s->nbad, best, first);
  for (long i = 0; i < s->nbad && i < 40; i++) dump_window(s, s->badlist[i]);
  return s->nbad == 0 ? 0 : 1;
}

/* write_result
 * write synthetic map (prime, base = K*i+1) for primes <= N with f(p) != 1 and a model file
 *       with "v" lines listing the true literals base+f(p).
 * What's missing: body.
 * Acceptance: `lamenc run K L LIM OUTMAP OUTMODEL` reports first run > R.
 * Depends on: search.
 */
static void write_result(State *s, const char *omap, const char *omodel) {
  FILE *mp = fopen(omap, "w"), *md = fopen(omodel, "w");
  if (!mp || !md) { perror("output"); exit(4); }
  long i = 0, col = 0;
  for (long p = 2; p <= s->N; p++) {
    if (s->lpf[p] || s->f[p] == 1) continue;
    long b = (long)s->K * i + 1; i++;
    fprintf(mp, "%ld %ld\n", p, b);
    if (col == 0) fputs("v", md);
    fprintf(md, " %ld", b + s->f[p]);
    if (++col == 10) { fputs("\n", md); col = 0; }
  }
  if (col) fputs("\n", md);
  fputs("v 0\n", md);
  fclose(mp); fclose(md);
  fprintf(stderr, "wrote %ld primes with f(p) != 1 to %s / %s\n", i, omap, omodel);
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

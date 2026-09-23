// Compact CNF encoder for S(R): "exists completely additive f: N -> Z/k with no l-run of zeros
// f(r)=...=f(r+l-1)=0 starting at any r <= R".  UNSAT(S(R)) <=> Lambda_comb(k,l) <= R.
//
// Usage:
//   lamenc enc k l R out.cnf out.map [nosym]     write CNF + map (prime -> base var)
//   lamenc run k l LIMIT map model               decode solver model (lines "v ...") and print
//                                                the first l-run of the induced f (large primes := 1)
//
// Encoding (N = R+l-1, P(n) = largest prime factor, m = n/P(n)):
//  * primes p > N/2 appear only as n = p; WLOG f(p) != 0 (dominance) -> no vars, z(p) = FALSE.
//  * "full" n (prime p <= N/2, or composite with n*P(n) <= N): one-hot y[n][0..k-1] (ALO+AMO);
//    composite full n: y[P][a] & y[m][b] -> y[n][a+b]   (m is full: m*P(m) <= m*P(n) = n).
//  * other composites: single var z(n) with y[P][a] & y[m][-a] -> z(n)  (k clauses).
//  * run clauses: OR_i not z(r+i), r = 1..R  (z(1) = TRUE; clauses with a FALSE z dropped).
//  * symmetry (units of Z/k act on f): first prime with nonzero value takes a value d | k.
// Only forward implications are encoded; any genuine f extends to a model, and every model's
// prime values define an f with no run <= R (spurious TRUE y/z only add restrictions).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int K, L; static long R, N;
static int *lpf; static long *yb; static long *zv; static long nv;
static FILE *out; static long ncl; static int counting;

static void emit(long *c, int n) {
  ncl++;
  if (counting) return;
  for (int i = 0; i < n; i++) fprintf(out, "%ld ", c[i]);
  fputs("0\n", out);
}
static void sieve(long n) {
  lpf = calloc(n + 1, sizeof(int));
  for (long p = 2; p <= n; p++) if (!lpf[p]) for (long j = p; j <= n; j += p) lpf[j] = (int)p;
}
static int isfull(long n) { return lpf[n] == n ? (n <= N / 2) : ((double)n * lpf[n] <= (double)N); }

static void gen(int sym) {
  long c[64]; long sprev = 0; ncl = 0;
  long nvsave = nv;
  for (long n = 2; n <= N; n++) {
    long P = lpf[n];
    if (P == n) {
      if (!yb[n]) continue;
      long b = yb[n];
      for (int v = 0; v < K; v++) c[v] = b + v; emit(c, K);
      for (int i = 0; i < K; i++) for (int j = i + 1; j < K; j++) { c[0] = -(b+i); c[1] = -(b+j); emit(c, 2); }
      if (sym) {
        for (int v = 1; v < K; v++) if (K % v != 0) { int t = 0; c[t++] = -(b + v); if (sprev) c[t++] = sprev; emit(c, t); }
        long s = yb[n] + K;  // chain var allocated right after the prime's block
        { int t = 0; c[t++] = -s; c[t++] = -b; if (sprev) c[t++] = sprev; emit(c, t); }
        if (sprev) { c[0] = -sprev; c[1] = s; emit(c, 2); }
        c[0] = b; c[1] = s; emit(c, 2);
        sprev = s;
      }
    } else {
      long m = n / P, bp = yb[P], bm = yb[m];
      if (yb[n]) {
        long b = yb[n];
        for (int v = 0; v < K; v++) c[v] = b + v; emit(c, K);
        for (int i = 0; i < K; i++) for (int j = i + 1; j < K; j++) { c[0] = -(b+i); c[1] = -(b+j); emit(c, 2); }
        for (int a = 0; a < K; a++) for (int d = 0; d < K; d++) { c[0] = -(bp+a); c[1] = -(bm+d); c[2] = b + (a+d)%K; emit(c, 3); }
      } else {
        for (int a = 0; a < K; a++) { c[0] = -(bp+a); c[1] = -(bm + (K-a)%K); c[2] = zv[n]; emit(c, 3); }
      }
    }
  }
  for (long r = 1; r <= R; r++) {
    int t = 0, skip = 0;
    for (long n = r; n < r + L; n++) {
      if (n == 1) continue;
      long z = yb[n] ? yb[n] : zv[n];
      if (!z) { skip = 1; break; }
      c[t++] = -z;
    }
    if (!skip) emit(c, t);
  }
  nv = nvsave;
}

static int enc(int argc, char **argv) {
  K = atoi(argv[2]); L = atoi(argv[3]); R = atol(argv[4]); N = R + L - 1;
  int sym = !(argc > 7 && !strcmp(argv[7], "nosym"));
  sieve(N);
  yb = calloc(N + 1, sizeof(long)); zv = calloc(N + 1, sizeof(long)); nv = 0;
  FILE *mp = fopen(argv[6], "w");
  long nfull = 0, nz = 0, np = 0;
  for (long n = 2; n <= N; n++) {
    if (lpf[n] == n) {
      if (n <= N / 2) { yb[n] = nv + 1; nv += K + (sym ? 1 : 0); np++; fprintf(mp, "%ld %ld\n", n, yb[n]); }
    } else if (isfull(n)) { yb[n] = nv + 1; nv += K; nfull++; }
    else { zv[n] = ++nv; nz++; }
  }
  fclose(mp);
  counting = 1; gen(sym);
  out = fopen(argv[5], "w");
  fprintf(out, "p cnf %ld %ld\n", nv, ncl);
  counting = 0; gen(sym);
  fclose(out);
  fprintf(stderr, "k=%d l=%d R=%ld N=%ld vars=%ld clauses=%ld primes_with_vars=%ld full_composites=%ld z_only=%ld\n",
          K, L, R, N, nv, ncl, np, nfull, nz);
  return 0;
}

static int run(int argc, char **argv) {
  K = atoi(argv[2]); L = atoi(argv[3]); long lim = atol(argv[4]);
  sieve(lim + L);
  // read map
  long maxv = 0; long p, b;
  FILE *mp = fopen(argv[5], "r");
  long cap = 1 << 20, cnt = 0; long *ps = malloc(cap * sizeof(long)), *bs = malloc(cap * sizeof(long));
  while (fscanf(mp, "%ld %ld", &p, &b) == 2) {
    if (cnt == cap) { cap *= 2; ps = realloc(ps, cap * sizeof(long)); bs = realloc(bs, cap * sizeof(long)); }
    ps[cnt] = p; bs[cnt] = b; cnt++; if (b + K > maxv) maxv = b + K;
  }
  fclose(mp);
  char *val = calloc(maxv + 2, 1);
  FILE *md = fopen(argv[6], "r");
  char tok[64];
  while (fscanf(md, "%63s", tok) == 1) {
    char *e; long x = strtol(tok, &e, 10);
    if (*e) continue;
    if (x > 0 && x <= maxv) val[x] = 1;
  }
  fclose(md);
  unsigned char *f = calloc(lim + L + 1, 1);
  for (long n = 2; n <= lim + L; n++) if (lpf[n] == n) f[n] = 1;
  for (long i = 0; i < cnt; i++) {
    int got = -1;
    for (int v = 0; v < K; v++) if (val[bs[i] + v]) { if (got >= 0) { fprintf(stderr, "prime %ld multi-valued\n", ps[i]); } got = v; }
    if (got < 0) { fprintf(stderr, "prime %ld no value\n", ps[i]); return 1; }
    if (ps[i] <= lim + L) f[ps[i]] = got;
  }
  int runlen = 1;  // f(1) = 0
  for (long n = 2; n <= lim + L; n++) {
    if (lpf[n] != n) f[n] = (f[lpf[n]] + f[n / lpf[n]]) % K;
    runlen = f[n] == 0 ? runlen + 1 : 0;
    if (runlen >= L) { printf("%ld\n", n - L + 1); return 0; }
  }
  printf("NONE %ld\n", lim);
  // optionally dump prime values
  return 0;
}

int main(int argc, char **argv) {
  if (argc >= 7 && !strcmp(argv[1], "enc")) return enc(argc, argv);
  if (argc >= 7 && !strcmp(argv[1], "run")) return run(argc, argv);
  fprintf(stderr, "usage: see header\n"); return 2;
}

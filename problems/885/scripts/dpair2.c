// Erdos #885, k=5 search driven by the DIFFERENCES (N unbounded).
//
// d in D(N)  <=>  x + d^2 = s^2 with x = 4N (s = a+b, d = b-a, N = ab).
// For two differences d_a < d_b sharing x:  s_b^2 - s_a^2 = d_b^2 - d_a^2 =: Delta,
// so every shared x comes from a factorisation Delta = u*v (u<v, u==v mod 2):
//   s_a = (v-u)/2,  x = s_a^2 - d_a^2  (need s_a > d_a).
// Candidate differences: d = g*m, m = 1..M. (g = 1: COMPLETE search over all k=5 witnesses whose
// five common differences are <= M, any N.  g > 1: rational x with denominator | g^2.)
// Pivot a = smallest common difference.  For each pivot, collect (x, b) for all b > a, group by x;
// rows with >= 3 partners give k=4 candidates (3-subsets shared by >= 4 rows), rows with >= 4
// partners give k=5 candidates (4-subsets shared by >= 5 rows).  Every hit is re-verified.
// Output x-values: any integer x works as N = x with differences 2d (4x + (2d)^2 = (2s)^2).
//
// dpair2: same search, but row-sets found by inverted-index intersection (memory O(pairs));
// in-process cap DPAIR_MEMCAP_MB (default 1500).  usage: dpair2 g M part nparts [print_k4] [mstart]   (stderr logs 'pivot m' progress; resume with mstart)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned __int128 u128;
typedef struct { u128 x; uint32_t b; } P;
typedef struct { u128 key; u128 x; } K;   // key = packed sorted partner indices

static uint32_t *spf;
static int nfg; static uint64_t fgp[32]; static int fge[32];   // factorisation of g^2

static int cmpP(const void *p, const void *q) {
  const P *a = p, *b = q;
  if (a->x != b->x) return a->x < b->x ? -1 : 1;
  return a->b < b->b ? -1 : a->b > b->b;
}
static int cmpK(const void *p, const void *q) {
  const K *a = p, *b = q;
  if (a->key != b->key) return a->key < b->key ? -1 : 1;
  return a->x < b->x ? -1 : a->x > b->x;
}
static void pr128(FILE *f, u128 v) {
  char buf[48]; int i = 47; buf[i] = 0;
  if (!v) { fputc('0', f); return; }
  while (v) { buf[--i] = '0' + (int)(v % 10); v /= 10; }
  fputs(buf + i, f);
}
static int issq(u128 n) {
  if (n == 0) return 1;
  long double r = sqrtl((long double)n);
  u128 s = (u128)r;
  while (s * s > n) s--;
  while ((s + 1) * (s + 1) <= n) s++;
  return s * s == n;
}

// add prime factorisation of n (n <= sieve limit) into (p,e) lists
static int addfac(uint64_t n, uint64_t *p, int *e, int np) {
  while (n > 1) {
    uint64_t q = spf[n]; int c = 0;
    while (n % q == 0) { n /= q; c++; }
    int i; for (i = 0; i < np && p[i] != q; i++);
    if (i == np) { p[np] = q; e[np] = 0; np++; }
    e[i] += c;
  }
  return np;
}


// ---- row-set search state (dpair2) ----
static P *pairs; static size_t *rs; static uint32_t *rc, *rcnt, *cand, *touched, *inv;
static size_t capR = 1 << 16, capI = 1 << 20, capC = 1 << 12, capT = 1 << 16;
static uint64_t *bst; static uint32_t *bcnt; static size_t memcap;
static uint64_t G; static int PK4; static long nk4, nk5, nk54, nk45;

static void report(const char *tag, uint32_t *chosen, int nrow, const uint32_t *T, uint32_t nT, uint64_t ma) {
  int ok = 1;
  for (int i = 0; i < nrow; i++) { u128 x = pairs[rs[chosen[i]]].x; u128 d = (u128)G * ma; if (!issq(x + d * d)) ok = 0;
    for (uint32_t t = 0; t < nT; t++) { d = (u128)G * T[t]; if (!issq(x + d * d)) ok = 0; } }
  printf("%s%s g=%llu m={%llu", tag, ok ? "" : "(VERIFY-FAIL)", (unsigned long long)G, (unsigned long long)ma);
  for (uint32_t t = 0; t < nT; t++) printf(",%u", T[t]);
  printf("} rows=%d x:", nrow);
  for (int i = 0; i < nrow; i++) { putchar(' '); pr128(stdout, pairs[rs[chosen[i]]].x); }
  putchar('\n');
}
// chosen[0..nrow) rows, T = common partners (sorted); extend with candidates cand[from..ncand)
static void dfs(int nrow, uint32_t *chosen, const uint32_t *T, uint32_t nT, size_t from, size_t ncand, uint64_t ma) {
  uint32_t T2[4096];
  for (size_t c = from; c < ncand; c++) {
    uint32_t r = cand[c]; const P *S = pairs + rs[r]; uint32_t ns = rc[r], n2 = 0, i = 0, j = 0;
    while (i < nT && j < ns) { if (T[i] < S[j].b) i++; else if (T[i] > S[j].b) j++; else { T2[n2++] = T[i]; i++; j++; } }
    if (n2 < 3) continue;
    chosen[nrow] = r; int k = nrow + 1;
    if (k == 4) { nk4++; if (PK4) report("K4", chosen, 4, T2, n2, ma); if (n2 >= 4) { nk45++; report("K45", chosen, 4, T2, n2, ma); } }
    if (k == 5) { nk54++; report("K54", chosen, 5, T2, n2, ma); if (n2 >= 4) { nk5++; report("K5", chosen, 5, T2, n2, ma); } }
    if (k < 5) dfs(k, chosen, T2, n2, c + 1, ncand, ma);
  }
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: dpair g M part nparts [print_k4]\n"); return 1; }
  uint64_t g = strtoull(argv[1], 0, 10); uint64_t M = strtoull(argv[2], 0, 10);
  int part = atoi(argv[3]), nparts = atoi(argv[4]); int pk4 = argc > 5 ? atoi(argv[5]) : 0;
  uint64_t mstart = argc > 6 ? strtoull(argv[6], 0, 10) : 1;   // resume: skip pivots < mstart
  setvbuf(stdout, NULL, _IOLBF, 0);
  uint64_t L = 2 * M + 2;
  spf = calloc(L + 1, sizeof(uint32_t));
  for (uint64_t i = 2; i <= L; i++) if (!spf[i]) for (uint64_t j = i; j <= L; j += i) if (!spf[j]) spf[j] = (uint32_t)i;
  { uint64_t n = g; nfg = 0;
    for (uint64_t q = 2; q * q <= n; q++) if (n % q == 0) { int c = 0; while (n % q == 0) { n /= q; c++; } fgp[nfg] = q; fge[nfg++] = 2 * c; }
    if (n > 1) { fgp[nfg] = n; fge[nfg++] = 2; } }

  size_t capP = 1 << 20; pairs = malloc(capP * sizeof(P)); uint64_t totpairs = 0;
  G = g; PK4 = pk4; memcap = (size_t)(getenv("DPAIR_MEMCAP_MB") ? atol(getenv("DPAIR_MEMCAP_MB")) : 1500) << 20;
  rs = malloc(capR * sizeof(size_t)); rc = malloc(capR * 4); rcnt = calloc(capR, 4); inv = malloc(capI * 4);
  cand = malloc(capC * 4); touched = malloc(capT * 4); bst = calloc(M + 2, 8); bcnt = calloc(M + 2, 4);
  uint64_t divs[1 << 16];

  for (uint64_t ma = 1 + part; ma <= M; ma += nparts) {
    if (ma < mstart) continue;
    if ((ma - 1 - part) % (50 * nparts) == 0) { fprintf(stderr, "pivot %llu\n", (unsigned long long)ma); fflush(stderr); }
    u128 da = (u128)g * ma;
    size_t np = 0;
    for (uint64_t mb = ma + 1; mb <= M; mb++) {
      // Delta = g^2 (mb-ma)(mb+ma)
      uint64_t p[64]; int e[64]; int n = 0;
      for (int i = 0; i < nfg; i++) { p[n] = fgp[i]; e[n] = fge[i]; n++; }
      n = addfac(mb - ma, p, e, n); n = addfac(mb + ma, p, e, n);
      u128 Delta = (u128)g * g * (mb - ma) * (mb + ma);
      // enumerate divisors (as u128 would be safer; Delta < 2^126 assumed, divisors kept in u128 via loop)
      static u128 dv[1 << 20]; size_t nd = 1; dv[0] = 1;
      for (int i = 0; i < n; i++) {
        size_t cur = nd; u128 pw = 1;
        for (int k = 1; k <= e[i]; k++) { pw *= p[i]; for (size_t j = 0; j < cur; j++) { if (nd >= (1 << 20)) { fprintf(stderr, "too many divisors\n"); exit(2); } dv[nd++] = dv[j] * pw; } }
      }
      for (size_t j = 0; j < nd; j++) {
        u128 u = dv[j]; if (u * u >= Delta) continue;
        u128 v = Delta / u; if (((u ^ v) & 1)) continue;
        u128 sa = (v - u) / 2; if (sa <= da) continue;
        u128 x = sa * sa - da * da;
        if (np == capP) { capP *= 2; if (capP * sizeof(P) > memcap) { fprintf(stderr, "MEMCAP exceeded (pairs) at pivot %llu\n", (unsigned long long)ma); exit(3); } pairs = realloc(pairs, capP * sizeof(P)); }
        pairs[np].x = x; pairs[np].b = (uint32_t)mb; np++;
      }
    }
    (void)divs;
    totpairs += np;
    qsort(pairs, np, sizeof(P), cmpP);
    // rows = x-groups with >= 3 partners; S_r = pairs[rs[r] .. rs[r]+rc[r]) sorted by b
    size_t nr = 0;
    for (size_t i = 0; i < np;) {
      size_t j = i; while (j < np && pairs[j].x == pairs[i].x) j++;
      if (j - i >= 3) { if (nr == capR) { capR *= 2; rs = realloc(rs, capR * sizeof(size_t)); rc = realloc(rc, capR * sizeof(uint32_t)); rcnt = realloc(rcnt, capR * sizeof(uint32_t)); memset(rcnt, 0, capR * sizeof(uint32_t)); }
        rs[nr] = i; rc[nr] = (uint32_t)(j - i); nr++; }
      i = j;
    }
    // inverted index (CSR) partner b -> rows
    size_t tot = 0;
    for (size_t r = 0; r < nr; r++) { for (uint32_t t = 0; t < rc[r]; t++) bcnt[pairs[rs[r] + t].b]++; tot += rc[r]; }
    if (tot > capI) { capI = tot * 2; inv = realloc(inv, capI * sizeof(uint32_t)); }
    { size_t acc = 0; for (uint64_t b = ma + 1; b <= M; b++) { bst[b] = acc; acc += bcnt[b]; bcnt[b] = 0; } bst[M + 1] = acc; }
    for (size_t r = 0; r < nr; r++) for (uint32_t t = 0; t < rc[r]; t++) { uint32_t b = pairs[rs[r] + t].b; inv[bst[b] + bcnt[b]++] = (uint32_t)r; }
    for (uint64_t b = ma + 1; b <= M; b++) bcnt[b] = 0;
    if (np * sizeof(P) + tot * 4 + nr * 16 > memcap) { fprintf(stderr, "MEMCAP exceeded at pivot %llu\n", (unsigned long long)ma); exit(3); }
    for (size_t r1 = 0; r1 < nr; r1++) {
      size_t nt = 0, ncand = 0;
      for (uint32_t t = 0; t < rc[r1]; t++) { uint32_t b = pairs[rs[r1] + t].b;
        for (size_t q = bst[b]; q < bst[b + 1]; q++) { uint32_t r = inv[q]; if (r <= r1) continue; if (!rcnt[r]++) { if (nt == capT) { capT *= 2; touched = realloc(touched, capT * 4); } touched[nt++] = r; } } }
      for (size_t q = 0; q < nt; q++) { uint32_t r = touched[q]; if (rcnt[r] >= 3) { if (ncand == capC) { capC *= 2; cand = realloc(cand, capC * 4); } cand[ncand++] = r; } rcnt[r] = 0; }
      if (ncand < 3) continue;
      // sort candidates ascending so row-sets are enumerated once
      for (size_t a = 1; a < ncand; a++) { uint32_t v = cand[a]; size_t b = a; while (b && cand[b - 1] > v) { cand[b] = cand[b - 1]; b--; } cand[b] = v; }
      uint32_t T0[4096]; uint32_t n0 = rc[r1] < 4096 ? rc[r1] : 4096;
      for (uint32_t t = 0; t < n0; t++) T0[t] = pairs[rs[r1] + t].b;
      uint32_t chosen[5]; chosen[0] = (uint32_t)r1;
      dfs(1, chosen, T0, n0, 0, ncand, ma);
    }
    (void)cmpK;
  }
  fprintf(stderr, "done g=%llu M=%llu part=%d/%d pairs=%llu k4keys=%ld k54=%ld k45=%ld k5=%ld\n", (unsigned long long)g, (unsigned long long)M,
          part, nparts, (unsigned long long)totpairs, nk4, nk54, nk45, nk5);
  return 0;
}

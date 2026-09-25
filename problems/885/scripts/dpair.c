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
// usage: dpair g M part nparts [print_k4]
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

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: dpair g M part nparts [print_k4]\n"); return 1; }
  uint64_t g = strtoull(argv[1], 0, 10); uint64_t M = strtoull(argv[2], 0, 10);
  int part = atoi(argv[3]), nparts = atoi(argv[4]); int pk4 = argc > 5 ? atoi(argv[5]) : 0;
  uint64_t L = 2 * M + 2;
  spf = calloc(L + 1, sizeof(uint32_t));
  for (uint64_t i = 2; i <= L; i++) if (!spf[i]) for (uint64_t j = i; j <= L; j += i) if (!spf[j]) spf[j] = (uint32_t)i;
  { uint64_t n = g; nfg = 0;
    for (uint64_t q = 2; q * q <= n; q++) if (n % q == 0) { int c = 0; while (n % q == 0) { n /= q; c++; } fgp[nfg] = q; fge[nfg++] = 2 * c; }
    if (n > 1) { fgp[nfg] = n; fge[nfg++] = 2; } }

  size_t capP = 1 << 20; P *pairs = malloc(capP * sizeof(P));
  size_t capK = 1 << 16; K *keys3 = malloc(capK * sizeof(K)), *keys4 = malloc(capK * sizeof(K));
  long nk4 = 0, nk5 = 0; uint64_t totpairs = 0;
  uint64_t divs[1 << 16];

  for (uint64_t ma = 1 + part; ma <= M; ma += nparts) {
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
        if (np == capP) { capP *= 2; pairs = realloc(pairs, capP * sizeof(P)); }
        pairs[np].x = x; pairs[np].b = (uint32_t)mb; np++;
      }
    }
    (void)divs;
    totpairs += np;
    qsort(pairs, np, sizeof(P), cmpP);
    size_t n3 = 0, n4 = 0;
    for (size_t i = 0; i < np;) {
      size_t j = i; while (j < np && pairs[j].x == pairs[i].x) j++;
      size_t c = j - i;
      if (c >= 3) {
        uint32_t *B = malloc(c * sizeof(uint32_t)); for (size_t t = 0; t < c; t++) B[t] = pairs[i + t].b;
        for (size_t q1 = 0; q1 < c; q1++) for (size_t q2 = q1 + 1; q2 < c; q2++) for (size_t q3 = q2 + 1; q3 < c; q3++) {
          if (n3 == capK) { capK *= 2; keys3 = realloc(keys3, capK * sizeof(K)); keys4 = realloc(keys4, capK * sizeof(K)); }
          keys3[n3].key = ((u128)B[q1] << 64) | ((u128)B[q2] << 32) | B[q3]; keys3[n3].x = pairs[i].x; n3++;
          for (size_t q4 = q3 + 1; q4 < c; q4++) {
            if (n4 == capK) { capK *= 2; keys3 = realloc(keys3, capK * sizeof(K)); keys4 = realloc(keys4, capK * sizeof(K)); }
            keys4[n4].key = ((u128)B[q1] << 96) | ((u128)B[q2] << 64) | ((u128)B[q3] << 32) | B[q4]; keys4[n4].x = pairs[i].x; n4++;
          }
        }
        free(B);
      }
      i = j;
    }
    qsort(keys3, n3, sizeof(K), cmpK);
    for (size_t i = 0; i < n3;) {
      size_t j = i; while (j < n3 && keys3[j].key == keys3[i].key) j++;
      if (j - i >= 4) {
        nk4++;
        if (pk4) {
          uint32_t b1 = (uint32_t)(keys3[i].key >> 64), b2 = (uint32_t)(keys3[i].key >> 32), b3 = (uint32_t)keys3[i].key;
          printf("K4 g=%llu m={%llu,%u,%u,%u} rows=%zu x:", (unsigned long long)g, (unsigned long long)ma, b1, b2, b3, j - i);
          for (size_t t = i; t < j; t++) { putchar(' '); pr128(stdout, keys3[t].x); }
          putchar('\n');
        }
      }
      i = j;
    }
    qsort(keys4, n4, sizeof(K), cmpK);
    for (size_t i = 0; i < n4;) {
      size_t j = i; while (j < n4 && keys4[j].key == keys4[i].key) j++;
      if (j - i >= 5) {
        uint64_t mm[5] = { ma, (uint32_t)(keys4[i].key >> 96), (uint32_t)(keys4[i].key >> 64), (uint32_t)(keys4[i].key >> 32), (uint32_t)keys4[i].key };
        int ok = 1;
        for (size_t t = i; t < j; t++) for (int c = 0; c < 5; c++) { u128 d = (u128)g * mm[c]; if (!issq(keys4[t].x + d * d)) ok = 0; }
        nk5++;
        printf("K5%s g=%llu m={%llu,%llu,%llu,%llu,%llu} rows=%zu x:", ok ? "" : "(VERIFY-FAIL)", (unsigned long long)g,
               (unsigned long long)mm[0], (unsigned long long)mm[1], (unsigned long long)mm[2], (unsigned long long)mm[3], (unsigned long long)mm[4], j - i);
        for (size_t t = i; t < j; t++) { putchar(' '); pr128(stdout, keys4[t].x); }
        putchar('\n'); fflush(stdout);
      }
      i = j;
    }
  }
  fprintf(stderr, "done g=%llu M=%llu part=%d/%d pairs=%llu k4keys=%ld k5=%ld\n", (unsigned long long)g, (unsigned long long)M,
          part, nparts, (unsigned long long)totpairs, nk4, nk5);
  return 0;
}

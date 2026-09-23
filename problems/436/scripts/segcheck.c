// segcheck: memory-light decoder/verifier for a candidate f (third implementation, independent of
// lamenc.c, warmls.c and checkf.py; used where `lamenc run` does not fit in RAM).
//
//   segcheck K L LIM MAP MODEL
//
// MAP: lines "p base"; MODEL: solver "v" lines.  f(p) = v iff literal base+v is true (exactly one
// required, else error); primes not in MAP have f(p) = 1.  Prints the least r <= LIM with
// f(r) = ... = f(r+L-1) = 0 (f(1) = 0), or "NONE LIM".
// Method: segments of 2^20 integers; for each prime p <= sqrt(N) (N = LIM+L-1) and each power
// p^j <= N, every multiple of p^j in the segment gets f(p) added and one factor p divided out; the
// remaining cofactor is 1 or a prime q > sqrt(N), looked up by binary search in the sorted MAP.
// Memory: O(segment + |MAP|).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { long p, b; } Ent;
static int cmp_ent(const void *a, const void *b) {
  long x = ((const Ent *)a)->p, y = ((const Ent *)b)->p; return (x > y) - (x < y);
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: segcheck K L LIM MAP MODEL\n"); return 2; }
  int K = atoi(argv[1]), L = atoi(argv[2]); long lim = atol(argv[3]), N = lim + L - 1;
  // map
  long cap = 1 << 16, n = 0, maxlit = 0; Ent *e = malloc(cap * sizeof(Ent));
  FILE *fm = fopen(argv[4], "r"); if (!fm) { perror(argv[4]); return 2; }
  long p, b;
  while (fscanf(fm, "%ld %ld", &p, &b) == 2) {
    if (n == cap) { cap *= 2; e = realloc(e, cap * sizeof(Ent)); }
    e[n].p = p; e[n].b = b; n++; if (b + K > maxlit) maxlit = b + K;
  }
  fclose(fm);
  qsort(e, n, sizeof(Ent), cmp_ent);
  // model: bitset of true literals
  uint8_t *tr = calloc(maxlit / 8 + 2, 1);
  FILE *fd = fopen(argv[5], "r"); if (!fd) { perror(argv[5]); return 2; }
  char tok[64];
  while (fscanf(fd, "%63s", tok) == 1) {
    char *end; long x = strtol(tok, &end, 10);
    if (*end || x <= 0 || x > maxlit) continue;
    tr[x >> 3] |= (uint8_t)(1 << (x & 7));
  }
  fclose(fd);
  uint8_t *val = malloc(n + 1);
  for (long i = 0; i < n; i++) {
    int cnt = 0, v = 0;
    for (int d = 0; d < K; d++) { long x = e[i].b + d; if ((tr[x >> 3] >> (x & 7)) & 1) { cnt++; v = d; } }
    if (cnt != 1) { fprintf(stderr, "prime %ld: %d true values\n", e[i].p, cnt); return 3; }
    if (i && e[i].p == e[i - 1].p) { fprintf(stderr, "prime %ld listed twice\n", e[i].p); return 3; }
    val[i] = (uint8_t)v;
  }
  // value of a prime q (binary search, default 1)
  #define FVAL(q, out) do { long lo_ = 0, hi_ = n - 1, r_ = 1; \
    while (lo_ <= hi_) { long mid = (lo_ + hi_) / 2; if (e[mid].p == (q)) { r_ = val[mid]; break; } \
      if (e[mid].p < (q)) lo_ = mid + 1; else hi_ = mid - 1; } (out) = r_; } while (0)
  // small primes <= sqrt(N) by a simple sieve
  long B = 1; while ((B + 1) * (B + 1) <= N) B++;
  uint8_t *comp = calloc(B + 1, 1); long *sp = malloc((B + 1) * sizeof(long)), *sv = malloc((B + 1) * sizeof(long)), ns = 0;
  for (long q = 2; q <= B; q++) if (!comp[q]) { sp[ns] = q; FVAL(q, sv[ns]); ns++; for (long j = q * q; j <= B; j += q) comp[j] = 1; }
  const long SEG = 1 << 20;
  uint64_t *rem = malloc(SEG * sizeof(uint64_t)); uint32_t *acc = malloc(SEG * sizeof(uint32_t));
  long run = 1;  // f(1) = 0: a run of length 1 ends at n = 1
  for (long lo = 2; lo <= N; lo += SEG) {
    long hi = lo + SEG; if (hi > N + 1) hi = N + 1;
    for (long x = lo; x < hi; x++) { rem[x - lo] = (uint64_t)x; acc[x - lo] = 0; }
    for (long i = 0; i < ns; i++) {
      long q = sp[i];
      for (long pk = q; pk < hi; pk *= q) {
        for (long m = ((lo + pk - 1) / pk) * pk; m < hi; m += pk) { rem[m - lo] /= (uint64_t)q; acc[m - lo] += (uint32_t)sv[i]; }
        if (pk > N / q) break;
      }
    }
    for (long x = lo; x < hi; x++) {
      uint32_t a = acc[x - lo]; uint64_t q = rem[x - lo];
      if (q > 1) { long v; FVAL((long)q, v); a += (uint32_t)v; }
      if (a % (uint32_t)K == 0) run++; else run = 0;
      if (run >= L && x - L + 1 <= lim) { printf("%ld\n", x - L + 1); return 0; }
    }
  }
  printf("NONE %ld\n", lim);
  return 0;
}

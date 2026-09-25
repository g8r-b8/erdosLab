// Erdos #885: try to extend a known 4x4 configuration (x_1..x_4, d_1..d_4 with every x_i + d_j^2 a square)
// by a RATIONAL 5th column d = p/q or a RATIONAL 5th row x = X/q^2, for all q <= Q.
//   column: q^2 x_1 + p^2 = s^2  =>  p = (v-u)/2 with uv = q^2 x_1;  test q^2 x_i + p^2 = square, i = 2..4.
//   row:    X + (q d_1)^2 = s_1^2, X + (q d_2)^2 = s_2^2  =>  s_1 = (v-u)/2 with uv = q^2 (d_2^2 - d_1^2);
//           X = s_1^2 - q^2 d_1^2 > 0;  test X + (q d_j)^2 = square, j = 3, 4.
// Such a point is a rational point on a genus-5 curve (3 quadrics in P^4). Squareness is tested modulo
// many small moduli (numbers overflow 128 bits); survivors are printed for exact verification in gp.
// Every surviving line must be verified exactly — this program proves nothing by itself.
// usage: ext Q x1 x2 x3 x4 d1 d2 d3 d4
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;

static const int MODS[] = {64, 63, 65, 11, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199};
#define NM (int)(sizeof(MODS) / sizeof(int))
static unsigned char qr[NM][256];

static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) { uint64_t r = 1; a %= m; while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; } return r; }
static int isprime(uint64_t n) {
  if (n < 2) return 0;
  static const uint64_t sp[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
  for (int i = 0; i < 12; i++) { if (n % sp[i] == 0) return n == sp[i]; }
  uint64_t d = n - 1; int s = 0; while (!(d & 1)) { d >>= 1; s++; }
  for (int i = 0; i < 12; i++) {
    uint64_t x = powmod(sp[i], d, n); if (x == 1 || x == n - 1) continue;
    int ok = 0; for (int r = 1; r < s; r++) { x = mulmod(x, x, n); if (x == n - 1) { ok = 1; break; } }
    if (!ok) return 0;
  }
  return 1;
}
static uint64_t gcd64(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }
static uint64_t rho(uint64_t n) {
  if (n % 2 == 0) return 2;
  for (uint64_t c = 1;; c++) {
    uint64_t x = 2, y = 2, d = 1;
    while (d == 1) { x = (mulmod(x, x, n) + c) % n; y = (mulmod(y, y, n) + c) % n; y = (mulmod(y, y, n) + c) % n; d = gcd64(x > y ? x - y : y - x, n); }
    if (d != n) return d;
  }
}
typedef struct { uint64_t p[64]; int e[64]; int n; } F;
static void addp(F *f, uint64_t p, int e) { for (int i = 0; i < f->n; i++) if (f->p[i] == p) { f->e[i] += e; return; } f->p[f->n] = p; f->e[f->n++] = e; }
static void factor(uint64_t n, F *f, int mult) {
  if (n == 1) return;
  for (uint64_t p = 2; p < 1000 && p * p <= n; p++) while (n % p == 0) { addp(f, p, mult); n /= p; }
  if (n == 1) return;
  if (isprime(n)) { addp(f, n, mult); return; }
  uint64_t d = rho(n); factor(d, f, mult); factor(n / d, f, mult);
}
static u128 *dv; static size_t capdv = 1 << 22;
static size_t divisors(const F *f) {
  size_t nd = 1; dv[0] = 1;
  for (int i = 0; i < f->n; i++) { size_t cur = nd; u128 pw = 1;
    for (int k = 1; k <= f->e[i]; k++) { pw *= f->p[i];
      for (size_t j = 0; j < cur; j++) { if (nd == capdv) { capdv *= 2; dv = realloc(dv, capdv * sizeof(u128)); } dv[nd++] = dv[j] * pw; } } }
  return nd;
}
static void pr128(u128 v) { char b[48]; int i = 47; b[i] = 0; if (!v) { putchar('0'); return; } while (v) { b[--i] = '0' + (int)(v % 10); v /= 10; } fputs(b + i, stdout); }

int main(int argc, char **argv) {
  if (argc < 10) { fprintf(stderr, "usage: ext Q x1 x2 x3 x4 d1 d2 d3 d4\n"); return 1; }
  uint64_t Q = strtoull(argv[1], 0, 10), x[4], d[4];
  for (int i = 0; i < 4; i++) { x[i] = strtoull(argv[2 + i], 0, 10); d[i] = strtoull(argv[6 + i], 0, 10); }
  for (int k = 0; k < NM; k++) for (int r = 0; r < MODS[k]; r++) qr[k][(r * r) % MODS[k]] = 1;
  dv = malloc(capdv * sizeof(u128));
  F fx = {0}, fD = {0};
  factor(x[0], &fx, 1);
  factor(d[1] - d[0], &fD, 1); factor(d[1] + d[0], &fD, 1);
  long ncol = 0, nrow = 0; uint64_t work = 0; int keepdup = getenv("EXT_KEEPDUP") != 0;   // validation: report known rows/cols
  uint64_t r[4]; for (int i = 0; i < 4; i++) { u128 t = (u128)x[i] + (u128)d[0] * d[0]; uint64_t s = 1; while ((u128)s * s < t) s <<= 1;
    uint64_t lo = 0, hi = s; while (lo < hi) { uint64_t mid = lo + (hi - lo + 1) / 2; if ((u128)mid * mid <= t) lo = mid; else hi = mid - 1; } r[i] = lo; }
  for (uint64_t q = 1; q <= Q; q++) {
    F fq = {0}; factor(q, &fq, 2);
    // ---- column extension ----
    F f = fx; for (int i = 0; i < fq.n; i++) addp(&f, fq.p[i], fq.e[i]);
    u128 T = (u128)q * q * x[0];
    size_t nd = divisors(&f); work += nd;
    for (size_t j = 0; j < nd; j++) {
      u128 u = dv[j]; if (u * u >= T) continue; u128 v = T / u; if ((u ^ v) & 1) continue;
      u128 p = (v - u) / 2; if (p == 0) continue;
      if (gcd64((uint64_t)(p % q), q) != 1 && q > 1) continue;   // p/q not in lowest terms: seen at smaller q
      int dup = 0; for (int i = 0; i < 4; i++) if (p == (u128)q * d[i]) dup = 1; if (dup && !keepdup) continue;
      int ok = 1;
      for (int k = 0; k < NM && ok; k++) { int m = MODS[k]; uint64_t pm = (uint64_t)(p % m), qm = q % m;
        for (int i = 1; i < 4 && ok; i++) if (!qr[k][(qm * qm % m * (x[i] % m) + pm * pm) % m]) ok = 0; }
      if (ok) { ncol++; printf("COL q=%llu p=", (unsigned long long)q); pr128(p); putchar('\n'); fflush(stdout); }
    }
    // ---- row extension ----
    F g = fD; for (int i = 0; i < fq.n; i++) addp(&g, fq.p[i], fq.e[i]);
    u128 T2 = (u128)q * q * (d[1] - d[0]) * (d[1] + d[0]);
    nd = divisors(&g); work += nd;
    for (size_t j = 0; j < nd; j++) {
      u128 u = dv[j]; if (u * u >= T2) continue; u128 v = T2 / u; if ((u ^ v) & 1) continue;
      u128 s1 = (v - u) / 2; if (s1 <= (u128)q * d[0]) continue;
      { int dup = 0; for (int i = 0; i < 4; i++) if (s1 == (u128)q * r[i]) dup = 1; if (dup && !keepdup) continue; }
      int ok = 1;
      for (int k = 0; k < NM && ok; k++) { int m = MODS[k]; uint64_t sm = (uint64_t)(s1 % m), qm = q % m;
        for (int jj = 2; jj < 4 && ok; jj++) {
          uint64_t a = (sm * sm + m * m - qm * qm % m * (d[0] % m * (d[0] % m) % m) % m + qm * qm % m * (d[jj] % m * (d[jj] % m) % m)) % m;
          if (!qr[k][a]) ok = 0; } }
      if (ok) { nrow++; printf("ROW q=%llu s1=", (unsigned long long)q); pr128(s1); putchar('\n'); fflush(stdout); }
    }
  }
  fprintf(stderr, "done Q=%llu divisor-work=%llu col-cands=%ld row-cands=%ld\n", (unsigned long long)Q, (unsigned long long)work, ncol, nrow);
  return 0;
}

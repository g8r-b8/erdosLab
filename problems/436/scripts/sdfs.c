// Direct DFS for the weakened instance F_y(X): assign f(p) for primes p <= y in increasing order;
// a run r..r+l-1 is checked as soon as its largest prime is assigned (each run forbids at most one
// value of the current prime, given the earlier ones).  Symmetry: first nonzero value is 1 (k prime).
// Usage: sdfs k l y runs.txt [maxsols [splitdepth job njobs]]
//   prints #nodes per depth and solutions (up to maxsols; 0 = count all; -N = Knuth estimate, N probes).  With splitdepth d, only the
//   subtrees rooted at depth-d nodes with (index mod njobs == job) are explored (parallel split).
// Partial sums are maintained incrementally (S[member] = sum over assigned primes of e*f(p)).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#define MAXP 4000
static int K, L, Y, P[MAXP], np;
typedef struct { int n; short idx[64]; char e[64]; } Vec;      // sparse exponent vector mod K
static Vec *V; static int nruns; static int **byp; static int *nbyp;  // runs grouped by max prime
static int f[MAXP]; static long long nodes[MAXP]; static long long sols, maxsols;
static int deepest;
static int *S; static int **mbyp; static char **ebyp; static int *nmbyp;   // members containing prime i
static int **cof;   // cof[i][t*L+m] = exponent of prime i in member m of run byp[i][t]
static int splitd = -1, job = 0, njobs = 1; static long long splitcnt;

static void vec(uint64_t n, Vec *v) {
  v->n = 0;
  for (int j = 0; j < np && n > 1; j++) { int e = 0; while (n % P[j] == 0) { n /= P[j]; e++; }
    if (e % K) { v->idx[v->n] = j; v->e[v->n] = e % K; v->n++; } }
  if (n != 1) { fprintf(stderr, "not smooth\n"); exit(1); }
}
static int allowed_mask(int i, int anynz) {
  int allowed = (1 << K) - 1;
  if (!anynz) allowed = 3;                        // symmetry: first nonzero value is 1 (k prime)
  for (int t = 0; t < nbyp[i] && allowed; t++) {
    int r = byp[i][t]; int forb = allowed;
    for (int m = 0; m < L; m++) {
      int a = S[r * L + m] % K, c = cof[i][t * L + m];
      int ok = 0;                                  // values x with a + c x == 0
      for (int x = 0; x < K; x++) if ((a + c * x) % K == 0) ok |= 1 << x;
      forb &= ok; if (!forb) break;
    }
    allowed &= ~forb;
  }
  return allowed;
}
static void assign(int i, int x, int sign) {
  if (x) for (int q = 0; q < nmbyp[i]; q++) S[mbyp[i][q]] += sign * ebyp[i][q] * x;
}
static void dfs(int i, int anynz) {
  nodes[i]++;
  if (i > deepest) deepest = i;
  if (i == np) { sols++; if (sols <= 5) { printf("SOL:"); for (int j = 0; j < np; j++) printf(" %d:%d", P[j], f[j]); printf("\n"); fflush(stdout); }
                 return; }
  int allowed = allowed_mask(i, anynz);
  if (i == splitd) { long long me = splitcnt++; if (me % njobs != job) return; }
  if (nodes[i] % (1 << 24) == 0 && i > 0) { fprintf(stderr, "progress depth %d nodes %lld path ", i, nodes[i]);
      for (int j = 0; j < i && j < 40; j++) fprintf(stderr, "%d", f[j]); fprintf(stderr, "\n"); }
  for (int x = 0; x < K; x++) if (allowed >> x & 1) {
    f[i] = x; assign(i, x, 1);
    dfs(i + 1, anynz || x);
    assign(i, x, -1);
    if (maxsols > 0 && sols >= maxsols) return;
  }
}
// Knuth's estimator: random root-leaf probes; E[prod of branching] = #nodes.
static void knuth(long long probes) {
  double tot = 0, sumsq = 0; double perdepth[MAXP] = {0}; long long reach = 0; srand(12345);
  for (long long t = 0; t < probes; t++) {
    double w = 1, est = 1; int anynz = 0, i;
    for (i = 0; i < np; i++) {
      int a = allowed_mask(i, anynz); int ch[8], nc = 0;
      for (int x = 0; x < K; x++) if (a >> x & 1) ch[nc++] = x;
      if (!nc) break;
      w *= nc; est += w; perdepth[i + 1] += w;
      int x = ch[rand() % nc]; f[i] = x; assign(i, x, 1); anynz |= x;
    }
    if (i == np) reach++;
    for (int j = i - 1; j >= 0; j--) assign(j, f[j], -1);
    tot += est; sumsq += est * est;
  }
  double mean = tot / probes;
  printf("knuth probes=%lld est_nodes=%.3e (sd of mean %.2e) probes_reaching_leaf=%lld\n", probes, mean,
         sqrt(sumsq / probes - mean * mean) / sqrt((double)probes), reach);
  printf("est nodes by depth:"); for (int i = 0; i <= np; i++) printf(" %.2e", perdepth[i] / probes); printf("\n");
}
int main(int argc, char **argv) {
  K = atoi(argv[1]); L = atoi(argv[2]); Y = atoi(argv[3]); maxsols = argc > 5 ? atoll(argv[5]) : 1;
  for (int p = 2; p <= Y; p++) { int ok = 1; for (int d = 2; d * d <= p; d++) if (p % d == 0) { ok = 0; break; } if (ok) P[np++] = p; }
  FILE *fh = fopen(argv[4], "r"); int cap = 1 << 16; uint64_t *rs = malloc(cap * 8); unsigned long long x;
  while (fscanf(fh, "%llu", &x) == 1) { if (nruns == cap) { cap *= 2; rs = realloc(rs, cap * 8); } rs[nruns++] = x; }
  V = malloc(sizeof(Vec) * nruns * L); nbyp = calloc(np, sizeof(int)); byp = malloc(np * sizeof(int *));
  int *mx = malloc(nruns * sizeof(int));
  for (int r = 0; r < nruns; r++) { int m = -1; for (int j = 0; j < L; j++) { vec(rs[r] + j, &V[r * L + j]);
      Vec *v = &V[r * L + j]; for (int q = 0; q < v->n; q++) if (v->idx[q] > m) m = v->idx[q]; }
    mx[r] = m; }
  for (int r = 0; r < nruns; r++) if (mx[r] >= 0) nbyp[mx[r]]++;
  for (int i = 0; i < np; i++) { byp[i] = malloc((nbyp[i] + 1) * sizeof(int)); nbyp[i] = 0; }
  int trivial = 0;
  for (int r = 0; r < nruns; r++) { if (mx[r] < 0) trivial++; else byp[mx[r]][nbyp[mx[r]]++] = r; }
  if (trivial) { printf("run with all-zero exponent vectors -> UNSAT trivially\n"); return 0; }
  if (argc > 8) { splitd = atoi(argv[6]); job = atoi(argv[7]); njobs = atoi(argv[8]); }
  S = calloc((size_t)nruns * L, sizeof(int)); nmbyp = calloc(np, sizeof(int));
  mbyp = malloc(np * sizeof(int *)); ebyp = malloc(np * sizeof(char *));
  for (int r = 0; r < nruns * L; r++) for (int q = 0; q < V[r].n; q++) nmbyp[V[r].idx[q]]++;
  for (int i = 0; i < np; i++) { mbyp[i] = malloc((nmbyp[i] + 1) * sizeof(int)); ebyp[i] = malloc(nmbyp[i] + 1); nmbyp[i] = 0; }
  for (int r = 0; r < nruns * L; r++) for (int q = 0; q < V[r].n; q++) { int i = V[r].idx[q];
      mbyp[i][nmbyp[i]] = r; ebyp[i][nmbyp[i]] = V[r].e[q]; nmbyp[i]++; }
  cof = malloc(np * sizeof(int *));
  for (int i = 0; i < np; i++) { cof[i] = malloc((nbyp[i] * L + 1) * sizeof(int));
    for (int t = 0; t < nbyp[i]; t++) for (int m = 0; m < L; m++) { Vec *v = &V[byp[i][t] * L + m]; int c = 0;
        for (int q = 0; q < v->n; q++) if (v->idx[q] == i) c = v->e[q]; cof[i][t * L + m] = c; } }
  if (maxsols < 0) { knuth(-maxsols); return 0; }
  dfs(0, 0);
  long long tot = 0; for (int i = 0; i <= np; i++) tot += nodes[i];
  printf("k=%d l=%d y=%d runs=%d primes=%d nodes=%lld sols=%lld%s deepest=%d\n", K, L, Y, nruns, np, tot, sols,
         (maxsols && sols >= maxsols) ? "+" : "", deepest);
  printf("nodes by depth:"); for (int i = 0; i <= np; i++) printf(" %lld", nodes[i]); printf("\n");
  return 0;
}

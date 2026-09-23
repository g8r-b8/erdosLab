// mrvdfs: DFS / Knuth tree-size estimator for the weakened instance F_y(X) with
//   * forward checking over ALL smooth runs (a run constrains a prime q as soon as q is the only
//     unassigned prime of the run and no fully-assigned member is nonzero),
//   * dynamic variable ordering (static increasing, MRV, MRV + degree tie-break),
//   * fixed partial assignments ("lemma cubes"), e.g. --fix 2=1 or --fix 2=0,3=1.
// Soundness (same as sdfs.c): every completely additive f restricted to primes <= y with no zero
// run r..r+l-1 among the listed smooth runs is a leaf of this search; the search never prunes a
// value unless some listed run would be all-zero.  Symmetry: when no --fix is given, the first
// nonzero value on the path is normalised to 1 (valid for k prime: values before the first nonzero
// are all 0, so the path order is the same for f and u*f).  With --fix, normalisation stays on;
// the first nonzero value in the fix list must itself be 1 (caller's responsibility).
//
// Usage: mrvdfs k l y runs.txt [--fix p=v,...] [--order inc|mrv|mrvdeg] [--knuth N] [--seed S]
//                               [--maxnodes N] [--maxsols N] [--nosym]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXP 4096
#define MAXK 8

typedef struct { int n; int *idx; unsigned char *e; } Member;   // sparse exponent vector mod K

// ---- global state (filled by load_instance / build_index) ----
static int K, L, Y, np, P[MAXP];
static int nruns; static Member *M;          // M[r*L+m]
static int **rprimes, *nrprimes;             // distinct primes of run r
static int **qruns, *nqruns;                 // runs containing prime q
static int **qmem, *nqmem; static unsigned char **qexp;  // members containing q, exponent
static int *ucnt;                            // # unassigned distinct primes of run r
static int *msum, *mun;                      // member partial sum (mod K), # unassigned primes
static int *satm;                            // # fully assigned members of run r with nonzero sum
static int forb[MAXP][MAXK];                 // # runs forbidding value x for prime q
static int cnt2[MAXP];                       // # unsatisfied runs where q is one of last 2 unassigned
static int val[MAXP];                        // -1 = unassigned
static int order_mode = 1, symmetry = 1, anynz0 = 0;
typedef struct { int kind, q, x; } TrailEnt; // kind 0 = forb[q][x]++, 1 = cnt2[q]++
static TrailEnt *trail; static long long ntrail, captrail;


/* load_instance
 * TODO: read primes <= y and the run list; factor r, r+1, ..., r+L-1 into sparse exponent vectors
 *       mod K (exponents divisible by K dropped).
 * What's missing: everything.
 * Acceptance: np == pi(y); every member factors completely over P (else exit(1) "not smooth").
 * Depends on: nothing. */
static void load_instance(const char *path);

/* build_index
 * TODO: build rprimes/qruns/qmem incidence lists, initialise ucnt/mun/msum/satm, and the
 *       initial forbidden values of runs that start with ucnt == 1 (and cnt2 for ucnt == 2).
 * What's missing: everything.
 * Acceptance: sum over q of nqruns[q] == sum over r of nrprimes[r]; a run with 0 primes aborts
 *       ("trivially UNSAT").
 * Depends on: load_instance. */
static void build_index(void);

/* forbidden_value
 * TODO: for run r whose only unassigned prime is q and with satm[r] == 0, return the unique x
 *       with all members zero when f(q)=x, or -1 if no such x exists.
 * What's missing: everything.
 * Acceptance: brute-force agrees on random states (tested via --selftest).
 * Depends on: build_index. */
static int forbidden_value(int r, int q);

/* assign
 * TODO: set val[q]=x, update member sums/mun/satm, decrement ucnt of runs containing q and push
 *       new forbidden values / cnt2 increments on the trail.  Returns the trail mark to undo to.
 * What's missing: everything.
 * Acceptance: assign followed by unassign restores all counters exactly (selftest).
 * Depends on: forbidden_value. */
static long long assign(int q, int x);

/* unassign
 * TODO: undo assign(q, x): pop trail entries down to `mark`, restore sums/mun/satm/ucnt.
 * What's missing: everything.
 * Acceptance: see assign.
 * Depends on: assign. */
static void unassign(int q, int x, long long mark);

/* domain
 * TODO: bitmask of allowed values of unassigned prime q (forb == 0), restricted to {0,1} when
 *       symmetry is on and no nonzero value has been assigned on the path.
 * Depends on: assign. */
static int domain(int q, int anynz);

/* pick_var
 * TODO: choose next unassigned prime per order_mode: 0 = smallest index; 1 = MRV (fewest allowed
 *       values, tie smallest index); 2 = MRV with tie-break max cnt2.  Returns -1 if all assigned;
 *       sets *dom to its domain mask.
 * Depends on: domain. */
static int pick_var(int anynz, int *dom);

/* dfs
 * TODO: exhaustive search with node counts per depth; stop after maxnodes (reports "ABORT") or
 *       maxsols solutions (prints SOL lines).
 * Acceptance: order inc on k=3 y=300 X=1e8 gives the same node count as sdfs.c (31,538 nodes)
 *       modulo the forward-checking difference (must also be UNSAT).
 * Depends on: pick_var, assign, unassign. */
static void dfs(int depth, int anynz);

/* knuth
 * TODO: Knuth random-probe estimate of the dfs tree size under the same ordering; print mean,
 *       standard error, per-depth estimated widths, and mean probe death depth.
 * Depends on: pick_var, assign, unassign. */
static void knuth(long long probes, unsigned seed);

/* parse_fix
 * TODO: parse "p=v,p=v" and assign them (in given order) before search; conflict => print
 *       "FIX-CONFLICT" (the cube is refuted by propagation alone) and exit 0.
 * Depends on: assign. */
static void parse_fix(const char *s);

static uint64_t *RS;                           // run starts
static long long maxnodes = 0, totnodes = 0, sols = 0, maxsols = 1; static int aborted = 0;
static long long nodes_at[MAXP + 1]; static int deepest = 0;
static int inv[MAXK];

static void push(int kind, int q, int x) {
  if (ntrail == captrail) { captrail = captrail ? 2 * captrail : 1 << 20; trail = realloc(trail, captrail * sizeof(TrailEnt)); }
  trail[ntrail].kind = kind; trail[ntrail].q = q; trail[ntrail].x = x; ntrail++;
  if (kind == 0) forb[q][x]++; else if (kind == 1) cnt2[q]++; else cnt2[q]--;
}

/* load_instance: see contract above. */
static void load_instance(const char *path) {
  for (int p = 2; p <= Y; p++) { int ok = 1; for (int d = 2; d * d <= p; d++) if (p % d == 0) { ok = 0; break; } if (ok) P[np++] = p; }
  FILE *fh = fopen(path, "r"); if (!fh) { perror(path); exit(1); }
  int cap = 1 << 16; RS = malloc(cap * sizeof(uint64_t)); unsigned long long x;
  while (fscanf(fh, "%llu", &x) == 1) { if (nruns == cap) { cap *= 2; RS = realloc(RS, cap * sizeof(uint64_t)); } RS[nruns++] = x; }
  fclose(fh);
  M = malloc(sizeof(Member) * (size_t)nruns * L);
  int ti[64]; unsigned char te[64];
  for (long long mm = 0; mm < (long long)nruns * L; mm++) {
    uint64_t n = RS[mm / L] + mm % L; int c = 0;
    for (int j = 0; j < np && n > 1; j++) { int e = 0; while (n % P[j] == 0) { n /= P[j]; e++; }
      if (e % K) { ti[c] = j; te[c] = e % K; c++; } }
    if (n != 1) { fprintf(stderr, "not smooth: %llu\n", (unsigned long long)(RS[mm / L] + mm % L)); exit(1); }
    M[mm].n = c; M[mm].idx = malloc(sizeof(int) * (c + 1)); M[mm].e = malloc(c + 1);
    memcpy(M[mm].idx, ti, sizeof(int) * c); memcpy(M[mm].e, te, c);
  }
  for (int a = 1; a < K; a++) for (int b = 1; b < K; b++) if (a * b % K == 1) inv[a] = b;
}

/* build_index: see contract above. */
static void build_index(void) {
  rprimes = malloc(sizeof(int *) * nruns); nrprimes = calloc(nruns, sizeof(int));
  nqruns = calloc(np, sizeof(int)); nqmem = calloc(np, sizeof(int));
  int *seen = calloc(np, sizeof(int)); int tmp[256];
  for (int r = 0; r < nruns; r++) {
    int c = 0;
    for (int m = 0; m < L; m++) { Member *v = &M[(size_t)r * L + m];
      for (int t = 0; t < v->n; t++) { int q = v->idx[t]; nqmem[q]++; if (seen[q] != r + 1) { seen[q] = r + 1; tmp[c++] = q; } } }
    rprimes[r] = malloc(sizeof(int) * (c + 1)); memcpy(rprimes[r], tmp, sizeof(int) * c); nrprimes[r] = c;
    for (int t = 0; t < c; t++) nqruns[tmp[t]]++;
  }
  free(seen);
  qruns = malloc(sizeof(int *) * np); qmem = malloc(sizeof(int *) * np); qexp = malloc(sizeof(unsigned char *) * np);
  for (int q = 0; q < np; q++) { qruns[q] = malloc(sizeof(int) * (nqruns[q] + 1)); qmem[q] = malloc(sizeof(int) * (nqmem[q] + 1));
    qexp[q] = malloc(nqmem[q] + 1); nqruns[q] = 0; nqmem[q] = 0; }
  for (int r = 0; r < nruns; r++) {
    for (int t = 0; t < nrprimes[r]; t++) { int q = rprimes[r][t]; qruns[q][nqruns[q]++] = r; }
    for (int m = 0; m < L; m++) { int mm = r * L + m; Member *v = &M[mm];
      for (int t = 0; t < v->n; t++) { int q = v->idx[t]; qmem[q][nqmem[q]] = mm; qexp[q][nqmem[q]] = v->e[t]; nqmem[q]++; } }
  }
  ucnt = malloc(sizeof(int) * nruns); satm = calloc(nruns, sizeof(int));
  msum = calloc((size_t)nruns * L, sizeof(int)); mun = malloc(sizeof(int) * (size_t)nruns * L);
  for (long long mm = 0; mm < (long long)nruns * L; mm++) mun[mm] = M[mm].n;
  for (int q = 0; q < np; q++) val[q] = -1;
  for (int r = 0; r < nruns; r++) {
    ucnt[r] = nrprimes[r];
    if (ucnt[r] == 0) { printf("run %llu has all-zero exponent vectors -> trivially UNSAT\n", (unsigned long long)RS[r]); exit(0); }
    if (ucnt[r] == 1) { int q = rprimes[r][0]; int x = forbidden_value(r, q); if (x >= 0) forb[q][x]++; }
    else if (ucnt[r] == 2) { cnt2[rprimes[r][0]]++; cnt2[rprimes[r][1]]++; }
  }
}

/* forbidden_value: see contract above. */
static int forbidden_value(int r, int q) {
  int x = -1;
  for (int m = 0; m < L; m++) {
    Member *v = &M[(size_t)r * L + m]; int c = 0;
    for (int t = 0; t < v->n; t++) if (v->idx[t] == q) c = v->e[t];
    int a = msum[r * L + m];
    if (c == 0) { if (a != 0) return -1; continue; }
    int xm = ((K - a) % K) * inv[c] % K;
    if (x >= 0 && x != xm) return -1;
    x = xm;
  }
  return x;
}

static long long violations = 0;
/* assign: see contract above. */
static long long assign(int q, int x) {
  long long mark = ntrail; val[q] = x;
  for (int t = 0; t < nqmem[q]; t++) { int mm = qmem[q][t];
    msum[mm] = (msum[mm] + qexp[q][t] * x) % K;
    if (--mun[mm] == 0 && msum[mm]) satm[mm / L]++; }
  for (int t = 0; t < nqruns[q]; t++) { int r = qruns[q][t]; int u = --ucnt[r];
    if (satm[r]) continue;
    if (u == 1 || u == 2) {
      int a = -1, b = -1;
      for (int s = 0; s < nrprimes[r]; s++) { int w = rprimes[r][s]; if (val[w] < 0) { if (a < 0) a = w; else b = w; } }
      if (u == 1) { int fx = forbidden_value(r, a); if (fx >= 0) push(0, a, fx); if (order_mode == 2) push(2, a, 0); }
      else if (order_mode == 2) { push(1, a, 0); push(1, b, 0); }
    } else if (u == 0) violations++;   // cannot happen when x was in the domain
  }
  return mark;
}

/* unassign: see contract above. */
static void unassign(int q, int x, long long mark) {
  while (ntrail > mark) { TrailEnt *e = &trail[--ntrail];
    if (e->kind == 0) forb[e->q][e->x]--; else if (e->kind == 1) cnt2[e->q]--; else cnt2[e->q]++; }
  for (int t = 0; t < nqruns[q]; t++) ucnt[qruns[q][t]]++;
  for (int t = 0; t < nqmem[q]; t++) { int mm = qmem[q][t];
    if (mun[mm]++ == 0 && msum[mm]) satm[mm / L]--;
    msum[mm] = (msum[mm] + (K - qexp[q][t]) * x) % K; }
  val[q] = -1;
}

/* domain: see contract above. */
static int domain(int q, int anynz) {
  int d = 0; for (int x = 0; x < K; x++) if (!forb[q][x]) d |= 1 << x;
  if (symmetry && !anynz) d &= 3;
  return d;
}

/* pick_var: see contract above. */
static int pick_var(int anynz, int *dom) {
  int best = -1, bc = 99, bd = 0, b2 = -1;
  for (int q = 0; q < np; q++) { if (val[q] >= 0) continue;
    int d = domain(q, anynz);
    if (order_mode == 0) { *dom = d; return q; }
    int c = __builtin_popcount(d);
    if (c < bc || (c == bc && order_mode == 2 && cnt2[q] > b2)) { best = q; bc = c; bd = d; b2 = cnt2[q]; if (c == 0) break; }
  }
  *dom = bd; return best;
}

static int check_full(void) {   // independent check of a complete assignment against every run
  for (int r = 0; r < nruns; r++) { int allz = 1;
    for (int m = 0; m < L && allz; m++) { Member *v = &M[(size_t)r * L + m]; int s = 0;
      for (int t = 0; t < v->n; t++) s += v->e[t] * val[v->idx[t]];
      if (s % K) allz = 0; }
    if (allz) return 0; }
  return 1;
}

/* dfs: see contract above. */
static void dfs(int depth, int anynz) {
  nodes_at[depth]++; totnodes++; if (depth > deepest) deepest = depth;
  if (maxnodes && totnodes >= maxnodes) { aborted = 1; return; }
  int dom, q = pick_var(anynz, &dom);
  if (q < 0) { sols++;
    printf("SOL%s:", check_full() ? "" : "(CHECK FAILED)"); for (int j = 0; j < np; j++) printf(" %d:%d", P[j], val[j]); printf("\n"); fflush(stdout);
    return; }
  for (int x = 0; x < K; x++) if (dom >> x & 1) {
    long long mk = assign(q, x); dfs(depth + 1, anynz || x); unassign(q, x, mk);
    if (aborted || (maxsols > 0 && sols >= maxsols)) return;
  }
}

/* knuth: see contract above. */
static void knuth(long long probes, unsigned seed) {
  srand(seed); double tot = 0, sumsq = 0, dsum = 0; static double perdepth[MAXP + 1];
  static int sq[MAXP], sx[MAXP]; static long long sm[MAXP]; long long reach = 0;
  static long long firstq[MAXP];
  for (long long t = 0; t < probes; t++) {
    double w = 1, est = 1; int anynz = anynz0, d = 0;
    perdepth[0] += 1;
    for (;;) { int dom, q = pick_var(anynz, &dom);
      if (q < 0) { reach++; break; }
      if (d == 0) firstq[q]++;
      int ch[MAXK], nc = 0; for (int x = 0; x < K; x++) if (dom >> x & 1) ch[nc++] = x;
      if (!nc) break;
      w *= nc; est += w; perdepth[d + 1] += w;
      int x = ch[rand() % nc]; sq[d] = q; sx[d] = x; sm[d] = assign(q, x); anynz |= x; d++; }
    dsum += d;
    for (int j = d - 1; j >= 0; j--) unassign(sq[j], sx[j], sm[j]);
    tot += est; sumsq += est * est;
  }
  double mean = tot / probes;
  printf("knuth probes=%lld est_nodes=%.3e (sd of mean %.2e) mean_death_depth=%.1f probes_reaching_leaf=%lld\n",
         probes, mean, sqrt(fmax(0, sumsq / probes - mean * mean)) / sqrt((double)probes), dsum / probes, reach);
  printf("est width by depth:"); for (int i = 0; i <= np; i++) { if (perdepth[i] == 0) break; printf(" %.2e", perdepth[i] / probes); } printf("\n");
}

/* parse_fix: see contract above. */
static void parse_fix(const char *s) {
  char *buf = strdup(s), *tok = strtok(buf, ",");
  while (tok) { int p, v; if (sscanf(tok, "%d=%d", &p, &v) != 2) { fprintf(stderr, "bad fix %s\n", tok); exit(1); }
    int q = -1; for (int j = 0; j < np; j++) if (P[j] == p) q = j;
    if (q < 0 || v < 0 || v >= K) { fprintf(stderr, "bad fix %s\n", tok); exit(1); }
    if (val[q] >= 0) { if (val[q] != v) { printf("FIX-CONFLICT at %d=%d\n", p, v); exit(0); } }
    else { if (forb[q][v]) { printf("FIX-CONFLICT at %d=%d (forbidden by propagation)\n", p, v); exit(0); }
      assign(q, v); if (v) anynz0 = 1; }
    tok = strtok(NULL, ","); }
  free(buf);
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: mrvdfs k l y runs.txt [--fix p=v,...] [--order inc|mrv|mrvdeg] [--knuth N] [--seed S] [--maxnodes N] [--maxsols N] [--nosym]\n"); return 1; }
  K = atoi(argv[1]); L = atoi(argv[2]); Y = atoi(argv[3]);
  const char *fix = NULL; long long probes = 0; unsigned seed = 12345;
  for (int i = 5; i < argc; i++) {
    if (!strcmp(argv[i], "--fix")) fix = argv[++i];
    else if (!strcmp(argv[i], "--order")) { i++; order_mode = !strcmp(argv[i], "inc") ? 0 : !strcmp(argv[i], "mrv") ? 1 : 2; }
    else if (!strcmp(argv[i], "--knuth")) probes = atoll(argv[++i]);
    else if (!strcmp(argv[i], "--seed")) seed = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--maxnodes")) maxnodes = atoll(argv[++i]);
    else if (!strcmp(argv[i], "--maxsols")) maxsols = atoll(argv[++i]);
    else if (!strcmp(argv[i], "--nosym")) symmetry = 0;
    else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 1; }
  }
  load_instance(argv[4]); build_index();
  if (fix) parse_fix(fix);
  if (probes) { knuth(probes, seed); return 0; }
  dfs(0, anynz0);
  printf("k=%d l=%d y=%d runs=%d primes=%d fix=%s order=%d nodes=%lld sols=%lld%s deepest=%d violations=%lld %s\n", K, L, Y, nruns, np,
         fix ? fix : "-", order_mode, totnodes, sols, (maxsols > 0 && sols >= maxsols) ? "+" : "", deepest, violations,
         aborted ? "ABORTED(maxnodes)" : (sols ? "SAT" : "UNSAT(exhaustive)"));
  return 0;
}

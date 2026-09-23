// mrvdfs: DFS / Knuth tree-size estimator for the weakened instance F_y(X) with
//   * forward checking over ALL smooth runs (a run constrains a prime q as soon as q is the only
//     unassigned prime of the run and no fully-assigned member is nonzero),
//   * dynamic variable ordering (static increasing, MRV, MRV + degree tie-break),
//   * fixed partial assignments ("lemma cubes"), e.g. --fix 2=1 or --fix 2=0,3=1.
// Soundness (same as sdfs.c): every completely additive f restricted to primes <= y with no zero
// run r..r+l-1 among the listed smooth runs is a leaf of this search; the search never prunes a
// value unless some listed run would be all-zero.  Symmetry: when no --fix is given, the first
// nonzero value on the path is normalised to 1 (valid for k prime: values before the first nonzero
// are all 0, so the path order is the same for f and u*f).  With --fix, normalisation is off unless
// --sym is given; the caller is responsible for the fix list being unit-normalised.
//
// Usage: mrvdfs k l y runs.txt [--fix p=v,...] [--order inc|mrv|mrvdeg] [--knuth N] [--seed S]
//                               [--maxnodes N] [--maxsols N] [--sym]
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

int main(int argc, char **argv) {
  (void)argc; (void)argv;
  fprintf(stderr, "mrvdfs: NotImplemented (skeleton)\n");
  return 2;
}

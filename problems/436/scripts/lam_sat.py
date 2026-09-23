"""SAT model for Lehmer's Lambda(k, l) (Erdos problem #436).

Combinatorial model: Lam_comb(k, l) = max over completely additive f: Z_{>0} -> Z/k of the
least r >= 1 with f(r) = f(r+1) = ... = f(r+l-1) = 0.   (See ../README.md for the reduction.)

S(R) := "exists f with no zero-run of length l starting at any r <= R".  S is monotone
(SAT at R => SAT at all R' < R), only primes <= R+l-1 matter, and Lam_comb = min{R : S(R) UNSAT}.
"""
from __future__ import annotations
from typing import Dict, List, Optional, Tuple


def spf_sieve(n: int) -> List[int]:
    """TODO: smallest-prime-factor table for 0..n.
    What's missing: body.  Acceptance: spf[p]==p for primes, spf[1]==1.  Depends on: nothing."""
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


class LamEncoder:
    """Incremental CNF encoder: one-hot y[n][v] (v in Z/k) for every 2 <= n <= N.

    For prime n: fresh vars, ALO (+AMO).  For composite n = p*m (p = spf(n)):
    forward clauses y[p][a] & y[m][b] -> y[n][a+b] (k^2 ternary clauses) plus ALO/AMO on y[n].
    Triple (l-run) clauses: OR_{i<l} not y[r+i][0] for r <= R.  Symmetry (k prime): the first
    prime with nonzero value has value 1 (aux chain s_i = "some prime among first i is nonzero").
    """

    def __init__(self, k: int, l: int, sym: bool = True, amo: bool = True) -> None:
        """TODO: set up counters/state.  Acceptance: no clauses yet, N=1.  Depends on: spf_sieve."""
        self.k, self.l, self.sym, self.amo = k, l, sym, amo
        self.N, self.R = 1, 0
        self.nv = 0
        self.base: Dict[int, int] = {}
        self.primes: List[int] = []
        self.s_prev: Optional[int] = None          # chain var "some earlier prime nonzero"
        self.spf = spf_sieve(1024)
        ds = [d for d in range(1, k) if k % d == 0]
        self.allowed_first = set(ds)             # orbit representatives of Z/k under units

    def extend_to(self, N: int) -> List[List[int]]:
        """TODO: add variables/clauses for all n in (self.N, N]; return the new clauses.
        Acceptance: validated by reproducing Lam(2,2)=9, Lam(3,2)=77.  Depends on: spf_sieve."""
        k = self.k
        if N <= self.N:
            return []
        if N >= len(self.spf):
            self.spf = spf_sieve(max(N, 2 * len(self.spf)))
        spf, base = self.spf, self.base
        cl: List[List[int]] = []
        for n in range(self.N + 1, N + 1):
            b = self.nv + 1
            self.nv += k
            base[n] = b
            ys = list(range(b, b + k))
            cl.append(ys)                                   # ALO
            if self.amo or spf[n] == n:
                for i in range(k):
                    for j in range(i + 1, k):
                        cl.append([-ys[i], -ys[j]])
            p = spf[n]
            if p == n:
                self.primes.append(n)
                if self.sym:
                    prev = self.s_prev
                    for v in range(1, k):
                        if v not in self.allowed_first:
                            cl.append([-ys[v]] + ([prev] if prev else []))
                    self.nv += 1
                    s = self.nv
                    # s <-> prev or not y0
                    cl.append([-s, -ys[0]] + ([prev] if prev else []))
                    if prev:
                        cl.append([-prev, s])
                    cl.append([ys[0], s])
                    self.s_prev = s
            else:
                m = n // p
                bp = base[p]
                if m == 1:
                    raise AssertionError
                bm = base[m]
                for a in range(k):
                    for c in range(k):
                        cl.append([-(bp + a), -(bm + c), b + (a + c) % k])
        self.N = N
        return cl

    def forbid_runs_upto(self, R: int) -> List[List[int]]:
        """TODO: add run-clauses for r in (self.R, R] (extends to N=R+l-1 first); return new clauses."""
        l = self.l
        if R <= self.R:
            return []
        cl = self.extend_to(R + l - 1)
        for r in range(self.R + 1, R + 1):
            c = [-self.base[n] for n in range(r, r + l) if n != 1]
            cl.append(c)
        self.R = R
        return cl

    def decode(self, model: List[int]) -> Dict[int, int]:
        """TODO: return {prime p <= N: f(p)} from a SAT model."""
        pos = set(x for x in model if x > 0)
        out = {}
        for p in self.primes:
            b = self.base[p]
            vals = [v for v in range(self.k) if b + v in pos]
            assert len(vals) == 1, (p, vals)
            out[p] = vals[0]
        return out


def first_run(fp: Dict[int, int], k: int, l: int, limit: int) -> Tuple[int, Dict[int, int]]:
    """TODO: extend f from primes in fp greedily (new primes get value 1, i.e. nonzero) and return
    (first r with an l-run of zeros, extended prime dict).  Acceptance: consistent with SAT."""
    spf = spf_sieve(limit + l)
    f = [0] * (limit + l + 1)
    ext = dict(fp)
    run = 1        # f(1) = 0
    if run >= l:
        return 1, ext
    for n in range(2, limit + l + 1):
        p = spf[n]
        if p == n:
            if n not in ext:
                ext[n] = 1
            f[n] = ext[n] % k
        else:
            f[n] = (f[p] + f[n // p]) % k
        run = run + 1 if f[n] == 0 else 0
        if run >= l:
            return n - l + 1, ext
    return limit + 1, ext


def search_lambda(k: int, l: int, R0: int = 1, log=print, proof_dir: Optional[str] = None) -> int:
    """TODO: incremental search: solve S(R); if SAT jump R to first_run of model; stop at UNSAT.
    Returns Lam_comb(k, l).  Depends on: LamEncoder, first_run, pysat Cadical153."""
    from pysat.solvers import Cadical153
    import time
    t0 = time.time()
    enc = LamEncoder(k, l)
    S = Cadical153()
    R = R0
    S.append_formula(enc.forbid_runs_upto(R))
    lim = 1024
    while True:
        ok = S.solve()
        if not ok:
            log(f"UNSAT at R={R}  vars={enc.nv} primes={len(enc.primes)} t={time.time()-t0:.1f}s")
            S.delete()
            return R
        fp = enc.decode(S.get_model())
        while True:
            t, _ = first_run(fp, k, l, lim)
            if t <= lim:
                break
            lim *= 2
            if lim > 10 ** 8:
                raise RuntimeError("model f has no run below 1e8")
        assert t > R
        log(f"SAT R={R}: model first run at {t}  vars={enc.nv} t={time.time()-t0:.1f}s")
        R = t
        S.append_formula(enc.forbid_runs_upto(R))


def write_dimacs(k: int, l: int, R: int, path: str, sym: bool = True) -> Tuple[int, int]:
    """TODO: write the CNF for S(R) (fresh, non-incremental) to path; return (nvars, nclauses)."""
    enc = LamEncoder(k, l, sym=sym)
    cl = enc.forbid_runs_upto(R)
    with open(path, "w") as fh:
        fh.write(f"p cnf {enc.nv} {len(cl)}\n")
        fh.write("".join(" ".join(map(str, c)) + " 0\n" for c in cl))
    return enc.nv, len(cl)


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int); ap.add_argument("l", type=int)
    ap.add_argument("--R0", type=int, default=1)
    ap.add_argument("--dimacs", type=int, default=None, help="write CNF for S(R) and exit")
    ap.add_argument("--out", default="out.cnf")
    a = ap.parse_args()
    if a.dimacs is not None:
        print(write_dimacs(a.k, a.l, a.dimacs, a.out))
    else:
        print("Lambda_comb =", search_lambda(a.k, a.l, a.R0))

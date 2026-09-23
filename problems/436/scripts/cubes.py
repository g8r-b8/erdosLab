"""Cube-and-conquer for the weakened instance F_y(X): split on f(2), f(3), f(5) (after the
unit-scaling symmetry this is 32 cubes), solve worker's share with incremental CaDiCaL.
  python cubes.py k y runs.txt WORKER NWORKERS [--depth 3]
"""
import sys, time, argparse, itertools
from smooth_sat import build
from pysat.solvers import Cadical153


def cubes(k, ps, depth):
    """value tuples for the first `depth` primes consistent with the symmetry breaking
    (first nonzero value is a divisor of k; for k prime: 1)."""
    out = []
    for vals in itertools.product(range(k), repeat=depth):
        nz = [v for v in vals if v]
        if nz and k % nz[0] != 0:
            continue
        out.append(vals)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int); ap.add_argument("y", type=int); ap.add_argument("runs")
    ap.add_argument("w", type=int); ap.add_argument("nw", type=int); ap.add_argument("--depth", type=int, default=3)
    a = ap.parse_args()
    rs = [int(x) for x in open(a.runs)]
    nv, cl, base, ps = build(a.k, 3, a.y, rs)
    S = Cadical153(bootstrap_with=cl)
    cs = cubes(a.k, ps, a.depth)
    t0 = time.time()
    for i, c in enumerate(cs):
        if i % a.nw != a.w:
            continue
        t = time.time()
        assum = [base[ps[j]] + c[j] for j in range(a.depth)]
        ok = S.solve(assumptions=assum)
        print(f"cube {i}/{len(cs)} {c}: {'SAT' if ok else 'UNSAT'} {time.time()-t:.1f}s (total {time.time()-t0:.0f}s)", flush=True)
        if ok:
            m = set(x for x in S.get_model() if x > 0)
            print("f:", " ".join(f"{p}:{[v for v in range(a.k) if base[p]+v in m][0]}" for p in ps), flush=True)
            return


if __name__ == "__main__":
    main()

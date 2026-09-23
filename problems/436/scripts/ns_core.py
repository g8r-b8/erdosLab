"""Linear-algebra certificates for F_y(X) on a small UNSAT core (Erdos #436, algebraic angle).

1. unsat_core: shrink the run list to a (deletion-)minimal UNSAT core, using mrvdfs as the oracle.
2. sampled_ns: test whether 1 = sum_r g_r P_r with deg g_r <= d (P_r = indicator that all three
   members of run r vanish, a function F_k^n -> F_k), by solving the linear system on N random
   evaluation points.  Every point gives one linear equation the certificate must satisfy, so:
     - system on sampled points infeasible  =>  no certificate of that shape exists (exact).
     - system on sampled points feasible     =>  evidence only (the identity may fail elsewhere).

  python ns_core.py core k y runs.txt out_core.txt
  python ns_core.py ns k y core.txt --deg 0 --points 5000
"""
from __future__ import annotations

import argparse
import os
import random
import subprocess
import tempfile
from typing import Dict, List

import numpy as np

from nullstellensatz import primes_upto, run_forms

HERE = os.path.dirname(os.path.abspath(__file__))


def is_unsat(k: int, l: int, y: int, runs: List[int], tmpdir: str) -> bool:
    """mrvdfs oracle: True iff F_y restricted to `runs` is refuted by MRV DFS within 3e5 nodes
    (a capped search is conservative: "not refuted in time" keeps the run in the core).

    Depends on: scripts/mrvdfs (compiled).
    """
    path = os.path.join(tmpdir, "core_try.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(map(str, runs)) + "\n")
    out = subprocess.run([os.path.join(HERE, "mrvdfs"), str(k), str(l), str(y), path, "--maxnodes", "300000"],
                         capture_output=True, text=True).stdout
    if "trivially UNSAT" in out:
        return True
    return "UNSAT(exhaustive)" in out


def unsat_core(k: int, l: int, y: int, runs: List[int], tmpdir: str) -> List[int]:
    """Deletion-minimal UNSAT core: try dropping blocks of size 512, 64, 8, 1.

    Acceptance: result is UNSAT and (after the size-1 pass) dropping any single run makes it SAT.
    """
    assert is_unsat(k, l, y, runs, tmpdir)
    cur = list(runs)
    for bs in (512, 64, 8, 1):
        i = 0
        while i < len(cur):
            trial = cur[:i] + cur[i + bs:]
            if is_unsat(k, l, y, trial, tmpdir):
                cur = trial
            else:
                i += bs
        print(f"block {bs}: core size {len(cur)}", flush=True)
    return cur


def sampled_ns(k: int, y: int, core: List[int], deg: int, npoints: int, seed: int = 1, l: int = 3) -> str:
    """Solve sum_r sum_{|m| <= deg} c_{r,m} m(x) P_r(x) = 1 on npoints random x in F_k^n.

    Supports deg 0 (g_r constant) and deg 1 restricted to g_r = c + sum over the run's own primes
    q of c_q x_q (a sub-family of degree-1 certificates).  Returns "INFEASIBLE" (exact: no certificate of this shape)
    or "FEASIBLE-ON-SAMPLE" (evidence only).
    """
    ps = primes_upto(y)
    n = len(ps)
    rng = np.random.default_rng(seed)
    X = rng.integers(0, k, size=(npoints, n))
    X[0] = 0
    cols = []
    for r in core:
        tri = run_forms(k, l, ps, r)
        ind = np.ones(npoints, dtype=np.int64)
        for v in tri:
            s = np.zeros(npoints, dtype=np.int64)
            for q, e in v.items():
                s += e * X[:, q]
            ind &= (s % k == 0)
        cols.append(ind)
        if deg >= 1:
            for q in sorted({q for v in tri for q in v}):   # multipliers: variables of the run only
                cols.append(ind * X[:, q] % k)
    A = (np.array(cols, dtype=np.int16) % k).T           # npoints x unknowns
    b = np.ones(npoints, dtype=np.int64)
    return "FEASIBLE-ON-SAMPLE" if solvable_mod(k, A, b) else "INFEASIBLE"


def solvable_mod(k: int, A: np.ndarray, b: np.ndarray) -> bool:
    """Is A c = b solvable over F_k?  Gaussian elimination on the augmented matrix."""
    M = np.concatenate([A % k, (b % k)[:, None]], axis=1).astype(np.int16)   # k <= 5: products < 2^15
    rows, cols = M.shape
    r = 0
    for c in range(cols - 1):
        piv = np.nonzero(M[r:, c])[0]
        if not len(piv):
            continue
        p = r + piv[0]
        if p != r:
            M[[r, p]] = M[[p, r]]
        M[r] = M[r] * pow(int(M[r, c]), k - 2, k) % k
        f = M[:, c].copy()
        f[r] = 0
        nz = np.nonzero(f)[0]
        if len(nz):
            M[nz] = (M[nz] - f[nz, None] * M[r]) % k
        r += 1
        if r == rows:
            break
    # inconsistent iff some row is (0 ... 0 | nonzero)
    lhs_zero = ~M[:, :-1].any(axis=1)
    return not (lhs_zero & (M[:, -1] != 0)).any()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["core", "ns"])
    ap.add_argument("k", type=int); ap.add_argument("y", type=int); ap.add_argument("runs")
    ap.add_argument("out", nargs="?")
    ap.add_argument("--deg", type=int, default=0); ap.add_argument("--points", type=int, default=4000)
    ap.add_argument("--l", type=int, default=3)
    a = ap.parse_args()
    runs = [int(x) for x in open(a.runs)]
    if a.mode == "core":
        with tempfile.TemporaryDirectory(dir=os.path.dirname(os.path.abspath(a.out))) as td:
            core = unsat_core(a.k, a.l, a.y, runs, td)
        with open(a.out, "w") as fh:
            fh.write("\n".join(map(str, core)) + "\n")
        print(f"core: {len(core)} runs (from {len(runs)})")
    else:
        print(f"k={a.k} y={a.y} core={len(runs)} deg={a.deg} points={a.points}: "
              f"{sampled_ns(a.k, a.y, runs, a.deg, a.points, l=a.l)}")


if __name__ == "__main__":
    main()

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
    raise NotImplementedError("sieve")


class LamEncoder:
    """Incremental CNF encoder: one-hot y[n][v] (v in Z/k) for every 2 <= n <= N.

    For prime n: fresh vars, ALO (+AMO).  For composite n = p*m (p = spf(n)):
    forward clauses y[p][a] & y[m][b] -> y[n][a+b] (k^2 ternary clauses) plus ALO/AMO on y[n].
    Triple (l-run) clauses: OR_{i<l} not y[r+i][0] for r <= R.  Symmetry (k prime): the first
    prime with nonzero value has value 1 (aux chain s_i = "some prime among first i is nonzero").
    """

    def __init__(self, k: int, l: int, sym: bool = True, amo: bool = True) -> None:
        """TODO: set up counters/state.  Acceptance: no clauses yet, N=1.  Depends on: spf_sieve."""
        raise NotImplementedError("init")

    def extend_to(self, N: int) -> List[List[int]]:
        """TODO: add variables/clauses for all n in (self.N, N]; return the new clauses.
        Acceptance: validated by reproducing Lam(2,2)=9, Lam(3,2)=77.  Depends on: spf_sieve."""
        raise NotImplementedError("extend")

    def forbid_runs_upto(self, R: int) -> List[List[int]]:
        """TODO: add run-clauses for r in (self.R, R] (extends to N=R+l-1 first); return new clauses."""
        raise NotImplementedError("runs")

    def decode(self, model: List[int]) -> Dict[int, int]:
        """TODO: return {prime p <= N: f(p)} from a SAT model."""
        raise NotImplementedError("decode")


def first_run(fp: Dict[int, int], k: int, l: int, limit: int) -> Tuple[int, Dict[int, int]]:
    """TODO: extend f from primes in fp greedily (new primes get value 1, i.e. nonzero) and return
    (first r with an l-run of zeros, extended prime dict).  Acceptance: consistent with SAT."""
    raise NotImplementedError("first_run")


def search_lambda(k: int, l: int, R0: int = 1, log=print, proof_dir: Optional[str] = None) -> int:
    """TODO: incremental search: solve S(R); if SAT jump R to first_run of model; stop at UNSAT.
    Returns Lam_comb(k, l).  Depends on: LamEncoder, first_run, pysat Cadical153."""
    raise NotImplementedError("search")


def write_dimacs(k: int, l: int, R: int, path: str, sym: bool = True) -> Tuple[int, int]:
    """TODO: write the CNF for S(R) (fresh, non-incremental) to path; return (nvars, nclauses)."""
    raise NotImplementedError("dimacs")


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

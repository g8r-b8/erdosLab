"""R8 Charge Lemma: exact regression on integer-lattice sets (Z[omega], Z[i]).

For every maximal clique of a lattice compatibility pool (pool construction as in
r5_b_exact.py: p = 0 forced extreme, all pairwise squared distances <= r2 or == d2) we compute
Delta, Delta2, layers, the Delta2-graph G and its 2-core exactly, enumerate all hooks
(p, w, x) (p extreme, w a middle Delta2-neighbour of p, x != p a Delta2-neighbour of w, x
strictly off line pw) and test:

  CH   Charge Lemma: each (x, orientation) carries at most one hook;
  LD   Lemma D: no two hooks with the same (x, w, orientation);
  CC   core configuration: no two hooks with the same (x, orientation), distinct w;
  EX   every hook endpoint x lies in V_Delta (Lemma M);
  K8+  mu2 <= |L1| + |L2| + |V_Delta n L1'|   (the consequence, sharpened form).

usage: python3 r8_charge_exact.py tri|sq R2MAX [cap]
"""
from __future__ import annotations

import sys
from collections import Counter

Pt = tuple[int, int]


def cross(o: Pt, a: Pt, b: Pt) -> int:
    """Exact signed area (a-o) x (b-o) in lattice coordinates (orientation-preserving basis).

    TODO: implement.
    What's missing: one-line formula.
    Acceptance: cross((0,0),(1,0),(0,1)) == 1.
    Depends on: nothing.
    """
    raise NotImplementedError("cross product")


def hooks(X: list[Pt], kind: str) -> tuple[list[tuple[int, int, int, int]], dict]:
    """All hooks (p, w, x, orientation) of X plus the exact invariants needed by check_set.

    TODO: implement.
    What's missing: Delta, Delta2, G, layers, 2-core, V_Delta; the hook enumeration.
    Acceptance: on a regular-pentagon-free small set returns [] ; on the lattice runs every
      hook's x satisfies |xb| = Delta for the far-side neighbour b.
    Depends on: va1_common.qform, va1_common.layers, va1_common.two_core, cross.
    """
    raise NotImplementedError("hook enumeration")


def check_set(X: list[Pt], kind: str, C: Counter) -> None:
    """Run the CH, LD, CC, EX, K8+ tests on one set and update the counter.

    TODO: implement.
    What's missing: the tests.
    Acceptance: increments C['sets']; any violation increments C['VIOL <name>'] and prints X.
    Depends on: hooks.
    """
    raise NotImplementedError("per-set tests")


def run(kind: str, r2max: int, cap: int) -> Counter:
    """Enumerate the lattice pools exactly as r5_b_exact.run and test every maximal clique.

    TODO: implement.
    What's missing: pool construction + va1_clique.maximal_cliques loop.
    Acceptance: returns a Counter; 'VIOL *' keys absent.
    Depends on: check_set, va1_clique.maximal_cliques.
    """
    raise NotImplementedError("lattice driver")


def main() -> int:
    """CLI entry: parse args, run, print, return 0 iff no violations.

    TODO: implement.
    What's missing: argument parsing.
    Acceptance: `python3 r8_charge_exact.py tri 13` prints a Counter and exits 0.
    Depends on: run.
    """
    raise NotImplementedError("CLI")


if __name__ == '__main__':
    raise SystemExit(main())

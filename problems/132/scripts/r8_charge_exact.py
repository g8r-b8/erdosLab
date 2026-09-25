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

from va1_common import qform, layers, two_core
from va1_clique import maximal_cliques

Pt = tuple[int, int]


def cross(o: Pt, a: Pt, b: Pt) -> int:
    """Exact signed area (a-o) x (b-o) in lattice coordinates (orientation-preserving basis)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def sgn(v: int) -> int:
    """Sign of an integer."""
    return (v > 0) - (v < 0)


def hooks(X: list[Pt], kind: str) -> tuple[list[tuple[int, int, int, int]], dict]:
    """All hooks (p, w, x, orientation) of X plus the exact invariants needed by check_set.

    A hook is (p, w, x): p a hull vertex, w a Delta2-neighbour of p with Delta2-neighbours of p
    strictly on both sides of line pw, x != p a Delta2-neighbour of w.  The proof shows x is
    never on line pw (counted as 'online' if it happens) and that every Delta2-neighbour b of
    p strictly beyond line pw from x has |xb| = Delta (counted as 'noDelta' if not).
    Orientation = sign of cross(x, w, p).
    """
    n = len(X)
    D = [[qform(kind, X[i][0] - X[j][0], X[i][1] - X[j][1]) for j in range(n)] for i in range(n)]
    vals = sorted({D[i][j] for i in range(n) for j in range(i + 1, n)}, reverse=True)
    info: dict = {'ok': len(vals) >= 2}
    if not info['ok']:
        return [], info
    Dl, D2 = vals[0], vals[1]
    adj = {i: [j for j in range(n) if j != i and D[i][j] == D2] for i in range(n)}
    Ls = layers(X)
    L1 = Ls[0]
    L2 = Ls[1] if len(Ls) > 1 else set()
    core = two_core(L1 | L2, adj)
    VD = {i for i in range(n) if any(D[i][j] == Dl for j in range(n) if j != i)}
    H: list[tuple[int, int, int, int]] = []
    online = noDelta = 0
    for p in L1:
        W = adj[p]
        for w in W:
            sides = {sgn(cross(X[p], X[w], X[a])) for a in W}
            if not (1 in sides and -1 in sides):
                continue
            for x in adj[w]:
                if x == p:
                    continue
                sx = sgn(cross(X[p], X[w], X[x]))
                if sx == 0:
                    online += 1
                    continue
                far = [b for b in W if sgn(cross(X[p], X[w], X[b])) == -sx]
                if any(D[x][b] != Dl for b in far):
                    noDelta += 1
                H.append((p, w, x, sgn(cross(X[x], X[w], X[p]))))
    E = sum(sum(1 for v in adj[q] if v in core) - 2 for q in core & L1)
    info.update(D=D, Dl=Dl, adj=adj, L1=L1, L2=L2, core=core, VD=VD, online=online,
                noDelta=noDelta, mu2=sum(len(a) for a in adj.values()) // 2, E=E)
    return H, info


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

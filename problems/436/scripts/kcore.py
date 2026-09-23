"""k-core reduction of the weakened instance F_y(X) (sound, equisatisfiable).

Lemma (THEORY.md, Lemma 4): fix all values except f(q).  A run containing q forbids at most one value
of f(q) (the members are affine in f(q) with at least one nonzero coefficient, so "all members zero"
has at most one solution).  Hence if q lies in fewer than k runs, every assignment of the other
primes extends to q, and q can be deleted together with all its runs.  Iterating gives the k-core.

  python kcore.py k y runs.txt           prints the core size and the surviving primes
"""
from __future__ import annotations

import sys
from collections import defaultdict
from typing import Dict, List, Set, Tuple


def kcore(k: int, y: int, runs: List[int]) -> Tuple[Set[int], Set[int]]:
    """Return (surviving run starts, surviving primes) of the k-core.

    A run is kept only while all its primes (with exponent not divisible by k) are kept.
    """
    ps = [p for p in range(2, y + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
    prim: Dict[int, Set[int]] = {}
    for r in runs:
        s: Set[int] = set()
        for n in (r, r + 1, r + 2):
            for p in ps:
                if n == 1:
                    break
                e = 0
                while n % p == 0:
                    n //= p
                    e += 1
                if e % k:
                    s.add(p)
            assert n == 1, "not smooth"
        prim[r] = s
    inc: Dict[int, Set[int]] = defaultdict(set)
    for r, s in prim.items():
        for p in s:
            inc[p].add(r)
    alive_runs = set(prim)
    stack = [p for p in inc if len(inc[p]) < k]
    dead_p: Set[int] = set()
    while stack:
        p = stack.pop()
        if p in dead_p:
            continue
        dead_p.add(p)
        for r in list(inc[p]):
            if r in alive_runs:
                alive_runs.discard(r)
                for q in prim[r]:
                    inc[q].discard(r)
                    if q not in dead_p and len(inc[q]) < k:
                        stack.append(q)
    alive_p = {p for p in inc if p not in dead_p and inc[p]}
    return alive_runs, alive_p


if __name__ == "__main__":
    k, y = int(sys.argv[1]), int(sys.argv[2])
    rs = [int(x) for x in open(sys.argv[3])]
    ar, ap = kcore(k, y, rs)
    print(f"k={k} y={y} runs={len(rs)} -> {k}-core runs={len(ar)} primes={len(ap)} (max prime {max(ap) if ap else None})")

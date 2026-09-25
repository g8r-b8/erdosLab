"""Cross-check the enumeration against Amato–Hasler–Melfi–Parton's odd PAN counts (OEIS A287728).

Counts odd primitive abundant numbers with Ω = K using the same tree as search.py: abundant leaves
with Ω = K (repeat children) are tested for primitivity directly, and each last-level prefix m
contributes #{primes p : L < p ≤ U} from lastprime.primitive_p_range.  Prime counts over all the
(L, U] windows are obtained in one sweep of a segmented sieve (memory ~ segment size).
"""
from __future__ import annotations

from typing import Callable, Dict, List, Tuple

import numpy as np

from arith import Factorization, big_omega, sigma, value
from lastprime import primitive_p_range
from tree import Node, walk


def prime_pi_many(xs: List[int], seg: int = 1 << 24) -> Dict[int, int]:
    """π(x) for every x in xs (one segmented-sieve sweep up to max(xs))."""
    targets = sorted(set(x for x in xs if x >= 2))
    out = {x: 0 for x in xs if x < 2}
    if not targets:
        return out
    top = targets[-1]
    r = int(top ** 0.5) + 1
    base = np.ones(r + 1, dtype=bool)
    base[:2] = False
    for i in range(2, int(r ** 0.5) + 1):
        if base[i]:
            base[i * i::i] = False
    small = np.nonzero(base)[0]
    count = 0
    ti = 0
    lo = 0
    while ti < len(targets):
        hi = min(lo + seg, top + 1)
        blk = np.ones(hi - lo, dtype=bool)
        if lo == 0:
            blk[:2] = False
        for p in small:
            p = int(p)
            if p * p >= hi:
                break
            start = max(p * p, (lo + p - 1) // p * p)
            blk[start - lo::p] = False
        primes = np.nonzero(blk)[0] + lo
        while ti < len(targets) and targets[ti] < hi:
            out[targets[ti]] = count + int(np.searchsorted(primes, targets[ti], side="right"))
            ti += 1
        count += len(primes)
        lo = hi
    return out


def is_primitive_nondeficient(f: Factorization) -> bool:
    """n abundant (strictly) and n/q deficient for every prime q | n."""
    n, s = value(f), sigma(f)
    if s <= 2 * n:
        return False
    for i, (q, e) in enumerate(f):
        g = f[:i] + (((q, e - 1),) if e > 1 else ()) + f[i + 1:]
        if sigma(g) >= 2 * value(g):
            return False
    return True


def count_odd_pan(K: int) -> int:
    """Number of odd PANs with Ω = K (odd perfect numbers cannot occur for Ω ≤ 8)."""
    direct = [0]
    windows: List[Tuple[int, int]] = []

    def on_abundant(node: Node) -> None:
        if big_omega(node.f) == K and is_primitive_nondeficient(node.f):
            direct[0] += 1

    def on_prefix(node: Node) -> None:
        L, U = primitive_p_range(node.f)
        if U > L:
            windows.append((L, U))

    walk(K, on_abundant, on_prefix)
    pi = prime_pi_many([x for w in windows for x in w])
    return direct[0] + sum(pi[U] - pi[L] for L, U in windows)


if __name__ == "__main__":
    import sys
    K = int(sys.argv[1])
    print(K, count_odd_pan(K))

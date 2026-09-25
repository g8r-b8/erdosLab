"""Integer arithmetic helpers for the #470 odd-weird search (pure Python ints)."""
from __future__ import annotations

from typing import Dict, List, Tuple

Factorization = Tuple[Tuple[int, int], ...]  # ((p1, e1), (p2, e2), ...) with p1 < p2 < ...

_SMALL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)


def is_probable_prime(n: int) -> bool:
    """Strong Miller–Rabin test with the first 13 prime bases.

    Deterministic for n < 3.317e24; above that it is a probable-prime test.  A False answer is
    always correct (an MR witness proves compositeness), which is all the proof direction needs.
    """
    if n < 2:
        return False
    for q in _SMALL_PRIMES:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _SMALL_PRIMES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def next_prime(p: int) -> int:
    """Smallest prime > p (probable prime above 3.3e24)."""
    if p < 2:
        return 2
    q = p + 1 if p % 2 == 0 else p + 2
    while not is_probable_prime(q):
        q += 2
    return q


def sigma(f: Factorization) -> int:
    """σ(n) from the factorization."""
    r = 1
    for p, e in f:
        r *= (p ** (e + 1) - 1) // (p - 1)
    return r


def value(f: Factorization) -> int:
    """n from its factorization."""
    r = 1
    for p, e in f:
        r *= p ** e
    return r


def divisors(f: Factorization) -> List[int]:
    """All divisors of n (including 1 and n), sorted ascending."""
    ds = [1]
    for p, e in f:
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    ds.sort()
    return ds


def factor_small(n: int) -> Factorization:
    """Trial-division factorization (tests only; n < 10^12)."""
    out = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            out.append((p, e))
        p += 1 if p == 2 else 2
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def mul_prime(f: Factorization, p: int) -> Factorization:
    """Factorization of n·p where p ≥ gpf(n) (append or bump the last exponent)."""
    if f and f[-1][0] == p:
        return f[:-1] + ((p, f[-1][1] + 1),)
    assert not f or p > f[-1][0], "mul_prime needs p >= gpf(n)"
    return f + ((p, 1),)


def big_omega(f: Factorization) -> int:
    """Ω(n) = number of prime factors with multiplicity."""
    return sum(e for _, e in f)


def as_dict(f: Factorization) -> Dict[int, int]:
    """dict view {p: e}."""
    return dict(f)

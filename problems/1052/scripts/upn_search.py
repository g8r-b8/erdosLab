#!/usr/bin/env python3
"""Independent cross-check of scripts/fixm.gp: all unitary perfect numbers N = 2^m * n (n odd) for a fixed m.

Written separately from the PARI/gp search: different code, same mathematics (see PROOF.md). Uses only the
ratio bound, the required-prime rule (R) and the 2-adic budget (B), not the refined free-component bound, so
it explores a larger tree. It is a cross-check, not the certificate; primality here is Miller–Rabin
(deterministic below 3.3e24, BPSW-style probable prime above) and is reported as such.

Usage: upn_search.py M_LO M_HI
"""
from __future__ import annotations

import sys
import time
from fractions import Fraction
from math import gcd, isqrt


def is_prime(n: int) -> bool:
    """Primality test.

    TODO: Miller–Rabin with the first 13 prime bases (deterministic for n < 3.3e24), plus a strong Lucas test
    above that bound.
    Acceptance: agrees with trial division for all n < 10^5.
    """
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    for p in small:
        if n % p == 0:
            return n == p
    d, s_ = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s_ += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s_ - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    if n < 3317044064679887385961981:
        return True
    return _strong_lucas(n)


def _strong_lucas(n: int) -> bool:
    """Strong Lucas probable-prime test with Selfridge parameters (n odd, not a square)."""
    r = isqrt(n)
    if r * r == n:
        return False
    D = 5
    while True:
        j = _jacobi(D, n)
        if j == -1:
            break
        if j == 0 and abs(D) != n:
            return False
        D = -D - 2 if D > 0 else -D + 2
    P, Q = 1, (1 - D) // 4
    d, s_ = n + 1, 0
    while d % 2 == 0:
        d //= 2
        s_ += 1
    U, V, Qk = 0, 2, 1  # U_0, V_0, Q^0
    inv2 = pow(2, -1, n)
    for bit in bin(d)[2:]:
        U, V = U * V % n, (V * V - 2 * Qk) % n
        Qk = Qk * Qk % n
        if bit == '1':
            U, V = (P * U + V) * inv2 % n, (D * U + P * V) * inv2 % n
            Qk = Qk * Q % n
    if U == 0 or V == 0:
        return True
    for _ in range(s_ - 1):
        V = (V * V - 2 * Qk) % n
        Qk = Qk * Qk % n
        if V == 0:
            return True
    return False


def _jacobi(a: int, n: int) -> int:
    a %= n
    t = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                t = -t
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            t = -t
        a %= n
    return t if n == 1 else 0


def factorize(n: int) -> dict[int, int]:
    """Prime factorisation {p: e}.

    TODO: trial division to 10^4, then Pollard–Brent rho with is_prime.
    Acceptance: product of p^e equals n; every p passes is_prime.
    Depends on: is_prime.
    """
    f: dict[int, int] = {}
    for p in range(2, 10**4):
        if p * p > n:
            break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        x = stack.pop()
        if is_prime(x):
            f[x] = f.get(x, 0) + 1
            continue
        d = _brent(x)
        stack += [d, x // d]
    return f


def _brent(n: int) -> int:
    """A nontrivial factor of composite n (Pollard–Brent)."""
    r0 = isqrt(n)
    if r0 * r0 == n:
        return r0
    for c in range(1, 10**6):
        y, m, g, r, q = 2, 128, 1, 1, 1
        x = ys = 2
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = gcd(abs(x - ys), n)
        if g != n:
            return g
    raise RuntimeError("rho failed")


def prime_power_base(q: int) -> int | None:
    """Return p if q = p^a (p an odd prime, a >= 1), else None.

    TODO: integer k-th roots for k up to log2 q, then is_prime.
    Depends on: is_prime.
    """
    if q < 3 or q % 2 == 0:
        return None
    for k in range(q.bit_length(), 0, -1):
        b = _iroot(q, k)
        if b ** k == q and is_prime(b):
            return b
    return None


def _iroot(x: int, k: int) -> int:
    """floor(x^(1/k))."""
    if k == 1:
        return x
    lo, hi = 1, 1 << (x.bit_length() // k + 1)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** k <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


def search_m(m: int) -> list[int]:
    """All N = 2^m * n (n odd) with sigma*(N) = 2N.

    TODO: for r = 1..m+1, DFS over odd components q_1 < ... < q_r with prod (1 + 1/q_i) = 2^(m+1)/(2^m+1),
    pruning by (R) required primes, (B) the budget sum v2(q_i + 1) = m + 1, the ratio window for the next
    component, and the divisor identity ((a-b)x - b)((a-b)y - b) = ab for the last two.
    Acceptance: m = 1, 2, 6, 18 return [6, 90], [60], [87360], [146361946186458562560000]; other m <= 10
    return [] (Subbarao–Warren 1966; Subbarao et al. 1972).
    Depends on: factorize, prime_power_base.
    """
    T0 = Fraction(2 ** (m + 1), 2 ** m + 1)
    sols: list[int] = []
    stats = [0]

    def odd_primes(x: int) -> set[int]:
        return {p for p in factorize(x) if p > 2}

    def v2(x: int) -> int:
        return (x & -x).bit_length() - 1

    def dfs(comps: list[int], prims: set[int], req: set[int], T: Fraction, used: int, r: int) -> None:
        stats[0] += 1
        if T <= 1 or len(req) > r or used + r > m + 1:
            return
        last = comps[-1] if comps else 1

        def close(new: list[int]) -> None:
            allc = comps + new
            ps = [prime_power_base(q) for q in allc]
            if None in ps or len(set(ps)) != len(ps):
                return
            need = set().union(*(odd_primes(q + 1) for q in allc), odd_primes(2 ** m + 1))
            if not need <= set(ps) or sum(v2(q + 1) for q in allc) != m + 1:
                return
            n = 2 ** m
            for q in allc:
                n *= q
            sols.append(n)

        if r == 1:
            if T.numerator - T.denominator == 1 and T.denominator > last:
                close([T.denominator])
            return
        if r == 2:
            a, b = T.numerator, T.denominator
            c = a - b
            fa = factorize(a * b)
            divs = [1]
            for p, e in fa.items():
                divs = [d * p ** i for d in divs for i in range(e + 1)]
            for d in divs:
                if (d + b) % c or (a * b // d + b) % c:
                    continue
                x, y = (d + b) // c, (a * b // d + b) // c
                if last < x < y:
                    close([x, y])
            return
        lo = max(last + 1, int(1 / (T - 1)) + 1)
        hi = int(r * T / (T - 1)) + 1
        for q in range(lo | 1, hi + 1, 2):
            if (1 + Fraction(1, q)) ** r <= T:
                break
            if used + v2(q + 1) + (r - 1) > m + 1:
                continue
            p = prime_power_base(q)
            if p is None or p in prims:
                continue
            nreq = (req | odd_primes(q + 1)) - prims - {p}
            dfs(comps + [q], prims | {p}, nreq, T / (1 + Fraction(1, q)), used + v2(q + 1), r - 1)

    for r in range(1, m + 2):
        dfs([], set(), odd_primes(2 ** m + 1), T0, 0, r)
    search_m.nodes = stats[0]
    return sorted(set(sols))


def main(argv: list[str]) -> None:
    """Run search_m for each m in [M_LO, M_HI] and print one line per m: m, solutions, node count."""
    lo, hi = int(argv[1]), int(argv[2])
    for m in range(lo, hi + 1):
        t = time.time()
        sols = search_m(m)
        print(f"m={m} sols={sols} nodes={search_m.nodes} s={time.time() - t:.1f}", flush=True)


if __name__ == "__main__":
    main(sys.argv)

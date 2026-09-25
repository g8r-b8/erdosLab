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
from fractions import Fraction


def is_prime(n: int) -> bool:
    """Primality test.

    TODO: Miller–Rabin with the first 13 prime bases (deterministic for n < 3.3e24), plus a strong Lucas test
    above that bound.
    Acceptance: agrees with trial division for all n < 10^5.
    """
    raise NotImplementedError("primality test")


def factorize(n: int) -> dict[int, int]:
    """Prime factorisation {p: e}.

    TODO: trial division to 10^4, then Pollard–Brent rho with is_prime.
    Acceptance: product of p^e equals n; every p passes is_prime.
    Depends on: is_prime.
    """
    raise NotImplementedError("factorisation")


def prime_power_base(q: int) -> int | None:
    """Return p if q = p^a (p an odd prime, a >= 1), else None.

    TODO: integer k-th roots for k up to log2 q, then is_prime.
    Depends on: is_prime.
    """
    raise NotImplementedError("prime-power test")


def search_m(m: int) -> list[int]:
    """All N = 2^m * n (n odd) with sigma*(N) = 2N.

    TODO: for r = 1..m+1, DFS over odd components q_1 < ... < q_r with prod (1 + 1/q_i) = 2^(m+1)/(2^m+1),
    pruning by (R) required primes, (B) the budget sum v2(q_i + 1) = m + 1, the ratio window for the next
    component, and the divisor identity ((a-b)x - b)((a-b)y - b) = ab for the last two.
    Acceptance: m = 1, 2, 6, 18 return [6, 90], [60], [87360], [146361946186458562560000]; other m <= 10
    return [] (Subbarao–Warren 1966; Subbarao et al. 1972).
    Depends on: factorize, prime_power_base.
    """
    raise NotImplementedError("fixed-m search")


def main(argv: list[str]) -> None:
    """Run search_m for each m in [M_LO, M_HI] and print one line per m: m, solutions, node count."""
    raise NotImplementedError("CLI")


if __name__ == "__main__":
    main(sys.argv)

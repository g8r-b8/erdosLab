"""Integer arithmetic helpers for the #470 odd-weird search (pure Python ints)."""
from __future__ import annotations

from typing import Dict, List, Tuple

Factorization = Tuple[Tuple[int, int], ...]  # ((p1, e1), (p2, e2), ...) with p1 < p2 < ...


def is_probable_prime(n: int) -> bool:
    """Strong Miller–Rabin test.

    TODO: implement.
    What's missing: trial division by small primes, then MR with the first 13 prime bases
        (deterministic for n < 3.317e24); above that it is a probable-prime test.
    Acceptance: agrees with a sieve for n < 10^6; a False answer is always correct
        (an MR witness proves compositeness), which is all the proof direction needs.
    Depends on: nothing.
    """
    raise NotImplementedError("MR test not written yet")


def next_prime(p: int) -> int:
    """Smallest prime > p (probable prime above 3.3e24).

    TODO: implement.  Acceptance: next_prime(2)=3, next_prime(40)=41.  Depends on: is_probable_prime.
    """
    raise NotImplementedError("next_prime not written yet")


def sigma(f: Factorization) -> int:
    """σ(n) from the factorization.

    TODO: implement.  Acceptance: sigma(((2,2),(3,1)))=28.  Depends on: nothing.
    """
    raise NotImplementedError("sigma not written yet")


def value(f: Factorization) -> int:
    """n from its factorization.

    TODO: implement.  Acceptance: value(((3,3),(5,1),(7,1)))=945.  Depends on: nothing.
    """
    raise NotImplementedError("value not written yet")


def divisors(f: Factorization) -> List[int]:
    """All divisors of n (including 1 and n), sorted ascending.

    TODO: implement.  Acceptance: divisors(((2,1),(5,1),(7,1))) == [1,2,5,7,10,14,35,70].
    Depends on: nothing.
    """
    raise NotImplementedError("divisors not written yet")


def factor_small(n: int) -> Factorization:
    """Trial-division factorization (tests only; n < 10^12).

    TODO: implement.  Acceptance: factor_small(945) == ((3,3),(5,1),(7,1)).  Depends on: nothing.
    """
    raise NotImplementedError("factor_small not written yet")


def mul_prime(f: Factorization, p: int) -> Factorization:
    """Factorization of n·p where p ≥ gpf(n) (append or bump the last exponent).

    TODO: implement.  Acceptance: mul_prime(((3,1),), 3) == ((3,2),); mul_prime(((3,1),), 5) == ((3,1),(5,1)).
    Depends on: nothing.
    """
    raise NotImplementedError("mul_prime not written yet")


def big_omega(f: Factorization) -> int:
    """Ω(n) = number of prime factors with multiplicity.

    TODO: implement.  Acceptance: big_omega(((3,3),(5,1),(7,1))) == 5.  Depends on: nothing.
    """
    raise NotImplementedError("big_omega not written yet")


def as_dict(f: Factorization) -> Dict[int, int]:
    """dict view {p: e}.  TODO: implement.  Depends on: nothing."""
    raise NotImplementedError("as_dict not written yet")

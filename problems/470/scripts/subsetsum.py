"""Subset sums of divisor sets, and the exact pseudoperfectness test."""
from __future__ import annotations

from typing import List, Optional

from arith import Factorization
from intervals import IntervalSet


class TooManyIntervals(Exception):
    """Raised when an interval-list DP exceeds its size cap (caller must fall back / flag)."""


def subset_sums(elems: List[int], cap: int = 200_000) -> IntervalSet:
    """SS(elems) = {sum of a sub-multiset... no: of a SUBSET of the distinct elems} as an IntervalSet.

    TODO: implement by DP in increasing order: S <- S ∪ (S + d).
    What's missing: the DP loop; raise TooManyIntervals if len(S) > cap.
    Acceptance: subset_sums([1,2,5,7,10,14,35]) does NOT contain 70 (70 is weird: A(70)=4 ∉
        SS of proper divisors [1,2,5,7,10,14,35]); subset_sums([1,3,5]) == {0,1,3,4,5,6,8,9}.
    Depends on: IntervalSet.union_shift.
    """
    raise NotImplementedError("subset_sums not written yet")


def is_pseudoperfect(f: Factorization, cap: int = 200_000) -> bool:
    """Exact test: n is a sum of distinct proper divisors ⇔ A(n) = σ(n) − 2n ∈ SS(proper divisors).

    TODO: implement.  Deficient n (A < 0) -> False.  Perfect (A = 0) -> True.
    Acceptance: 70 -> False, 836 -> False (weird); 12, 945 -> True.  Agrees with a brute-force
        bitset check on all abundant n < 10^5.
    Depends on: arith.divisors, arith.sigma, arith.value, subset_sums.
    """
    raise NotImplementedError("is_pseudoperfect not written yet")


def witness(f: Factorization) -> Optional[List[int]]:
    """A set of distinct proper divisors summing to n (for certificates), or None if weird/deficient.

    TODO: implement by backtracking over the SS DP (greedy-from-largest with membership checks
        against the interval sets of prefixes).
    Acceptance: sum(witness(945)) == 945 and each element is a proper divisor of 945.
    Depends on: subset_sums.
    """
    raise NotImplementedError("witness not written yet")

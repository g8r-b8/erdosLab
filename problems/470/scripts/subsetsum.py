"""Subset sums of divisor sets, and the exact pseudoperfectness test."""
from __future__ import annotations

from typing import List, Optional

from arith import Factorization, divisors, sigma, value
from intervals import IntervalSet


class TooManyIntervals(Exception):
    """Raised when an interval-list DP exceeds its size cap (caller must fall back / flag)."""


def subset_sums(elems: List[int], cap: int = 200_000) -> IntervalSet:
    """SS(elems) = {sums of subsets of the (distinct) elems} as an IntervalSet (DP S <- S ∪ (S+d))."""
    S = IntervalSet([(0, 0)])
    for d in sorted(elems):
        S = S.union_shift(d)
        if len(S) > cap:
            raise TooManyIntervals(f"{len(S)} intervals after element {d}")
    return S


def _prefix_sums_tables(elems: List[int], cap: int) -> List[IntervalSet]:
    """tables[i] = SS(elems[:i]) for the sorted elems (tables[0] = {0})."""
    tables = [IntervalSet([(0, 0)])]
    for d in elems:
        tables.append(tables[-1].union_shift(d))
        if len(tables[-1]) > cap:
            raise TooManyIntervals(f"{len(tables[-1])} intervals")
    return tables


def is_pseudoperfect(f: Factorization, cap: int = 200_000) -> bool:
    """Exact test: n is a sum of distinct proper divisors ⇔ A(n) = σ(n) − 2n ∈ SS(proper divisors)."""
    n, s = value(f), sigma(f)
    A = s - 2 * n
    if A < 0:
        return False
    if A == 0:
        return True
    # only divisors ≤ A can occur in a representation of A
    small = [d for d in divisors(f) if d <= A and d != n]
    return subset_sums(small, cap).contains(A)


def witness(f: Factorization, cap: int = 200_000) -> Optional[List[int]]:
    """A set of distinct proper divisors summing to n, or None if n is weird or deficient.

    Finds T ⊆ proper divisors with sum(T) = A(n) by backtracking through the prefix tables, and
    returns the complement (proper divisors minus T), whose sum is (σ(n) − n) − A(n) = n.
    """
    n, s = value(f), sigma(f)
    A = s - 2 * n
    if A < 0:
        return None
    proper = [d for d in divisors(f) if d != n]
    small = [d for d in proper if d <= A]
    tables = _prefix_sums_tables(small, cap)
    if not tables[-1].contains(A):
        return None
    T = []
    target = A
    for i in range(len(small), 0, -1):
        if tables[i - 1].contains(target):
            continue  # can do without small[i-1]
        target -= small[i - 1]
        T.append(small[i - 1])
    assert target == 0
    Tset = set(T)
    return [d for d in proper if d not in Tset]

"""Finite sets of non-negative integers stored as sorted, disjoint, non-adjacent closed intervals."""
from __future__ import annotations

from typing import Iterator, List, Tuple

Interval = Tuple[int, int]  # closed [lo, hi], lo <= hi


class IntervalSet:
    """Canonical union of closed integer intervals: sorted, disjoint, and gaps of size >= 1
    between consecutive intervals (i.e. hi_i + 1 < lo_{i+1})."""

    def __init__(self, ivs: List[Interval] | None = None) -> None:
        """Build from arbitrary (possibly overlapping/unsorted) intervals.

        TODO: implement via normalize().  Acceptance: IntervalSet([(3,5),(0,1),(2,2)]).ivs == [(0,5)].
        Depends on: normalize.
        """
        raise NotImplementedError("IntervalSet.__init__ not written yet")

    @staticmethod
    def normalize(ivs: List[Interval]) -> List[Interval]:
        """Sort and merge overlapping or adjacent intervals; drop empty ones (lo > hi).

        TODO: implement.  Acceptance: normalize([(5,7),(1,2),(3,4)]) == [(1,7)].
        Depends on: nothing.
        """
        raise NotImplementedError("normalize not written yet")

    def contains(self, x: int) -> bool:
        """Membership by bisection.  TODO: implement.  Depends on: nothing."""
        raise NotImplementedError("contains not written yet")

    def union_shift(self, d: int) -> "IntervalSet":
        """self ∪ (self + d) — one subset-sum DP step for a new element d.

        TODO: implement as a linear merge of two sorted lists.
        Acceptance: IntervalSet([(0,0)]).union_shift(3).ivs == [(0,0),(3,3)].
        Depends on: normalize.
        """
        raise NotImplementedError("union_shift not written yet")

    def subtract(self, other: "IntervalSet") -> "IntervalSet":
        """Set difference self \\ other.  TODO: implement (two-pointer sweep).  Depends on: nothing."""
        raise NotImplementedError("subtract not written yet")

    def intersect_range(self, lo: int, hi: int) -> "IntervalSet":
        """self ∩ [lo, hi].  TODO: implement.  Depends on: nothing."""
        raise NotImplementedError("intersect_range not written yet")

    def overlapping(self, lo: int, hi: int) -> Iterator[Interval]:
        """Yield the stored intervals meeting [lo, hi] (bisect to the first one).

        TODO: implement.  Depends on: nothing.
        """
        raise NotImplementedError("overlapping not written yet")

    def size(self) -> int:
        """Number of integers in the set.  TODO: implement.  Depends on: nothing."""
        raise NotImplementedError("size not written yet")

    def __iter__(self) -> Iterator[Interval]:
        """Iterate the stored intervals.  TODO: implement.  Depends on: nothing."""
        raise NotImplementedError("__iter__ not written yet")

    def __len__(self) -> int:
        """Number of stored intervals.  TODO: implement.  Depends on: nothing."""
        raise NotImplementedError("__len__ not written yet")

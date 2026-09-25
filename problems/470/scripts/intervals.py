"""Finite sets of non-negative integers stored as sorted, disjoint, non-adjacent closed intervals."""
from __future__ import annotations

from bisect import bisect_right
from typing import Iterator, List, Tuple

Interval = Tuple[int, int]  # closed [lo, hi], lo <= hi


class IntervalSet:
    """Canonical union of closed integer intervals: sorted, disjoint, and gaps of size >= 1
    between consecutive intervals (i.e. hi_i + 1 < lo_{i+1})."""

    __slots__ = ("ivs", "_los")

    def __init__(self, ivs: List[Interval] | None = None) -> None:
        self.ivs: List[Interval] = self.normalize(list(ivs or []))
        self._los: List[int] | None = None

    @classmethod
    def _canonical(cls, ivs: List[Interval]) -> "IntervalSet":
        """Wrap an already-canonical list without re-normalizing."""
        obj = cls.__new__(cls)
        obj.ivs = ivs
        obj._los = None
        return obj

    @staticmethod
    def normalize(ivs: List[Interval]) -> List[Interval]:
        """Sort and merge overlapping or adjacent intervals; drop empty ones (lo > hi)."""
        ivs = sorted(iv for iv in ivs if iv[0] <= iv[1])
        out: List[Interval] = []
        for lo, hi in ivs:
            if out and lo <= out[-1][1] + 1:
                if hi > out[-1][1]:
                    out[-1] = (out[-1][0], hi)
            else:
                out.append((lo, hi))
        return out

    def _lo_list(self) -> List[int]:
        if self._los is None:
            self._los = [lo for lo, _ in self.ivs]
        return self._los

    def contains(self, x: int) -> bool:
        """Membership by bisection."""
        i = bisect_right(self._lo_list(), x) - 1
        return i >= 0 and self.ivs[i][1] >= x

    def union_shift(self, d: int) -> "IntervalSet":
        """self ∪ (self + d) — one subset-sum DP step for a new element d ≥ 0."""
        a = self.ivs
        b = [(lo + d, hi + d) for lo, hi in a]
        out: List[Interval] = []
        i = j = 0
        na = nb = len(a)
        while i < na or j < nb:
            if j >= nb or (i < na and a[i][0] <= b[j][0]):
                lo, hi = a[i]
                i += 1
            else:
                lo, hi = b[j]
                j += 1
            if out and lo <= out[-1][1] + 1:
                if hi > out[-1][1]:
                    out[-1] = (out[-1][0], hi)
            else:
                out.append((lo, hi))
        return IntervalSet._canonical(out)

    def subtract(self, other: "IntervalSet") -> "IntervalSet":
        """Set difference self \\ other."""
        out: List[Interval] = []
        b = other.ivs
        j = 0
        for lo, hi in self.ivs:
            while j < len(b) and b[j][1] < lo:
                j += 1
            k = j
            cur = lo
            while k < len(b) and b[k][0] <= hi:
                if b[k][0] > cur:
                    out.append((cur, b[k][0] - 1))
                cur = max(cur, b[k][1] + 1)
                k += 1
            if cur <= hi:
                out.append((cur, hi))
        return IntervalSet._canonical(out)

    def intersect_range(self, lo: int, hi: int) -> "IntervalSet":
        """self ∩ [lo, hi]."""
        out = [(max(a, lo), min(b, hi)) for a, b in self.overlapping(lo, hi)]
        return IntervalSet._canonical([iv for iv in out if iv[0] <= iv[1]])

    def overlapping(self, lo: int, hi: int) -> Iterator[Interval]:
        """Yield the stored intervals meeting [lo, hi]."""
        i = max(bisect_right(self._lo_list(), lo) - 1, 0)
        ivs = self.ivs
        while i < len(ivs) and ivs[i][0] <= hi:
            if ivs[i][1] >= lo:
                yield ivs[i]
            i += 1

    def size(self) -> int:
        """Number of integers in the set."""
        return sum(hi - lo + 1 for lo, hi in self.ivs)

    def __iter__(self) -> Iterator[Interval]:
        return iter(self.ivs)

    def __len__(self) -> int:
        return len(self.ivs)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, IntervalSet) and self.ivs == other.ivs

    def __repr__(self) -> str:
        return f"IntervalSet({self.ivs})"

"""Cross-check the enumeration against Amato–Hasler–Melfi–Parton's odd PAN counts (OEIS A287728).

Counts odd primitive abundant numbers with Ω = K using the same tree: primitive abundant leaves at
depth < K are tested for primitivity directly, and each last-level prefix contributes
π(U) − π(L) primes from lastprime.primitive_p_range (plus its repeat child if primitive).
"""
from __future__ import annotations

from typing import List


def prime_pi_table(limit: int) -> "object":
    """Return a callable π(x) for x ≤ limit (numpy odd-only sieve + cumulative counts).

    TODO: implement; memory ≈ limit/2 bytes (limit 3e8 -> 150 MB; run under memcap).
    Acceptance: π(10^6) = 78498, π(2.72e8) computed.
    Depends on: numpy.
    """
    raise NotImplementedError("prime_pi_table not written yet")


def is_primitive_nondeficient(f: "object") -> bool:
    """n non-deficient and n/q deficient for every prime q | n.  TODO: implement.  Depends on: arith."""
    raise NotImplementedError("is_primitive_nondeficient not written yet")


def count_odd_pan(K: int) -> List[int]:
    """Number of odd PANs with Ω = K (primitive abundant; odd perfect numbers cannot occur here).

    TODO: implement.  Acceptance: K=5 -> 121, K=6 -> 15772, K=7 -> 102896101.
    Depends on: tree.walk, primitive_p_range, prime_pi_table.
    """
    raise NotImplementedError("count_odd_pan not written yet")


if __name__ == "__main__":
    import sys
    print(count_odd_pan(int(sys.argv[1])))

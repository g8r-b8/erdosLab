"""Driver: prove (computationally) that every odd non-deficient n with Ω(n) ≤ K is pseudoperfect.

Usage:  python3 search.py K [--log logs/omegaK.jsonl]
Output: summary counts; every flagged prefix / weird candidate is printed and logged.
By the reduction in README.md, "no weird found and nothing flagged" ⇒ no odd weird n has Ω(n) ≤ K.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from typing import Dict, List


@dataclass
class Summary:
    K: int
    abundant_leaves: Dict[int, int] = field(default_factory=dict)  # Ω -> count checked directly
    prefixes: int = 0
    new_prime_range_ints: int = 0      # total integers p covered uniformly
    residual_primes: int = 0           # primes checked one by one
    weird: List[str] = field(default_factory=list)
    flagged: List[str] = field(default_factory=list)


def run(K: int, log_path: str | None) -> Summary:
    """Walk the tree, check abundant leaves exactly, settle prefixes uniformly.

    TODO: implement with tree.walk, subsetsum.is_pseudoperfect, lastprime.settle_prefix.
    Acceptance: K=5,6 complete in seconds with no weird; K=7 completes with no weird/flag.
    Depends on: tree.walk, subsetsum.is_pseudoperfect, lastprime.settle_prefix.
    """
    raise NotImplementedError("run not written yet")


def main() -> None:
    """CLI.  TODO: implement argparse wrapper printing the Summary.  Depends on: run."""
    raise NotImplementedError("main not written yet")


if __name__ == "__main__":
    main()

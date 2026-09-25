"""Driver: prove (computationally) that every odd non-deficient n with Ω(n) ≤ K is pseudoperfect.

Usage:  python3 search.py K [--log logs/omegaK.jsonl]
Output: summary counts; every flagged prefix / weird candidate is printed and logged.
By the reduction in README.md, "no weird found and nothing flagged" ⇒ no odd weird n has Ω(n) ≤ K.
"""
from __future__ import annotations

import argparse
import json
import time
from dataclasses import dataclass, field
from typing import Dict, List

from arith import big_omega
from lastprime import settle_prefix
from subsetsum import is_pseudoperfect
from tree import Node, walk


@dataclass
class Summary:
    K: int
    abundant_leaves: Dict[int, int] = field(default_factory=dict)  # Ω -> count checked directly
    prefixes: int = 0
    new_prime_range_ints: int = 0      # total integers p covered uniformly
    residual_primes: int = 0           # primes checked one by one
    weird: List[str] = field(default_factory=list)
    flagged: List[str] = field(default_factory=list)
    t_max_used: int = 0
    max_residual_ints: int = 0
    max_p_hi: int = 0
    seconds: float = 0.0


def run(K: int, log_path: str | None) -> Summary:
    """Walk the tree, check abundant leaves exactly, settle prefixes uniformly."""
    S = Summary(K=K)
    log = open(log_path, "w") if log_path else None
    t0 = time.time()

    def on_abundant(node: Node) -> None:
        om = big_omega(node.f)
        S.abundant_leaves[om] = S.abundant_leaves.get(om, 0) + 1
        if not is_pseudoperfect(node.f):
            S.weird.append(str(node.f))
            print("WEIRD (direct):", node.f, flush=True)

    def on_prefix(node: Node) -> None:
        S.prefixes += 1
        rep = settle_prefix(node.f)
        S.new_prime_range_ints += max(0, rep.p_hi - rep.p_lo + 1)
        S.residual_primes += rep.residual_primes
        S.t_max_used = max(S.t_max_used, len(rep.t_used))
        S.max_residual_ints = max(S.max_residual_ints, rep.residual_ints)
        S.max_p_hi = max(S.max_p_hi, rep.p_hi)
        if rep.weird:
            S.weird.append(f"{node.f} * p for p in {rep.weird}")
            print("WEIRD (last prime):", node.f, rep.weird, flush=True)
        if rep.flagged:
            S.flagged.append(f"{node.f}: {rep.flagged}")
            print("FLAG:", node.f, rep.flagged, flush=True)
        if log and (rep.residual_primes or rep.flagged or rep.weird or len(rep.t_used) > 2):
            log.write(json.dumps({"m": node.f, "p_lo": rep.p_lo, "p_hi": rep.p_hi,
                                  "t_used": rep.t_used, "residual_ints": rep.residual_ints,
                                  "residual_primes": rep.residual_primes, "weird": rep.weird,
                                  "flagged": rep.flagged}) + "\n")
        if S.prefixes % 1000 == 0:
            print(f"  {S.prefixes} prefixes, {time.time() - t0:.0f}s", flush=True)

    walk(K, on_abundant, on_prefix)
    S.seconds = time.time() - t0
    if log:
        log.close()
    return S


def main() -> None:
    """CLI."""
    ap = argparse.ArgumentParser()
    ap.add_argument("K", type=int)
    ap.add_argument("--log", default=None)
    a = ap.parse_args()
    S = run(a.K, a.log)
    for k, v in S.__dict__.items():
        print(f"{k}: {v}")
    ok = not S.weird and not S.flagged
    print("RESULT:", f"every odd non-deficient n with Omega(n) <= {a.K} is pseudoperfect" if ok
          else "NOT SETTLED (see weird/flagged)")


if __name__ == "__main__":
    main()

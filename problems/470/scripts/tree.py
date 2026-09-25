"""Depth-bounded Fang-style DFS over n -> n·q (q ≥ gpf n) restricted to odd n with Ω(n) ≤ K.

Nodes are deficient odd n.  For each child c = n·q:
  * c non-deficient  -> an "abundant leaf": checked directly (its multiples need no search, since a
    multiple of a pseudoperfect number is pseudoperfect);
  * c deficient and Ω(c) = K−1 -> a "last-level prefix": all n·p with a NEW prime p > gpf are handled
    uniformly by lastprime.settle_prefix; the child c·gpf(c) (repeat) is an ordinary child.
Barrier (Fang Prop. 3.3, depth version): σ(n)/n · (1+1/q)^r < 2 with r = K − Ω(n) remaining
factors ⇒ no descendant through q or any larger q is non-deficient; stop the q loop.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterator, Tuple

from arith import Factorization


@dataclass
class Node:
    f: Factorization
    n: int
    s: int  # σ(n)


def children(node: Node, K: int) -> Iterator[Node]:
    """Children n·q for q = gpf(n), next primes..., until the depth barrier fails.

    TODO: implement: q starts at gpf(n) (repeat) and runs through primes; break when
        s·(q+1)^r < 2·n·q^r (r = K − Ω(n)).  σ update: new prime -> s·(q+1); repeat -> exact.
    Acceptance: for K=5 yields exactly the tree whose abundant leaves are the 121 odd Ω=5 PANs
        plus non-primitive ones (none for Ω=5).
    Depends on: arith.next_prime, arith.mul_prime.
    """
    raise NotImplementedError("children not written yet")


def walk(K: int,
         on_abundant: Callable[[Node], None],
         on_prefix: Callable[[Node], None]) -> None:
    """Run the DFS from the roots 3, 5, 7, ... (all odd primes p with (1+1/p)^K ≥ 2).

    TODO: implement recursively (depth ≤ K so recursion is shallow).
        - abundant child (s ≥ 2n)  -> on_abundant(child), do not descend;
        - deficient child with Ω = K−1 -> on_prefix(child) (new-prime extensions) AND descend into
          its repeat child only (q = gpf) — which, having Ω = K, is either abundant (-> on_abundant)
          or deficient (dropped);
        - deficient child with Ω < K−1 -> recurse.
    Acceptance: prefix count 23067 and abundant-leaf counts [121 @Ω5, 15810 @Ω6] for K = 7
        (numbers from the scratch measurement, 2026-09-25).
    Depends on: children.
    """
    raise NotImplementedError("walk not written yet")

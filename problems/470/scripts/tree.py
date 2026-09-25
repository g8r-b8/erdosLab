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

from arith import Factorization, big_omega, mul_prime, next_prime


@dataclass
class Node:
    f: Factorization
    n: int
    s: int  # σ(n)


def children(node: Node, K: int) -> Iterator[Node]:
    """Children n·q for q = gpf(n), next primes..., until the depth barrier fails.

    Barrier: s·(q+1)^r < 2·n·q^r (r = K − Ω(n)) ⇒ every n·q·(r−1 more factors ≥ q) is deficient,
    and the same holds for all larger q, so the loop stops.
    """
    f, n, s = node.f, node.n, node.s
    r = K - big_omega(f)
    if r <= 0:
        return
    q, e = f[-1]
    # repeat child
    if s * (q + 1) ** r >= 2 * n * q ** r:
        pe = (q ** (e + 1) - 1) // (q - 1)
        pe2 = pe * q + 1
        yield Node(mul_prime(f, q), n * q, s // pe * pe2)
    q = next_prime(q)
    while s * (q + 1) ** r >= 2 * n * q ** r:
        yield Node(f + ((q, 1),), n * q, s * (q + 1))
        q = next_prime(q)


def roots(K: int) -> Iterator[Node]:
    """Odd primes p with (1 + 1/p)^K ≥ 2 (otherwise nothing below p·... can be non-deficient)."""
    p = 3
    while (p + 1) ** K >= 2 * p ** K:
        yield Node(((p, 1),), p, p + 1)
        p = next_prime(p)


def walk(K: int,
         on_abundant: Callable[[Node], None],
         on_prefix: Callable[[Node], None]) -> None:
    """DFS over odd n with Ω(n) ≤ K (see module docstring).

    - non-deficient node -> on_abundant, no descent;
    - deficient node with Ω = K−1 -> on_prefix (new-prime extensions), plus its repeat child;
    - deficient node with Ω < K−1 -> recurse into children.
    """
    def visit(node: Node) -> None:
        if node.s >= 2 * node.n:
            on_abundant(node)
            return
        om = big_omega(node.f)
        if om >= K:
            return
        if om == K - 1:
            on_prefix(node)
            q, e = node.f[-1]
            pe = (q ** (e + 1) - 1) // (q - 1)
            rep = Node(mul_prime(node.f, q), node.n * q, node.s // pe * (pe * q + 1))
            if rep.s >= 2 * rep.n:
                on_abundant(rep)
            return
        for c in children(node, K):
            visit(c)

    for r in roots(K):
        visit(r)

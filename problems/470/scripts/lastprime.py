"""Uniform handling of the last (largest, new) prime.

Setting: m odd, deficient, Ω(m) = K−1, P = gpf(m), s = σ(m), δ = 2m − s ≥ 1.
For a prime p > P put n = m·p. Then
    σ(n) = s(p+1),   A(n) = σ(n) − 2n = s − δp,
    n abundant-or-perfect ⇔ δp ≤ s ⇔ p ≤ U := ⌊s/δ⌋,
    proper divisors of n = D(m) ∪ p·D'(m)   (D = divisors, D' = proper divisors),
and (LEMMA LP) n is pseudoperfect ⇔ ∃ t ∈ δ + J with t·p ∈ X, where X = SS(D(m)), J = SS(D'(m)).
Proof: a representation n = x + p·j (x ∈ X, j ∈ J) forces p | x, x = kp, k = m − j; since J is
symmetric about (s−m)/2 (complement in D'(m)), m − J = δ + J.  Conversely any such t gives one.
So for any finite T0 ⊆ δ + J, every p with some t ∈ T0, t·p ∈ X is settled at once, for the whole
p-range, without enumerating primes.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Tuple

from arith import Factorization
from intervals import IntervalSet


@dataclass
class PrefixReport:
    """Outcome for one prefix m."""
    m_factors: Factorization
    p_lo: int                      # smallest new prime considered (> P)
    p_hi: int                      # U = floor(s/δ)
    t_used: List[int] = field(default_factory=list)
    residual_ints: int = 0         # integers left after the uniform step
    residual_primes: int = 0       # of those, probable primes (each checked exactly)
    weird: List[int] = field(default_factory=list)   # p with m·p weird (should stay empty!)
    flagged: str = ""              # non-empty if the prefix could not be settled (needs attention)


def good_p_for_t(X: IntervalSet, t: int, lo: int, hi: int) -> IntervalSet:
    """{p ∈ [lo, hi] : t·p ∈ X} = ∪ over X-intervals [u, v] of [⌈u/t⌉, ⌊v/t⌋] ∩ [lo, hi].

    TODO: implement using X.overlapping(t*lo, t*hi).
    Acceptance: X = [0,10]∪[20,30], t = 2, [0, 20] -> [0,5]∪[10,15].
    Depends on: IntervalSet.overlapping.
    """
    raise NotImplementedError("good_p_for_t not written yet")


def t_candidates(delta: int, J: IntervalSet, limit: int) -> List[int]:
    """The `limit` smallest elements of δ + J (J = SS(D'(m)) contains 0, 1, ...).

    TODO: implement by walking J's intervals.  Acceptance: δ=5, J={0,1,3,4} -> [5,6,8,9].
    Depends on: IntervalSet iteration.
    """
    raise NotImplementedError("t_candidates not written yet")


def exact_single_p(X: IntervalSet, J: IntervalSet, delta: int, s: int, p: int) -> bool:
    """LEMMA LP for one p: is there t ∈ δ + J with t·p ∈ X?  (t ≤ s/p necessarily.)

    TODO: implement: for each X-interval [u, v] meeting [δp, s], the multiples of p in [u, v]
        form t ∈ [⌈u/p⌉, ⌊v/p⌋]; test whether (that range − δ) meets J.
    Acceptance: agrees with subsetsum.is_pseudoperfect(m·p) on random small cases.
    Depends on: IntervalSet.overlapping.
    """
    raise NotImplementedError("exact_single_p not written yet")


def settle_prefix(m: Factorization, max_t: int = 64, max_residual: int = 10**6) -> PrefixReport:
    """Settle all n = m·p with p prime, p > gpf(m), n non-deficient.

    TODO: implement.
    What's missing: compute s, δ, U, X, J; bad := [P+1, U]; for t in t_candidates: bad -= good_p_for_t;
        stop when bad is empty or small; then for every integer p in bad: skip composites (MR witness),
        otherwise run exact_single_p; record weird p (and double-check it with is_pseudoperfect).
        If bad still has > max_residual integers after max_t values of t, set flagged.
    Acceptance: for all Ω=5,6 PAN of the form m·p (p new largest prime) the result agrees with
        brute-force is_pseudoperfect; no weird found; residual counts are small.
    Depends on: subset_sums, good_p_for_t, t_candidates, exact_single_p, is_probable_prime.
    """
    raise NotImplementedError("settle_prefix not written yet")


def primitive_p_range(m: Factorization) -> Tuple[int, int]:
    """(L, U): m·p (p prime > gpf m) is a primitive non-deficient number ⇔ L < p ≤ U.

    TODO: implement: U = ⌊σ(m)/δ(m)⌋; for each prime q | m with m/q =: m_q, need m_q·p deficient,
        i.e. p·δ(m_q) > σ(m_q), so L = max(gpf(m), max_q ⌊σ(m_q)/δ(m_q)⌋).
    Acceptance: used by validate_counts to reproduce Amato et al.'s odd PAN counts
        (Ω=5: 121, Ω=6: 15772, Ω=7: 102896101).
    Depends on: arith.sigma.
    """
    raise NotImplementedError("primitive_p_range not written yet")

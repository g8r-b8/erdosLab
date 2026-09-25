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

from arith import Factorization, divisors, is_probable_prime, mul_prime, sigma, value
from intervals import IntervalSet
from subsetsum import is_pseudoperfect, subset_sums


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
    """{p ∈ [lo, hi] : t·p ∈ X} = ∪ over X-intervals [u, v] of [⌈u/t⌉, ⌊v/t⌋] ∩ [lo, hi]."""
    out = []
    for u, v in X.overlapping(t * lo, t * hi):
        a = max(-(-u // t), lo)
        b = min(v // t, hi)
        if a <= b:
            out.append((a, b))
    return IntervalSet(out)


def t_candidates(delta: int, J: IntervalSet, limit: int) -> List[int]:
    """The `limit` smallest elements of δ + J."""
    out: List[int] = []
    for lo, hi in J:
        for j in range(lo, hi + 1):
            if len(out) >= limit:
                return out
            out.append(delta + j)
    return out


def exact_single_p(X: IntervalSet, J: IntervalSet, delta: int, s: int, p: int) -> bool:
    """LEMMA LP for one p: is there t ∈ δ + J with t·p ∈ X?"""
    for u, v in X.overlapping(delta * p, s):
        tlo = max(-(-u // p), delta)
        thi = v // p
        if tlo <= thi and any(True for _ in J.overlapping(tlo - delta, thi - delta)):
            return True
    return False


def settle_prefix(m: Factorization, max_t: int = 64, max_residual: int = 10**6) -> PrefixReport:
    """Settle all n = m·p with p prime, p > gpf(m), n non-deficient (see module docstring)."""
    mv, s = value(m), sigma(m)
    delta = 2 * mv - s
    assert delta > 0, "prefix must be deficient"
    P = m[-1][0]
    U = s // delta
    rep = PrefixReport(m_factors=m, p_lo=P + 1, p_hi=U)
    if U <= P:
        return rep
    divs = divisors(m)
    X = subset_sums(divs)
    J = subset_sums(divs[:-1])
    bad = IntervalSet([(P + 1, U)])
    for t in t_candidates(delta, J, max_t):
        if not len(bad) or t * bad.ivs[0][0] > s:
            break
        good = []
        for a, b in bad:
            good.extend(good_p_for_t(X, t, a, b).ivs)
        rep.t_used.append(t)
        bad = bad.subtract(IntervalSet(good))
    rep.residual_ints = bad.size()
    if rep.residual_ints > max_residual:
        rep.flagged = f"{rep.residual_ints} residual integers after t={rep.t_used[-1:]}"
        return rep
    for a, b in bad:
        for p in range(a, b + 1):
            if not is_probable_prime(p):
                continue
            rep.residual_primes += 1
            if not exact_single_p(X, J, delta, s, p):
                # independent re-check on the full divisor set before recording
                if not is_pseudoperfect(mul_prime(m, p)):
                    rep.weird.append(p)
                else:
                    rep.flagged += f" LP/direct disagree at p={p};"
    return rep


def primitive_p_range(m: Factorization) -> Tuple[int, int]:
    """(L, U): m·p (p prime > gpf m) is primitive abundant ⇔ L < p ≤ U.

    U = largest p with δp < s (strictly abundant); L = max(gpf(m), max_q ⌊σ(m/q)/δ(m/q)⌋) where
    q runs over the primes dividing m (m/q·p must be deficient: p·δ(m/q) > σ(m/q)).
    """
    mv, s = value(m), sigma(m)
    delta = 2 * mv - s
    U = (s - 1) // delta
    L = m[-1][0]
    for i, (q, e) in enumerate(m):
        mq = m[:i] + (((q, e - 1),) if e > 1 else ()) + m[i + 1:]
        sq, vq = sigma(mq), value(mq)
        dq = 2 * vq - sq
        L = max(L, sq // dq)
    return L, U

#!/usr/bin/env python3
"""Route 4 numerics for lambda_1 = zeta^Omega (Erdos #436, Lambda(5,3)).

Computes, with logarithmic weights 1/n over n <= N (default N = 2*10^7):
  * Z   : density of zero runs  Omega(n) = Omega(n+1) = Omega(n+2) = 0 mod 5
  * Q   : density of constant triples Omega(n) = Omega(n+1) = Omega(n+2) mod 5
  * P1, P2, P3 : the three second-difference events of THEORY Prop 9.5
  * for d = 1..DMAX:
        F(d)   = P(A_d)          (unconditioned step-d constant triple density)
        Qc(d)  = P(A_d | d | n)  (conditioned; equals Q(N/d) exactly by
                                  multiplicativity, see route4_selfsimilar.md Lemma R4.1)
        Delta(d) = Qc(d) - F(d)  (decoupling defect)
  * the running mean  E_{d<=D} F(d)  (the Furstenberg-Roth average).

Usage: python3 route4_omega_stats.py [N] [DMAX]
Memory: about 8 bytes * N (int8 Omega array + float64 weights on the fly); N = 2e7 -> ~250 MB.
"""
import sys
import numpy as np


def omega_mod5(N: int) -> np.ndarray:
    """Omega(n) mod 5 for 0 <= n <= N+2*DMAX (index n); Omega(0) is junk."""
    M = N + 1
    om = np.zeros(M, dtype=np.int16)
    sieve = np.ones(M, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(M ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    primes = np.nonzero(sieve)[0]
    del sieve
    for p in primes:
        pk = int(p)
        while pk < M:
            om[pk::pk] += 1
            pk *= int(p)
    return (om % 5).astype(np.int8)


def main() -> None:
    N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000
    DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    L = N + 2 * DMAX + 3
    om = omega_mod5(L)
    n = np.arange(1, N + 1)
    w = 1.0 / n
    W = w.sum()
    a0 = om[1:N + 1]
    a1 = om[2:N + 2]
    a2 = om[3:N + 3]
    const = (a0 == a1) & (a1 == a2)
    zero = const & (a0 == 0)
    Q = (w * const).sum() / W
    Z = (w * zero).sum() / W
    P1 = (w * (((a0 + a2 - 2 * a1) % 5) == 0)).sum() / W
    P2 = (w * (((a0 + a1 - 2 * a2) % 5) == 0)).sum() / W
    P3 = (w * (((a1 + a2 - 2 * a0) % 5) == 0)).sum() / W
    print(f"N = {N:.3g}  (log-weighted)")
    print(f"zero-run density Z = {Z:.6f}   (1/125 = {1/125:.6f})")
    print(f"constant-triple  Q = {Q:.6f}   5Z = {5*Z:.6f}   (1/25 = {1/25:.6f})")
    print(f"P1 = {P1:.5f}  P2 = {P2:.5f}  P3 = {P3:.5f}  sum = {P1+P2+P3:.5f}")
    print(f"Prop 9.5 prediction (1/25)(sum - 2/5) = {(P1+P2+P3-0.4)/25:.6f}  vs Z = {Z:.6f}")
    print()
    print(" d    F(d)=P(A_d)   Qc(d)=P(A_d|d|n)   Delta(d)   running E_{d'<=d} F")
    run = 0.0
    for d in range(1, DMAX + 1):
        b0 = om[1:N + 1]
        b1 = om[1 + d:N + 1 + d]
        b2 = om[1 + 2 * d:N + 1 + 2 * d]
        c = (b0 == b1) & (b1 == b2)
        F = (w * c).sum() / W
        mask = (n % d == 0)
        Qc = (w[mask] * c[mask]).sum() / w[mask].sum()
        run += F
        print(f"{d:2d}   {F:.5f}        {Qc:.5f}          {Qc-F:+.5f}    {run/d:.5f}")


if __name__ == "__main__":
    main()

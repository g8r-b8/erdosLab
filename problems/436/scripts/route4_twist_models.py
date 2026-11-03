#!/usr/bin/env python3
"""Route 4: exact survival sets for 'Bohr + periodic additive twist' models (Erdos #436).

Model (route4_selfsimilar.md, Section 3): X_h = floor(5(y + h*theta)) + F_s(h) mod 5, with
(y, theta) Haar on T^2, s uniform on Z/N, all independent of the profinite coordinate r, and
Delta^2 F_s(h) = D(s + h) for a fixed D: Z/N -> Z/5.

Proved in the note (Lemma R4.6): the step-d process has a constant triple with positive probability
iff some D^(d)(h) := sum_{i,j<d} D(h+i+j) lies in {-1,0,1} mod 5.  Because s is independent of r,
conditioning on d | r changes nothing, so "survives d" means D^(d)(h) in {2,3} for all h.

For every D in {2,3}^N (N <= NMAX, primitive period N) we list the steps d <= DMAX it survives, and
report which survival patterns occur.  Output answers: does any periodic additive twist survive an
even step AND a step divisible by 5?  (Theorem R4.3 predicts: never both 2 and 5; Prop R4.4 predicts:
never a multiple of the period of F.)
"""
import itertools
import sys
from collections import defaultdict


def conv_step(D, d):
    N = len(D)
    w = [min(k + 1, 2 * d - 1 - k) for k in range(2 * d - 1)]
    return [sum(w[k] * D[(h + k) % N] for k in range(2 * d - 1)) % 5 for h in range(N)]


def primitive(D):
    N = len(D)
    return all(D != D[t:] + D[:t] for t in range(1, N) if N % t == 0)


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    patterns = defaultdict(list)
    both = []
    for N in range(1, NMAX + 1):
        seen = set()
        for D in itertools.product((2, 3), repeat=N):
            D = list(D)
            if not primitive(D):
                continue
            key = min(tuple(D[t:] + D[:t]) for t in range(N))
            if key in seen:
                continue
            seen.add(key)
            surv = tuple(d for d in range(1, DMAX + 1)
                         if all(v in (2, 3) for v in conv_step(D, d)))
            patterns[surv].append((N, key))
            if any(d % 2 == 0 for d in surv) and any(d % 5 == 0 for d in surv):
                both.append((N, key, surv))
    print(f"periodic D in {{2,3}}^N, N <= {NMAX}; steps d <= {DMAX}")
    for surv, lst in sorted(patterns.items(), key=lambda kv: (-len(kv[0]), kv[0])):
        ex = lst[0]
        desc = "all d" if len(surv) == DMAX else (
            "odd d" if surv == tuple(range(1, DMAX + 1, 2)) else
            "5∤d" if surv == tuple(d for d in range(1, DMAX + 1) if d % 5) else str(surv[:12]) + ("..." if len(surv) > 12 else ""))
        print(f"  #models={len(lst):5d}  survives: {desc}   e.g. N={ex[0]} D={ex[1]}")
    print("models surviving an even step and a multiple of 5:", len(both))
    for b in both[:10]:
        print("   ", b)


if __name__ == "__main__" and "--mc" not in sys.argv:
    main()


def parity_mc(samples: int = 2_000_000, seed: int = 1) -> None:
    """Monte Carlo check of the parity model X_h = floor(5(y+h*theta)) + (s+h mod 2), s in {0,1}.

    Prints constant-triple mass at steps d = 1..10, the maximal deviation of the two-point law
    (X_0, X_1), (X_0, X_2) from uniform, and the 3-point Fourier coefficients |E zeta^{aX0+bX1+cX2}|
    that exceed 0.01 (expected: only multiples of (1,3,1)).
    """
    import numpy as np
    rng = np.random.default_rng(seed)
    y = rng.random(samples)
    th = rng.random(samples)
    s = rng.integers(0, 2, samples)

    def X(h):
        return (np.floor(5 * ((y + h * th) % 1.0)).astype(np.int64) + (s + h) % 2) % 5

    print("parity model, constant-triple mass by step d:")
    for d in range(1, 11):
        a, b, c = X(0), X(d), X(2 * d)
        print(f"   d={d:2d}: {np.mean((a == b) & (b == c)):.5f}")
    x0, x1, x2 = X(0), X(1), X(2)
    dev = 0.0
    for u, v in ((x0, x1), (x0, x2)):
        cnt = np.bincount(5 * u + v, minlength=25) / samples
        dev = max(dev, float(np.max(np.abs(cnt - 1 / 25))))
    print(f"   max two-point deviation from 1/25: {dev:.2e}")
    z = np.exp(2j * np.pi / 5)
    big = []
    for a in range(5):
        for b in range(5):
            for c in range(5):
                if (a, b, c) == (0, 0, 0):
                    continue
                val = abs(np.mean(z ** ((a * x0 + b * x1 + c * x2) % 5)))
                if val > 0.01:
                    big.append(((a, b, c), round(val, 3)))
    print("   3-point Fourier coefficients > 0.01:", big)


if __name__ == "__main__" and "--mc" in sys.argv:
    parity_mc()

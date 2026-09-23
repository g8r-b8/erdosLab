"""Independent verifier for a candidate f (numpy; shares no code with lamenc.c / warmls.c).

  python checkf.py K L LIM MAP MODEL

MAP: lines "p base"; MODEL: solver "v" lines. f(p) = v iff literal base+v is true; primes not in MAP
get f(p) = 1 (the convention of `lamenc run`).  Recomputes f(n) for n <= LIM+L-1 by complete
additivity from a smallest-prime-factor sieve (lamenc uses largest prime factors) and prints the
first r <= LIM with f(r) = ... = f(r+L-1) = 0, or "NONE LIM".
"""
import sys

import numpy as np


def spf_sieve(n: int) -> np.ndarray:
    """TODO: smallest prime factor array spf[0..n] (spf[p] == p for primes).
    What's missing: body (numpy sieve, int32).
    Acceptance: spf[12] == 2, spf[35] == 5, spf[p] == p for primes.
    Depends on: nothing.
    """
    raise NotImplementedError("spf sieve")


def load_prime_values(k: int, mapfile: str, modelfile: str) -> dict:
    """TODO: return {p: f(p)} for primes in MAP from the true literals in MODEL.
    What's missing: body; must reject primes with 0 or >1 true value literals.
    Acceptance: on the 5.75M kissat model, every mapped prime has exactly one value.
    Depends on: nothing.
    """
    raise NotImplementedError("parse map + model")


def compute_f(k: int, n: int, spf: np.ndarray, pv: dict) -> np.ndarray:
    """TODO: f[0..n] (uint8) with f(1) = 0, f(p) = pv.get(p, 1), f(ab) = f(a) + f(b) mod k.
    What's missing: body (vectorised: repeatedly divide by spf).
    Acceptance: f[m*n] == (f[m] + f[n]) % k on random samples.
    Depends on: spf_sieve, load_prime_values.
    """
    raise NotImplementedError("additive extension")


def first_run(f: np.ndarray, l: int, lim: int):
    """TODO: least r in [1, lim] with f[r..r+l-1] all zero, else None.
    What's missing: body.
    Acceptance: agrees with `lamenc run` on the 5.75M model (5,750,107).
    Depends on: compute_f.
    """
    raise NotImplementedError("scan for zero runs")


def main() -> None:
    k, l, lim = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    n = lim + l - 1
    spf = spf_sieve(n)
    pv = load_prime_values(k, sys.argv[4], sys.argv[5])
    f = compute_f(k, n, spf, pv)
    r = first_run(f, l, lim)
    print(r if r is not None else f"NONE {lim}")


if __name__ == "__main__":
    main()

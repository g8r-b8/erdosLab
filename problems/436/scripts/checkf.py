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
    """smallest prime factor array spf[0..n] (spf[p] == p for primes).
    What's missing: body (numpy sieve, int32).
    Acceptance: spf[12] == 2, spf[35] == 5, spf[p] == p for primes.
    Depends on: nothing.
    """
    spf = np.zeros(n + 1, dtype=np.int32)
    for p in range(2, int(n ** 0.5) + 1):
        if spf[p] == 0:
            seg = spf[p * p::p]
            seg[seg == 0] = p
    idx = np.nonzero(spf == 0)[0]
    spf[idx] = idx  # primes (and 0, 1: unused)
    return spf


def load_prime_values(k: int, mapfile: str, modelfile: str) -> dict:
    """return {p: f(p)} for primes in MAP from the true literals in MODEL.
    What's missing: body; must reject primes with 0 or >1 true value literals.
    Acceptance: on the 5.75M kissat model, every mapped prime has exactly one value.
    Depends on: nothing.
    """
    base = {}
    with open(mapfile) as fh:
        for line in fh:
            p, b = line.split()
            base[int(p)] = int(b)
    true = set()
    with open(modelfile) as fh:
        for line in fh:
            if line.startswith("v"):
                true.update(int(t) for t in line.split()[1:] if int(t) > 0)
    pv = {}
    for p, b in base.items():
        vals = [v for v in range(k) if b + v in true]
        if len(vals) != 1:
            raise ValueError(f"prime {p}: true values {vals}")
        pv[p] = vals[0]
    return pv


def compute_f(k: int, n: int, spf: np.ndarray, pv: dict) -> np.ndarray:
    """f[0..n] (uint8) with f(1) = 0, f(p) = pv.get(p, 1), f(ab) = f(a) + f(b) mod k.
    What's missing: body (vectorised: repeatedly divide by spf).
    Acceptance: f[m*n] == (f[m] + f[n]) % k on random samples.
    Depends on: spf_sieve, load_prime_values.
    """
    val = np.ones(n + 1, dtype=np.uint8)
    for p, v in pv.items():
        if p <= n:
            val[p] = v
    f = np.zeros(n + 1, dtype=np.uint8)
    chunk = 1 << 22
    for lo in range(0, n + 1, chunk):
        rem = np.arange(lo, min(n + 1, lo + chunk), dtype=np.int32)
        acc = np.zeros(len(rem), dtype=np.uint8)
        rem[rem < 1] = 1  # n = 0 unused
        while True:
            live = rem > 1
            if not live.any():
                break
            q = spf[rem[live]]
            acc[live] = (acc[live] + val[q]) % k
            rem[live] //= q
        f[lo:lo + len(rem)] = acc
    return f


def first_run(f: np.ndarray, l: int, lim: int):
    """least r in [1, lim] with f[r..r+l-1] all zero, else None.
    What's missing: body.
    Acceptance: agrees with `lamenc run` on the 5.75M model (5,750,107).
    Depends on: compute_f.
    """
    z = f[1:lim + l] == 0  # z[i] <-> f(i+1) == 0
    run = z[:lim].copy()
    for j in range(1, l):
        run &= z[j:lim + j]
    hit = np.nonzero(run)[0]
    return int(hit[0]) + 1 if len(hit) else None


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

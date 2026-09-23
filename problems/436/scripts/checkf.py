"""Independent verifier for a candidate f (numpy; shares no code with lamenc.c / warmls.c).

  python checkf.py K L LIM MAP MODEL [sieve]

MAP: lines "p base"; MODEL: solver "v" lines. f(p) = v iff literal base+v is true; primes not in MAP
get f(p) = 1 (the convention of `lamenc run`).  Recomputes f(n) for n <= LIM+L-1 by complete
additivity and prints the first r <= LIM with f(r) = ... = f(r+L-1) = 0, or "NONE LIM".
Default: segmented trial division by prime powers <= sqrt(N) (memory O(segment + #listed primes));
"sieve": whole-range smallest-prime-factor sieve (lamenc uses largest prime factors).
"""
import math
import sys

import numpy as np


def spf_sieve(n: int) -> np.ndarray:
    """smallest prime factor array spf[0..n] as uint16 (n < 65536**2); spf[p] == 0 for primes.
    Acceptance: spf[12] == 2, spf[35] == 5, spf[p] == 0 for primes.
    Depends on: nothing.
    """
    assert n < 65536 ** 2
    spf = np.zeros(n + 1, dtype=np.uint16)
    for p in range(2, int(n ** 0.5) + 1):
        if spf[p] == 0:
            seg = spf[p * p::p]
            seg[seg == 0] = p
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
            r = rem[live]
            q = spf[r].astype(np.int32)
            q[q == 0] = r[q == 0]  # r is prime
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
    chunk = 1 << 24
    for lo in range(1, lim + 1, chunk):  # r in [lo, hi)
        hi = min(lim + 1, lo + chunk)
        z = f[lo:hi + l - 1] == 0
        run = z[:hi - lo].copy()
        for j in range(1, l):
            run &= z[j:hi - lo + j]
        hit = np.nonzero(run)[0]
        if len(hit):
            return lo + int(hit[0])
    return None


def first_run_segmented(k: int, l: int, lim: int, pv: dict, seg: int = 1 << 22):
    """Least r <= lim with f(r) = ... = f(r+l-1) = 0, computing f segment by segment (O(seg) memory).

    In each segment every n is divided by all prime powers p^j <= n with p <= isqrt(N), adding f(p)
    each time; what remains is 1 or a single prime q > isqrt(N) (two such factors would exceed N),
    whose value is looked up in the sorted table of primes listed in the map (default 1).
    Shares no code with the sieve path above and none with lamenc.c / warmls.c.
    """
    n = lim + l - 1
    B = math.isqrt(n)
    sp = spf_sieve(B)
    small = [p for p in range(2, B + 1) if sp[p] == 0]
    keys = np.array(sorted(pv), dtype=np.int64)
    kv = np.array([pv[p] for p in sorted(pv)], dtype=np.int64)
    tail = np.zeros(0, dtype=bool)
    for lo in range(1, n + 1, seg):
        hi = min(n + 1, lo + seg)
        rem = np.arange(lo, hi, dtype=np.int64)
        acc = np.zeros(hi - lo, dtype=np.int64)
        for p in small:
            fp = pv.get(p, 1)
            pk = p
            while pk < hi:
                st = (-lo) % pk
                rem[st::pk] //= p
                if fp:
                    acc[st::pk] += fp
                pk *= p
        big = rem > 1
        q = rem[big]
        idx = np.minimum(np.searchsorted(keys, q), len(keys) - 1)
        acc[big] += np.where(keys[idx] == q, kv[idx], 1)
        z = np.concatenate([tail, acc % k == 0])
        base = lo - len(tail)
        run = z[:len(z) - l + 1].copy()
        for j in range(1, l):
            run &= z[j:len(z) - l + 1 + j]
        hit = np.nonzero(run)[0]
        if len(hit) and base + int(hit[0]) <= lim:
            return base + int(hit[0])
        tail = z[len(z) - (l - 1):]
    return None


def main() -> None:
    k, l, lim = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    pv = load_prime_values(k, sys.argv[4], sys.argv[5])
    if len(sys.argv) > 6 and sys.argv[6] == "sieve":  # original whole-range path (~7 bytes per n)
        n = lim + l - 1
        r = first_run(compute_f(k, n, spf_sieve(n), pv), l, lim)
    else:
        r = first_run_segmented(k, l, lim, pv)
    print(r if r is not None else f"NONE {lim}")

if __name__ == "__main__":
    main()

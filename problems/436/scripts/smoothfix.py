"""Small-prime repair for warmls: make f avoid every zero triple among y-smooth runs.

  python smoothfix.py Y RUNS MAP MODEL OUTMAP OUTMODEL [SEED] [MAXSTEPS]

RUNS: output of `smoothruns Y X 3` (every r <= X with r, r+1, r+2 all Y-smooth).
Loads f(p) from MAP/MODEL (primes not listed = 1), runs a min-conflicts local search over the
values f(p), p <= Y, against the smooth triples only (the F_Y(X) instance of README.md). Moves are
scored as (change in #violated triples, cost) with cost = sum over changed primes of 1/p relative
to the start, so fixes prefer few changes on the largest primes, i.e. the least collateral
damage in the full instance. Writes the full prime assignment (p <= Y replaced) as a synthetic
map/model, in the same format as warmls output.

Why: every stuck window of warmls at R >= 1.5e8 is a run of 3 consecutive ~1000-smooth numbers.
Fixing it needs a prime <= 1000, which has ~N/p multiples, so the full-instance local search
cannot afford that move. Solving the smooth level first removes these windows up to X;
warmls with PMIN > Y then repairs the collateral damage with large primes.
"""
import sys

import numpy as np

import checkf


def primes_upto(y: int) -> list:
    """All primes <= y."""
    return [p for p in range(2, y + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def exponent_matrix(runs: np.ndarray, ps: list) -> np.ndarray:
    """E[j, t, i] = v_{ps[i]}(runs[t] + j) mod 5 for j = 0..2 (int8). Asserts full Y-smoothness."""
    E = np.zeros((3, len(runs), len(ps)), dtype=np.int8)
    for j in range(3):
        rem = runs + j
        for i, p in enumerate(ps):
            e = np.zeros(len(runs), dtype=np.int64)
            while True:
                m = rem % p == 0
                if not m.any():
                    break
                e += m
                rem = np.where(m, rem // p, rem)
            E[j, :, i] = e % 5
        assert (rem == 1).all(), "runs file contains a non-smooth number"
    return E


def fvals(E: np.ndarray, v: np.ndarray) -> np.ndarray:
    """F[j, t] = f(runs[t] + j) mod 5 (loop over primes to avoid an int64 copy of E)."""
    F = np.zeros(E.shape[:2], dtype=np.int64)
    for i in range(E.shape[2]):
        if v[i]:
            F += E[:, :, i].astype(np.int64) * int(v[i])
    return F % 5


def search(E: np.ndarray, v0: np.ndarray, ps: list, seed: int, maxsteps: int) -> np.ndarray:
    """Min-conflicts with breakout weights. Returns v with no zero triple, or raises."""
    rng = np.random.default_rng(seed)
    v = v0.copy()
    F = fvals(E, v)  # f values of the 3 members
    w = np.ones(E.shape[1])
    touch = [np.nonzero(E[:, :, i].any(axis=0))[0] for i in range(len(ps))]
    inv_p = np.array([1.0 / p for p in ps])

    def bad_mask(Fsub):
        return (Fsub == 0).all(axis=0)

    for step in range(maxsteps):
        bad = np.nonzero(bad_mask(F))[0]
        if len(bad) == 0:
            return v
        t = rng.choice(bad)
        cands = [i for i in range(len(ps)) if E[:, t, i].any()]
        best = None
        for i in cands:
            idx = touch[i]
            Fi = F[:, idx]
            b0 = bad_mask(Fi)
            for d in range(1, 5):
                Fn = (Fi + E[:, idx, i].astype(np.int64) * d) % 5
                b1 = bad_mask(Fn)
                wg = float((w[idx] * (b1.astype(int) - b0.astype(int))).sum())
                changed = (v[i] + d) % 5 != v0[i]
                cost = (inv_p[i] if changed else 0.0) - (inv_p[i] if v[i] != v0[i] else 0.0)
                key = (wg, cost, rng.random())
                if best is None or key < best[0]:
                    best = (key, i, d)
        (wg, cost, _), i, d = best
        if wg >= 0:
            w[t] += 1
            continue
        idx = touch[i]
        F[:, idx] = (F[:, idx] + E[:, idx, i].astype(np.int64) * d) % 5
        v[i] = (v[i] + d) % 5
        if step % 50 == 0:
            print(f"step {step} bad {int(bad_mask(F).sum())} changed "
                  f"{[ps[k] for k in np.nonzero(v != v0)[0]]}", file=sys.stderr)
    raise RuntimeError("no fix found")


def main() -> None:
    y = int(sys.argv[1])
    runs = np.loadtxt(sys.argv[2], dtype=np.int64).reshape(-1)
    pv = checkf.load_prime_values(5, sys.argv[3], sys.argv[4])
    seed = int(sys.argv[7]) if len(sys.argv) > 7 else 1
    maxsteps = int(sys.argv[8]) if len(sys.argv) > 8 else 100000
    ps = primes_upto(y)
    v0 = np.array([pv.get(p, 1) for p in ps], dtype=np.int64)
    E = exponent_matrix(runs, ps)
    F0 = fvals(E, v0)
    nb0 = int((F0 == 0).all(axis=0).sum())
    print(f"{len(runs)} smooth runs, {len(ps)} primes, violated at start: {nb0}", file=sys.stderr)
    v = search(E, v0, ps, seed, maxsteps)
    ch = [(ps[k], int(v0[k]), int(v[k])) for k in np.nonzero(v != v0)[0]]
    print(f"fixed: changed primes (p, old, new): {ch}", file=sys.stderr)
    for k, p in enumerate(ps):
        pv[p] = int(v[k])
    with open(sys.argv[5], "w") as mp, open(sys.argv[6], "w") as md:
        i = 0
        for p in sorted(pv):
            if pv[p] == 1:
                continue
            b = 5 * i + 1
            i += 1
            mp.write(f"{p} {b}\n")
            md.write(f"v {b + pv[p]}\n")
        md.write("v 0\n")


if __name__ == "__main__":
    main()

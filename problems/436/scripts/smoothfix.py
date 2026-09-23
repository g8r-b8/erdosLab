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


def factor_sparse(runs: np.ndarray, ps: list):
    """Per prime index i: (t, j, e) arrays with e = v_p(runs[t] + j) mod 5 != 0. Asserts smoothness."""
    ts = [[] for _ in ps]; js = [[] for _ in ps]; es = [[] for _ in ps]
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
            nz = np.nonzero(e % 5)[0]
            ts[i].append(nz); js[i].append(np.full(len(nz), j, dtype=np.int64)); es[i].append(e[nz] % 5)
        assert (rem == 1).all(), "runs file contains a non-smooth number"
    out = []
    for i in range(len(ps)):
        t = np.concatenate(ts[i]); j = np.concatenate(js[i]); e = np.concatenate(es[i])
        U = np.unique(t)
        out.append((U, np.searchsorted(U, t), j, e))
    return out


def fvals(fac, v: np.ndarray, M: int) -> np.ndarray:
    """F[j, t] = f(runs[t] + j) mod 5."""
    F = np.zeros((3, M), dtype=np.int64)
    for i, (U, pos, j, e) in enumerate(fac):
        if v[i]:
            np.add.at(F, (j, U[pos]), e * int(v[i]))
    return F % 5


def search(fac, v0: np.ndarray, ps: list, M: int, seed: int, maxsteps: int) -> np.ndarray:
    """Min-conflicts with breakout weights; tie-break toward changing large primes. Returns v."""
    rng = np.random.default_rng(seed)
    v = v0.copy()
    F = fvals(fac, v, M)
    w = np.ones(M)
    inv_p = np.array([1.0 / p for p in ps])
    # prime indices touching each run: build from fac
    touching = [[] for _ in range(M)]
    for i, (U, pos, j, e) in enumerate(fac):
        for t in U[np.unique(pos)]:
            touching[t].append(i)

    def delta(i, d):
        U, pos, j, e = fac[i]
        Fs = F[:, U].copy()
        b0 = (Fs == 0).all(axis=0)
        np.add.at(Fs, (j, pos), e * d)
        Fs %= 5
        b1 = (Fs == 0).all(axis=0)
        return U, Fs, b1.astype(int) - b0.astype(int)

    for step in range(maxsteps):
        bad = np.nonzero((F == 0).all(axis=0))[0]
        if len(bad) == 0:
            return v
        if step % 20 == 0:
            print(f"step {step} bad {len(bad)} changed {int((v != v0).sum())}", file=sys.stderr)
        t = int(rng.choice(bad))
        best = None
        for i in touching[t]:
            for d in range(1, 5):
                U, Fs, dg = delta(i, d)
                wg = float((w[U] * dg).sum())
                changed = (v[i] + d) % 5 != v0[i]
                cost = (inv_p[i] if changed else 0.0) - (inv_p[i] if v[i] != v0[i] else 0.0)
                key = (wg, cost, rng.random())
                if best is None or key < best[0]:
                    best = (key, i, d, U, Fs)
        (wg, cost, _), i, d, U, Fs = best
        if wg >= 0:
            w[t] += 1
            continue
        F[:, U] = Fs
        v[i] = (v[i] + d) % 5
    raise RuntimeError("no fix found")


def main() -> None:
    y = int(sys.argv[1])
    runs = np.loadtxt(sys.argv[2], dtype=np.int64).reshape(-1)
    pv = checkf.load_prime_values(5, sys.argv[3], sys.argv[4])
    seed = int(sys.argv[7]) if len(sys.argv) > 7 else 1
    maxsteps = int(sys.argv[8]) if len(sys.argv) > 8 else 100000
    ps = primes_upto(y)
    v0 = np.array([pv.get(p, 1) for p in ps], dtype=np.int64)
    fac = factor_sparse(runs, ps)
    F0 = fvals(fac, v0, len(runs))
    nb0 = int((F0 == 0).all(axis=0).sum())
    print(f"{len(runs)} smooth runs, {len(ps)} primes, violated at start: {nb0}", file=sys.stderr)
    v = search(fac, v0, ps, len(runs), seed, maxsteps)
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

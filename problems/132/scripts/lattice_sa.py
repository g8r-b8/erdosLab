"""Simulated annealing over lattice subsets for Erdos #132 (adversarial side).

Objective (Erdos): maximise M(X) = min over non-diameter distances d of mu(X,d).
A counterexample to the conjecture needs M(X) >= n+1.
Exact arithmetic: triangular lattice Z[w] with Q(a,b)=a^2+ab+b^2, square lattice Z[i] with a^2+b^2.

Also objective '16': min(mu(Delta_2), mu(delta)) (Problem 1.6), for comparison.
"""
import sys, math, random
import numpy as np


def pool(kind, R):
    pts = []
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            if kind == 'tri':
                # hexagonal patch of radius R
                if max(abs(a), abs(b), abs(a + b)) <= R:
                    pts.append((a, b))
            else:
                if a * a + b * b <= R * R:
                    pts.append((a, b))
    return pts


def qform(kind, da, db):
    return da * da + da * db + db * db if kind == 'tri' else da * da + db * db


def dmat(kind, pts):
    P = np.array(pts)
    da = P[:, None, 0] - P[None, :, 0]
    db = P[:, None, 1] - P[None, :, 1]
    return (da * da + da * db + db * db) if kind == 'tri' else (da * da + db * db)


def spectrum(D, S):
    sub = D[np.ix_(S, S)]
    iu = np.triu_indices(len(S), 1)
    vals, cnts = np.unique(sub[iu], return_counts=True)
    return dict(zip(vals.tolist(), cnts.tolist()))


def score_erdos(counts, n):
    nz = np.nonzero(counts)[0]
    nz = nz[nz > 0]
    diam = nz[-1]
    nd = nz[:-1]
    if len(nd) == 0:
        return -1e9, 0
    c = counts[nd]
    M = int(c.min())
    # energy: total deficit below n+1 (squared) - smooth surrogate
    deficit = np.maximum(0, n + 1 - c)
    E = float((deficit ** 2).sum())
    return -E, M


def score_16(counts, n):
    nz = np.nonzero(counts)[0]
    nz = nz[nz > 0]
    if len(nz) < 2:
        return -1e9, 0
    d2 = counts[nz[-2]]
    dl = counts[nz[0]]
    M = int(min(d2, dl))
    return M + 0.001 * (d2 + dl), M


def anneal(kind, R, n, obj='erdos', iters=200000, T0=3.0, seed=0):
    rng = random.Random(seed)
    pts = pool(kind, R)
    N = len(pts)
    D = dmat(kind, pts)
    K = int(D.max()) + 1
    S = rng.sample(range(N), n)
    inS = np.zeros(N, bool); inS[S] = True
    counts = np.zeros(K, np.int64)
    for i in range(n):
        for j in range(i + 1, n):
            counts[D[S[i], S[j]]] += 1
    sf = {"erdos": score_erdos, "16": score_16, "F": score_F, "R": score_R}[obj]
    cur, M = sf(counts, n)
    best = (M, list(S), cur)
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-3
        k = rng.randrange(n)
        out = S[k]
        # prefer lattice neighbours of existing points (local moves) half the time
        inn = rng.randrange(N)
        if inS[inn]:
            continue
        Sarr = np.array(S)
        np.subtract.at(counts, D[out, Sarr], 1)
        counts[0] += 1  # D[out,out]=0 was subtracted
        S[k] = inn
        Sarr[k] = inn
        np.add.at(counts, D[inn, Sarr], 1)
        counts[0] -= 1
        new, M2 = sf(counts, n)
        if new >= cur or rng.random() < math.exp((new - cur) / T):
            cur = new; inS[out] = False; inS[inn] = True
            if M2 > best[0] or (M2 == best[0] and new > best[2]):
                best = (M2, list(S), new)
        else:
            np.subtract.at(counts, D[inn, Sarr], 1)
            counts[0] += 1
            S[k] = out; Sarr[k] = out
            np.add.at(counts, D[out, Sarr], 1)
            counts[0] -= 1
    M, S, _ = best
    return M, [pts[i] for i in S], spectrum(D, S)


def score_F(counts, n):
    """3*(mu(delta) + (4/3) mu(Delta_2)) - 9n ; conjecture: <= O(sqrt n)."""
    nz = np.nonzero(counts)[0]
    nz = nz[nz > 0]
    if len(nz) < 3:
        return -1e9, -10**9
    F = 3 * int(counts[nz[0]]) + 4 * int(counts[nz[-2]]) - 9 * n
    return F, F


def score_R(counts, n):
    """R = number of distances with 1 <= mu <= n (conjecture: R >= 2, R -> infinity)."""
    nz = np.nonzero(counts)[0]
    nz = nz[nz > 0]
    c = counts[nz]
    rare = c <= n
    R = int(rare.sum())
    deficit = float(np.maximum(0, n + 1 - c[rare]).sum())
    return -(R * 2 * n + deficit), -R


if __name__ == '__main__':
    kind = sys.argv[1]; obj = sys.argv[2]
    ns = [int(x) for x in sys.argv[3].split(',')]
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 100000
    restarts = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    for n in ns:
        R = max(2, int(math.ceil(math.sqrt(n) * 0.9)))
        bestM, bestX, bestSp = -10**9, None, None
        for r in range(restarts):
            M, X, sp = anneal(kind, R, n, obj, iters, T0=(3.0*n if obj in ("erdos","R") else 3.0), seed=r * 1000 + n)
            if M > bestM:
                bestM, bestX, bestSp = M, X, sp
        print(f"{kind} {obj} n={n} R={R} best M={bestM} ratio={bestM/n:.3f}", flush=True)
        print("  pts", bestX)
        print("  spec", sorted(bestSp.items()))

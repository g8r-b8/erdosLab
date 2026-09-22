"""SA over subsets of cyclotomic pools Z[zeta_N] (small-coefficient points).

Pool: 0, zeta^a, zeta^a+zeta^b (a<=b), optionally zeta^a+zeta^b+zeta^c.
Distances are algebraic; classes formed by rounding |z-w|^2 to 1e-9 (collisions of
distinct algebraic numbers of this height at 1e-9 are implausible; spot-check with
sympy for any claimed record).
Objective 'erdos': maximise M = min non-diameter multiplicity.
"""
import sys, math, random, cmath
import numpy as np
from lattice_sa import score_erdos, score_16, score_F, score_R


def make_pool(N, depth=2, radius=None):
    z = [cmath.exp(2j * math.pi * a / N) for a in range(N)]
    pts = {0j}
    for a in range(N):
        pts.add(z[a])
    if depth >= 2:
        for a in range(N):
            for b in range(a, N):
                pts.add(z[a] + z[b])
    if depth >= 3:
        for a in range(N):
            for b in range(a, N):
                for c in range(b, N):
                    pts.add(z[a] + z[b] + z[c])
    # dedupe by rounding
    uniq = {}
    for p in pts:
        key = (round(p.real, 9), round(p.imag, 9))
        uniq[key] = p
    P = list(uniq.values())
    if radius is not None:
        P = [p for p in P if abs(p) <= radius + 1e-9]
    return P


def class_matrix(P):
    P = np.array(P)
    d2 = np.abs(P[:, None] - P[None, :]) ** 2
    r = np.round(d2, 8)
    vals, inv = np.unique(r, return_inverse=True)
    return inv.reshape(d2.shape), vals


def anneal(C, n, obj, iters, T0, seed):
    rng = random.Random(seed)
    N = C.shape[0]
    K = int(C.max()) + 1
    S = rng.sample(range(N), n)
    inS = np.zeros(N, bool); inS[S] = True
    counts = np.zeros(K, np.int64)
    for i in range(n):
        for j in range(i + 1, n):
            counts[C[S[i], S[j]]] += 1
    sf = {"erdos": score_erdos, "16": score_16, "F": score_F, "R": score_R}[obj]
    cur, M = sf(counts, n)
    best = (M, list(S), cur)
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-3
        k = rng.randrange(n); out = S[k]; inn = rng.randrange(N)
        if inS[inn]:
            continue
        Sarr = np.array(S)
        np.subtract.at(counts, C[out, Sarr], 1); counts[0] += 1
        S[k] = inn; Sarr[k] = inn
        np.add.at(counts, C[inn, Sarr], 1); counts[0] -= 1
        new, M2 = sf(counts, n)
        if new >= cur or rng.random() < math.exp((new - cur) / T):
            cur = new; inS[out] = False; inS[inn] = True
            if M2 > best[0] or (M2 == best[0] and new > best[2]):
                best = (M2, list(S), new)
        else:
            np.subtract.at(counts, C[inn, Sarr], 1); counts[0] += 1
            S[k] = out; Sarr[k] = out
            np.add.at(counts, C[out, Sarr], 1); counts[0] -= 1
    return best


if __name__ == '__main__':
    N = int(sys.argv[1]); obj = sys.argv[2]
    ns = [int(x) for x in sys.argv[3].split(',')]
    iters = int(sys.argv[4]); restarts = int(sys.argv[5])
    depth = int(sys.argv[6]) if len(sys.argv) > 6 else 2
    radius = float(sys.argv[7]) if len(sys.argv) > 7 else None
    P = make_pool(N, depth, radius)
    C, vals = class_matrix(P)
    print(f"pool N={N} size={len(P)} classes={len(vals)}", flush=True)
    for n in ns:
        if n > len(P):
            continue
        bestb = None
        for r in range(restarts):
            b = anneal(C, n, obj, iters, 3.0 * n if obj in ('erdos','R') else 3.0, r * 7919 + n)
            if bestb is None or b[0] > bestb[0]:
                bestb = b
        M, S, _ = bestb
        sub = C[np.ix_(S, S)][np.triu_indices(n, 1)]
        cl, cn = np.unique(sub, return_counts=True)
        spec = [(round(float(vals[c]), 5), int(k)) for c, k in zip(cl, cn)]
        print(f"N={N} {obj} n={n} M={M} ratio={M/n:.3f} spec={spec}", flush=True)
        print("   pts=", [(round(P[i].real, 5), round(P[i].imag, 5)) for i in S], flush=True)

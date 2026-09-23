"""Re-check the sharpness example for Corollary A1 (regular even m-gon with
'servers' on alternate edges) and the N2 example, in float64 and with the
gap (Delta2, Delta) margin printed, and run them through theorem checks.
Independent of checkA.py (own layer computation with a tolerance-aware hull).
"""
import math, itertools
import numpy as np
from scipy.spatial import ConvexHull


def dists(P):
    return np.sqrt(((P[:, None] - P[None]) ** 2).sum(-1))


def layers(P):
    idx = list(range(len(P)))
    out = []
    while len(idx) >= 3:
        h = ConvexHull(P[idx]).vertices
        L = [idx[i] for i in h]
        out.append(set(L))
        idx = [i for i in idx if i not in L]
    if idx:
        out.append(set(idx))
    return out


def report(P, name, tol=1e-9):
    n = len(P)
    D = dists(P)
    iu = np.triu_indices(n, 1)
    v = np.sort(D[iu])[::-1]
    Dl = v[0]
    k = int(np.sum(abs(v - Dl) < tol))
    D2 = v[k]
    k2 = int(np.sum(abs(v - D2) < tol))
    D3 = v[k + k2]
    A = (abs(D - D2) < tol) & ~np.eye(n, dtype=bool)
    mu2 = int(A.sum() // 2)
    Ls = layers(P)
    L1, L2 = Ls[0], (Ls[1] if len(Ls) > 1 else set())
    h = A.sum(1)
    # 2-core
    core = set(L1 | L2)
    ch = True
    while ch:
        ch = False
        for x in list(core):
            if sum(A[x, u] for u in core) < 2:
                core.remove(x); ch = True
    dc = {x: int(sum(A[x, u] for u in core)) for x in core}
    thA = len(L1) + len(L2) + 0.5 * sum(dc[x] - 2 for x in core if x in L1)
    A1 = 1.5 * len(L1) + len(L2)
    cdl = min(1.5 * (len(L1) + len(L2)), 4 / 3 * len(L1) + 2 * len(L2), 2 * len(L1) + len(L2))
    L2deg = sorted(dc[x] for x in core if x in L2)
    print(f"{name}: n={n} Delta={Dl:.6f} D2={D2:.6f} next={D3:.6f} (gap {D2-D3:.2e}) mu(Delta)={k} mu2={mu2} "
          f"|L1|={len(L1)} |L2|={len(L2)} max h(L1)={max(h[x] for x in L1)} H3={all(h[x]<=3 for x in L1)} "
          f"L2' core degs={set(L2deg)} ThmA={thA} A1={A1} CDL={cdl:.2f}")
    # concyclic quadruples count (just existence)
    return mu2, thA, A1


def sharp(m):
    V = np.array([[math.cos(2 * math.pi * i / m), math.sin(2 * math.pi * i / m)] for i in range(m)])
    h = m // 2
    D2 = np.linalg.norm(V[0] - V[h - 1])
    S = []
    for i in range(0, m, 2):
        a, b = V[i], V[(i + 1) % m]
        mid = (a + b) / 2
        half = np.linalg.norm(a - b) / 2
        t = math.sqrt(D2 ** 2 - half ** 2)
        u = -mid / np.linalg.norm(mid)  # inward
        S.append(mid + t * u)
    return np.vstack([V, np.array(S)])


if __name__ == '__main__':
    for m in (6, 8, 10, 12, 14, 16, 20):
        report(sharp(m), f"sharp m={m}")
    # N2: 60-degree rhombus a c b d, side 1, Delta = sqrt3 = |ab|
    a = np.array([0., 0.]); b = np.array([math.sqrt(3), 0.])
    c = np.array([math.sqrt(3) / 2, 0.5]); d = np.array([math.sqrt(3) / 2, -0.5])
    for th in (0.2, 0.4, 0.6):
        e = a + np.array([math.cos(th), math.sin(th) * 0.3])
        e = a + (e - a) / np.linalg.norm(e - a)
        f = b + np.array([-math.cos(th + 0.1), -math.sin(th + 0.1) * 0.3])
        f = b + (f - b) / np.linalg.norm(f - b)
        report(np.vstack([a, b, c, d, e, f]), f"N2-like th={th}")


def general_position(P, tol=1e-9):
    """Return (#collinear triples, #concyclic quadruples) with tolerance."""
    col = sum(1 for i, j, k in itertools.combinations(range(len(P)), 3)
              if abs(np.cross(P[j] - P[i], P[k] - P[i])) < tol)
    cc = 0
    for Q in itertools.combinations(range(len(P)), 4):
        M = np.array([[x, y, x * x + y * y, 1.0] for x, y in P[list(Q)]])
        if abs(np.linalg.det(M)) < tol:
            cc += 1
    return col, cc


if __name__ == '__main__':
    for th in (0.2, 0.4, 0.6):
        e = a + np.array([math.cos(th), math.sin(th) * 0.3]); e = a + (e - a) / np.linalg.norm(e - a)
        f = b + np.array([-math.cos(th + 0.1), -math.sin(th + 0.1) * 0.3]); f = b + (f - b) / np.linalg.norm(f - b)
        print('N2-like', th, '(collinear triples, concyclic quads) =', general_position(np.vstack([a, b, c, d, e, f])))
    print('sharp m=8 (collinear, concyclic) =', general_position(sharp(8)))

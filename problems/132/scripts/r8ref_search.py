"""R8 referee: independent adversarial search against the Charge Lemma (angle_R8_charge.md).

Written from scratch; does not use the proof's normal form or case split. Needs numpy + scipy
(homebrew python3).  Usage (always via tools/memcap.sh):

  python3 r8ref_search.py search MODE NSTARTS SEED     MODE in core | lemD | opp
  python3 r8ref_search.py gamma3                       witness for R8's gamma3 family (R5 correction)
  python3 r8ref_search.py rings                        tightness of Thm 6.1 / Charge Lemma on rings

search: x = 0, w = (1,0) and 7 (core/opp) or 6 (lemD) free angles:
  u = e(a0) [lemD: u = w], p = w + e(a1), b = p + e(a2), c = p + e(a3),
  p' = u + e(a4), b' = p' + e(a5), c' = p' + e(a6).
Constraints: hook (p,w,x) and hook (p',u,x) with w middle (b beyond pw from x, c on x's side),
u middle (b', c' likewise), orientations EQUAL (core, lemD) or OPPOSITE (opp = positive control,
realised by rings), p and p' extreme in the 9-point set, (p,w) != (p',u) by a margin, and (*):
every distance in (0,1] U {Delta} with Delta = max distance.  The objective is a sum of squared
normalised violations (distance gaps divided by Delta-1, sign margins).  A hit (objective < 1e-12)
would be polished and re-checked; none should exist if the Charge Lemma holds.
"""
from __future__ import annotations

import sys

import numpy as np
from scipy.optimize import minimize

MARG = 1e-3      # strictness margin for sign conditions (absolute; the scale is ~1)
SEP = 2e-2       # (p,w) != (p',u): max(|wu|, |pp'|) >= SEP


def e(a: float) -> np.ndarray:
    """Unit vector at angle a."""
    return np.array([np.cos(a), np.sin(a)])


def cr(o, a, b) -> float:
    """cross(o; a, b)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def build(th: np.ndarray, mode: str) -> dict:
    """Points of the configuration from the angle vector."""
    x = np.zeros(2); w = np.array([1.0, 0.0])
    if mode == 'lemD':
        u = w.copy(); a = th
        p = w + e(a[0]); b = p + e(a[1]); c = p + e(a[2])
        pp = u + e(a[3]); bp = pp + e(a[4]); cp = pp + e(a[5])
    else:
        a = th
        u = e(a[0]); p = w + e(a[1]); b = p + e(a[2]); c = p + e(a[3])
        pp = u + e(a[4]); bp = pp + e(a[5]); cp = pp + e(a[6])
    return dict(x=x, w=w, u=u, p=p, b=b, c=c, pp=pp, bp=bp, cp=cp)


def hinge(v: float, m: float = MARG) -> float:
    """Squared violation of v >= m."""
    return 0.0 if v >= m else (m - v) ** 2


def maxgap(o: np.ndarray, pts: list[np.ndarray]) -> float:
    """Largest cyclic angular gap of the directions from o to the points (distinct from o)."""
    ang = sorted(np.arctan2(q[1] - o[1], q[0] - o[0]) for q in pts if np.hypot(*(q - o)) > 1e-7)
    if len(ang) < 2:
        return 2 * np.pi
    gaps = [ang[i + 1] - ang[i] for i in range(len(ang) - 1)] + [ang[0] + 2 * np.pi - ang[-1]]
    return max(gaps)


def objective(th: np.ndarray, mode: str, detail: bool = False):
    """Sum of squared normalised violations."""
    P = build(th, mode)
    x, w, u, p, b, c, pp, bp, cp = (P[k] for k in ('x', 'w', 'u', 'p', 'b', 'c', 'pp', 'bp', 'cp'))
    terms = {}
    # hook 1: orientation +1; b strictly beyond line pw from x; c strictly on x's side
    terms['o1'] = hinge(cr(x, w, p))
    sx = cr(p, w, x)
    terms['x1'] = hinge(abs(sx))                         # x off line pw
    terms['b1'] = hinge(-np.sign(sx) * cr(p, w, b))
    terms['c1'] = hinge(np.sign(sx) * cr(p, w, c))
    # hook 2
    o2 = cr(x, u, pp)
    terms['o2'] = hinge(-o2) if mode == 'opp' else hinge(o2)
    sx2 = cr(pp, u, x)
    terms['x2'] = hinge(abs(sx2))
    terms['b2'] = hinge(-np.sign(sx2) * cr(pp, u, bp))
    terms['c2'] = hinge(np.sign(sx2) * cr(pp, u, cp))
    terms['sep'] = hinge(max(np.hypot(*(w - u)), np.hypot(*(p - pp))), SEP)
    terms['xp'] = hinge(np.hypot(*(x - p)), 1e-3) + hinge(np.hypot(*(x - pp)), 1e-3)
    pts = [x, w, u, p, b, c, pp, bp, cp]
    # extremality of p and p'
    terms['ext'] = hinge(maxgap(p, pts) - np.pi) + hinge(maxgap(pp, pts) - np.pi)
    # (*)
    ds = [np.hypot(*(pts[i] - pts[j])) for i in range(9) for j in range(i + 1, 9)]
    D = max(ds)
    terms['D>1'] = hinge(D - 1, 5e-3)
    gd = 0.0
    for dd in ds:
        if 1 < dd < D:
            gd += (min(dd - 1, D - dd) / max(D - 1, 1e-9)) ** 2
    terms['dist'] = gd
    tot = sum(terms.values())
    return (tot, terms, D) if detail else tot


def search(mode: str, n: int, seed: int) -> None:
    """Multi-start local minimisation."""
    rng = np.random.default_rng(seed)
    dim = 6 if mode == 'lemD' else 7
    best = []
    for i in range(n):
        th0 = rng.uniform(-np.pi, np.pi, dim)
        r = minimize(objective, th0, args=(mode,), method='Powell',
                     options=dict(xtol=1e-10, ftol=1e-14, maxfev=6000))
        r = minimize(objective, r.x, args=(mode,), method='Nelder-Mead',
                     options=dict(xatol=1e-12, fatol=1e-16, maxfev=4000))
        best.append((r.fun, r.x))
    best.sort(key=lambda q: q[0])
    vals = np.array([q[0] for q in best])
    print(f'mode={mode} starts={n} seed={seed} SEP={SEP} MARG={MARG}')
    print(f'  best objective {vals[0]:.3e}; #<1e-12: {(vals < 1e-12).sum()}; #<1e-8: {(vals < 1e-8).sum()};'
          f' #<1e-4: {(vals < 1e-4).sum()}; median {np.median(vals):.3e}')
    for f, th in best[:3]:
        tot, terms, D = objective(th, mode, True)
        nz = {k: f'{v:.2e}' for k, v in terms.items() if v > 0}
        print(f'  f={f:.3e} Delta={D:.6f} violated={nz}')


def gamma3() -> None:
    """Scan (s,t) for the gamma3 '+' family: all 21 distances admissible, side conditions (b),(c)
    hold, and p' is inside triangle u b' p (hence not extreme)."""
    wit = 0; tot = 0; bad_inside = 0; example = None
    for s in np.linspace(0.02, 0.5, 97):
        for t in np.linspace(0.02, 0.5, 97):
            d = np.sqrt(1 - (t - s) ** 2); k = np.sqrt(1 - s * s); D = np.sqrt(1 + 4 * s * t)
            x = np.array([-s, 0]); p = np.array([s, 0]); u = np.array([-t, -d]); b = np.array([t, -d])
            w = np.array([0, -k])
            if cr(x, u, w) <= 1e-9:
                continue
            bp = np.array([0.0, -np.sqrt(D * D - s * s)])     # |xb'| = |pb'| = D, on w's side of xp
            if not (cr(x, u, bp) >= 0 and cr(x, bp, b) > 1e-12):   # 0 <= A < A_b (case gamma3)
                continue
            l = np.hypot(*(u - bp))
            if l >= 1 or np.hypot(*(bp - b)) < 1e-9:
                continue
            M = (u + bp) / 2; nvec = np.array([-(bp - u)[1], (bp - u)[0]]) / l
            if np.dot(p - M, nvec) < 0:
                nvec = -nvec
            pp = M + np.sqrt(1 - l * l / 4) * nvec             # '+' apex
            pts = dict(x=x, p=p, b=b, u=u, w=w, pp=pp, bp=bp)
            names = list(pts)
            ok = True
            for i in range(7):
                for j in range(i + 1, 7):
                    dd = np.hypot(*(pts[names[i]] - pts[names[j]]))
                    if not (dd <= 1 + 1e-12 or abs(dd - D) < 1e-12):
                        ok = False
            # (b) p' strictly on w's side of xu; (c) x, b' strictly opposite sides of line u p'
            ok = ok and cr(x, u, pp) * cr(x, u, w) > 1e-9 and cr(u, pp, x) * cr(u, pp, bp) < -1e-9
            tot += 1
            if ok:
                wit += 1
                # p' in closed triangle u b' p?
                s1, s2, s3 = cr(u, bp, pp), cr(bp, p, pp), cr(p, u, pp)
                inside = (s1 >= -1e-12 and s2 >= -1e-12 and s3 >= -1e-12) or (s1 <= 1e-12 and s2 <= 1e-12 and s3 <= 1e-12)
                bad_inside += not inside
                if example is None:
                    example = (s, t, D, {k_: v.round(6).tolist() for k_, v in pts.items()})
    print(f'gamma3: grid points {tot}, full witnesses (21 distances admissible + (b),(c)) {wit}, '
          f'witnesses with p\' outside triangle u b\' p: {bad_inside}')
    print('  example', example)


def rings() -> None:
    """Regular m-gon + one server per edge: mu2 vs |L1|+|L2|+|V_D cap L1'|, hooks per (x, orientation)."""
    from scipy.spatial import ConvexHull
    for m in list(range(5, 17)):
        V = [e(2 * np.pi * j / m) for j in range(m)]
        D2 = 2 * np.cos(np.pi / m) if m % 2 == 0 else 2 * np.cos(3 * np.pi / (2 * m))
        S = []
        for j in range(m):
            dirn = -e(2 * np.pi * (j + 0.5) / m)
            # |r dirn - V_j| = D2, r > 0
            cj = np.dot(dirn, V[j]); r = cj + np.sqrt(cj * cj - 1 + D2 * D2)
            S.append(r * dirn)
        X = np.array(V + S); n = len(X)
        dist = np.hypot(*(X[:, None, :] - X[None, :, :]).transpose(2, 0, 1))
        iu = np.triu_indices(n, 1); vals = np.sort(dist[iu])[::-1]
        classes = []
        for v in vals:
            if classes and abs(classes[-1][0] - v) < 1e-9:
                classes[-1][1] += 1
            else:
                classes.append([v, 1])
        Dl, mu1 = classes[0]; Dd2, mu2 = classes[1]
        close = lambda a, b_: abs(a - b_) < 1e-9
        H1 = set(ConvexHull(X).vertices.tolist())
        rest = [i for i in range(n) if i not in H1]
        H2 = set(np.array(rest)[ConvexHull(X[rest]).vertices].tolist()) if len(rest) >= 3 else set(rest)
        W = H1 | H2
        adj = {i: {j for j in range(n) if j != i and close(dist[i, j], Dd2)} for i in range(n)}
        core = set(W)
        while True:
            rm = {v for v in core if len(adj[v] & core) < 2}
            if not rm:
                break
            core -= rm
        VD = {i for i in range(n) for j in range(n) if i != j and close(dist[i, j], Dl)}
        bound = len(H1) + len(H2) + len(VD & H1 & core)
        # hooks (unrestricted definition): p extreme, w middle unit nbr, x != p unit nbr of w
        cnt = {}
        for pi in H1:
            for wi in adj[pi]:
                sides = [np.sign(cr(X[pi], X[wi], X[q])) for q in adj[pi] if q != wi]
                if not (1 in sides and -1 in sides):
                    continue
                for xi in adj[wi]:
                    if xi == pi:
                        continue
                    o = int(np.sign(cr(X[xi], X[wi], X[pi])))
                    cnt[(xi, o)] = cnt.get((xi, o), 0) + 1
        print(f'm={m:2d} n={n} mu1={mu1} mu2={mu2} |L1|={len(H1)} |L2|={len(H2)} '
              f'|VD cap L1\'|={len(VD & H1 & core)} bound={bound} tight={mu2 == bound} '
              f'hooks={sum(cnt.values())} max per (x,eps)={max(cnt.values()) if cnt else 0}')


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'search':
        search(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
    elif cmd == 'gamma3':
        gamma3()
    elif cmd == 'rings':
        rings()

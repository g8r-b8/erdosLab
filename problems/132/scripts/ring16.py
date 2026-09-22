"""Problem 1.6 (min{mu(Delta_2), mu(delta)}) ring constructions + symmetric gadget screening.

ring_core(m): regular m-gon v_j (circumradius 1) + servers u_i in C(v_i,D2) cap C(v_{i+1},D2)
(the inner intersection point).  For even m this is ienjoymath's construction.
Everything with float64 for screening; mpmath verification in verify16.py.

Marginal-value criterion (LP dual at the 9/7 optimum, weights 4/7 on Delta_2 and 3/7 on delta):
a new point with Delta_2-degree a and delta-degree b is a strict improvement iff 4a+3b > 9;
patch points (0,3) and the ring core (1.5,1 per point) are both exactly tight.
"""
import math, cmath, itertools, sys
import numpy as np

TOL = 1e-9


def ring_core(m):
    al = 2 * math.pi / m
    v = [cmath.exp(1j * al * j) for j in range(m)]
    # chords
    ch = sorted({round(abs(v[0] - v[k]), 12) for k in range(1, m)})
    D, D2 = ch[-1], ch[-2]
    us = []
    for i in range(m):
        a, b = v[i], v[(i + 1) % m]
        for p in circ_int(a, D2, b, D2):
            if abs(p) < 1 - 1e-12 and all(abs(p - w) <= D2 + 1e-9 for w in v):
                us.append(p)
    return v, us, D, D2


def circ_int(c1, r1, c2, r2):
    d = abs(c2 - c1)
    if d < 1e-15 or d > r1 + r2 + 1e-15 or d < abs(r1 - r2) - 1e-15:
        return []
    a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
    h2 = r1 * r1 - a * a
    h = math.sqrt(max(h2, 0.0))
    e = (c2 - c1) / d
    base = c1 + a * e
    return [base + 1j * h * e, base - 1j * h * e]


def spectrum(X):
    X = np.array(X)
    d = np.abs(X[:, None] - X[None, :])[np.triu_indices(len(X), 1)]
    d = np.sort(d)
    classes = []
    for x in d:
        if classes and abs(x - classes[-1][0]) < TOL:
            classes[-1][1] += 1
        else:
            classes.append([x, 1])
    return classes


def summary(X):
    sp = spectrum(X)
    return dict(n=len(X), delta=sp[0][0], mu_delta=sp[0][1], D2=sp[-2][0], mu_D2=sp[-2][1],
                D=sp[-1][0], mu_D=sp[-1][1], ndist=len(sp))


def hex_patch(P, g, center=0j):
    """Harborth-type spiral hexagonal patch with P points, mesh g."""
    w = cmath.exp(1j * math.pi / 3)
    pts = [0j]
    # spiral shells
    k = 1
    while len(pts) < P:
        p = k * 1 + 0j
        dirs = [w ** (2 + t) for t in range(6)]
        for dd in dirs:
            for _ in range(k):
                if len(pts) < P:
                    pts.append(p)
                p += dd
        k += 1
    return [center + g * p for p in pts[:P]]


def construction(m, n):
    v, us, D, D2 = ring_core(m)
    core = v + us
    sp = spectrum(core)
    g = sp[0][0]
    P = n - len(core)
    X = core + (hex_patch(P, g) if P > 0 else [])
    return X, g, D2


def screen_gadgets(m, extra_rounds=1):
    """Generate candidates = intersections of circles (radius g or D2) around pairs of
    existing core points; keep those valid (all distances to core >= g-tol and <= D2+tol,
    rotated copies mutually >= g), report (a,b) and 4a+3b."""
    v, us, D, D2 = ring_core(m)
    core = v + us
    g = spectrum(core)[0][0]
    radii = [g, D2]
    cands = []
    # only need candidates near one sector by symmetry; use pairs of points within 3g
    # of the server u_0 (for D2-circles, use their far centres too)
    loc = [p for p in core if abs(p - us[0]) < 4 * g] if us else core[:4]
    for p, q in itertools.combinations(core, 2):
        if not (p in loc or q in loc):
            continue
        for r1 in radii:
            for r2 in radii:
                for x in circ_int(p, r1, q, r2):
                    if abs(x - us[0]) < 4 * g:
                        cands.append(x)
    res = []
    seen = set()
    rot = [cmath.exp(2j * math.pi * k / m) for k in range(m)]
    for x in cands:
        key = (round(x.real, 7), round(x.imag, 7))
        if key in seen:
            continue
        seen.add(key)
        ds = np.abs(np.array(core) - x)
        if ds.min() < g - TOL or ds.max() > D2 + TOL:
            continue
        # rotated copies distances
        cop = np.array([x * r for r in rot[1:]])
        dc = np.abs(cop - x)
        if dc.min() < g - TOL or dc.max() > D2 + TOL:
            continue
        a = int(np.sum(np.abs(ds - D2) < TOL)) + int(np.sum(np.abs(dc - D2) < TOL)) / 2
        b = int(np.sum(np.abs(ds - g) < TOL)) + int(np.sum(np.abs(dc - g) < TOL)) / 2
        res.append((4 * a + 3 * b, a, b, x))
    res.sort(key=lambda t: -t[0])
    return g, D2, res


if __name__ == '__main__':
    for n in [int(x) for x in sys.argv[1].split(',')]:
        best = None
        for m in range(6, n // 2 + 1):
            X, g, D2 = construction(m, n)
            s = summary(X)
            ok = abs(s['delta'] - g) < TOL and abs(s['D2'] - D2) < TOL
            val = min(s['mu_D2'], s['mu_delta'])
            if ok and (best is None or val > best[0]):
                best = (val, m, s)
        print(n, 'best m', best[1], 'min', best[0], 'ratio %.4f' % (best[0] / n), '9/7n=%.1f' % (9 * n / 7), best[2])

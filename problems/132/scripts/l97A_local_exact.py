"""Route A (L97): EXACT (Fraction, angles in degrees) verification of the local A-point lemmas.

For an A-point a with neighbour directions n_1..n_d (pairwise >= 60 deg apart, all strictly within
90 deg of EVERY inward normal in the normal cone [th1, th2] of K at a):
  E_a   = {phi : no neighbour within open 30 deg of phi}
  J_a   = E_a \\ (-E_a)
  s_a   = (largest gap) - 180   (s_a = 180 if d <= 1)
  X_a   = int_{J_a} sup_{th in [th1,th2]} clamp(120 - dist(phi, th), 0, 60) dphi   (deg^2)
Lemma 5:  |E_a u -E_a| >= 240 + 2 min(s_a, 60)
Lemma 6:  X_a <= min(s_a, 60)^2
(*)       |E_a u -E_a| - (6/pi) X_a >= 4pi/3, i.e. in degrees  |EuE|/180 - 6 X_a/180^2 >= 4/3.
All arithmetic is exact (fractions.Fraction); the integrand is piecewise linear, integrated exactly.
Usage: .venv/bin/python l97A_local_exact.py [step_deg] [nrandom]
"""
from fractions import Fraction as F
import itertools
import random
import sys

FULL = F(360)


def norm(a):
    a = F(a) % FULL
    return a


def arc(lo, hi):
    """open ccw arc (lo, hi), length in (0, 360] -> list of (a,b) inside [0,360)."""
    L = F(hi) - F(lo)
    if L <= 0:
        return []
    if L >= FULL:
        return [(F(0), FULL)]
    lo = norm(lo)
    hi = lo + L
    if hi <= FULL:
        return [(lo, hi)]
    return [(lo, FULL), (F(0), hi - FULL)]


def union(ivs):
    ivs = sorted(i for i in ivs if i[1] > i[0])
    out = []
    for a, b in ivs:
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def meas(ivs):
    return sum((b - a for a, b in union(ivs)), F(0))


def neg(ivs):
    out = []
    for a, b in ivs:
        out += arc(a + 180, b + 180)
    return union(out)


def inter(X, Y):
    out = []
    for a, b in union(X):
        for c, d in union(Y):
            lo, hi = max(a, c), min(b, d)
            if hi > lo:
                out.append((lo, hi))
    return union(out)


def minus(X, Y):
    comp, prev = [], F(0)
    for a, b in union(Y):
        if a > prev:
            comp.append((prev, a))
        prev = max(prev, b)
    if prev < FULL:
        comp.append((prev, FULL))
    return inter(X, comp)


def E_set(nbrs):
    if not nbrs:
        return [(F(0), FULL)]
    s = sorted(norm(x) for x in nbrs)
    d = len(s)
    out = []
    for k in range(d):
        a = s[k]
        gap = FULL if d == 1 else (s[(k + 1) % d] - a) % FULL
        out += arc(a + 30, a + gap - 30)
    return union(out)


def cdist(x, y):
    d = (F(x) - F(y)) % FULL
    return min(d, FULL - d)


def dist_to_arc(phi, th1, th2):
    """distance on the circle from phi to the closed ccw arc [th1, th2] (th2 - th1 in [0,180))."""
    if (F(phi) - th1) % FULL <= (th2 - th1):
        return F(0)
    return min(cdist(phi, th1), cdist(phi, th2))


def integrand(phi, th1, th2):
    v = 120 - dist_to_arc(phi, th1, th2)
    return max(F(0), min(v, F(60)))


def integrate(ivs, th1, th2):
    """exact integral of the piecewise-linear integrand over a union of intervals."""
    # breakpoints: where dist_to_arc changes formula, where 120-dist crosses 0 or 60
    bps = set()
    for base in (th1, th2):
        for off in (0, 60, 120, 180, -60, -120):
            bps.add(norm(base + off))
    mid = norm(th1 + (th2 - th1) / 2 + 180)
    bps.add(mid)
    tot = F(0)
    for a, b in ivs:
        pts = sorted({a, b} | {p for p in bps if a < p < b})
        for u, v in zip(pts, pts[1:]):
            # linear on [u,v]: Simpson/trapezoid exact for linear pieces
            tot += (v - u) * (integrand(u, th1, th2) + integrand(v, th1, th2)) / 2
    return tot


def s_value(nbrs):
    d = len(nbrs)
    if d <= 1:
        return F(180)
    s = sorted(norm(x) for x in nbrs)
    gaps = [((s[(k + 1) % d] - s[k]) % FULL) for k in range(d)]
    return max(gaps) - 180


def admissible(nbrs, th1, th2):
    for n in nbrs:
        for th in (th1, th2):
            if not cdist(n, th) < 90:
                return False
    for x, y in itertools.combinations(nbrs, 2):
        if cdist(x, y) < 60:
            return False
    return True


def check_one(nbrs, th1, th2, stats):
    E = E_set(nbrs)
    nE = neg(E)
    U = meas(union(E + nE))
    J = minus(E, nE)
    X = integrate(J, th1, th2)
    s = s_value(nbrs)
    m = min(s, F(60))
    assert U >= 240 + 2 * m, ('Lemma5', nbrs, th1, th2, U, s)
    assert X <= m * m, ('Lemma6', nbrs, th1, th2, X, s)
    lhs = U / 180 - 6 * X / (180 * 180)
    assert lhs >= F(4, 3), ('star', nbrs, th1, th2, lhs)
    stats['n'] += 1
    slack = lhs - F(4, 3)
    if slack < stats['min']:
        stats['min'], stats['arg'] = slack, (tuple(nbrs), th1, th2)


def main():
    step = F(sys.argv[1]) if len(sys.argv) > 1 else F(5)
    nrand = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    stats = {'n': 0, 'min': F(10), 'arg': None}
    # inward normal cone [th1, th2] containing 270; neighbours strictly within 90 of all of it
    grid = [F(180) + step * k for k in range(1, int(180 / step))]
    cones = [(F(270) - a, F(270) + b) for a in (0, step, 2 * step, 30, 60, 89)
             for b in (0, step, 30, 60) if a + b < 90]
    for d in range(0, 4):
        for nbrs in itertools.combinations(grid, d):
            for th1, th2 in cones:
                if admissible(nbrs, th1, th2):
                    check_one(list(nbrs), th1, th2, stats)
    rng = random.Random(7)
    for _ in range(nrand):
        d = rng.randint(1, 3)
        nb = [F(rng.randint(180 * 997 + 1, 360 * 997 - 1), 997) for _ in range(d)]
        a, b = F(rng.randint(0, 60 * 97), 97), F(rng.randint(0, 60 * 97), 97)
        th1, th2 = 270 - a, 270 + b
        if th2 - th1 < 180 and admissible(nb, th1, th2):
            check_one(nb, th1, th2, stats)
    print('checked', stats['n'], 'configurations exactly; min slack in (*) =', stats['min'],
          '=', float(stats['min']), 'at', [str(x) for x in stats['arg'][0]], stats['arg'][1:])
    print('LOCAL LEMMAS 5, 6, (*) HOLD EXACTLY ON ALL TESTED CONFIGURATIONS')


if __name__ == '__main__':
    main()

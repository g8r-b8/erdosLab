"""Route A (L97): test configurations for l97A_check.py.

ring        : unit-chord polygon inscribed in a disc (Def = 2|A|, the tight case)
ringpath    : the ring cut into A-paths of length k (gaps)
eis         : triangular (Eisenstein) lattice, K = disc of radius sqrt(N) with N = 7*13*19 (48 lattice
              points exactly on bK), Yout = lattice points of depth < rho
Lk          : angle_R6 L family (r6_gap_L_family.build), k = 1..4
Mpair       : angle_R6 M pair-gap row (A-chords alternate 1 and 1+eps, inward apex row at unit steps)
rand*       : random unit-distance growth inside a Reuleaux triangle / lens / disc, A-points on bK
"""
import math
import random
import sys
import os
from l97A_common import Config, dist

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def ring(N=60, rho=1):
    R = 1 / (2 * math.sin(math.pi / N))
    Y = [(R * math.cos(2 * math.pi * k / N), R * math.sin(2 * math.pi * k / N)) for k in range(N)]
    return Config([(0.0, 0.0)], R, Y, rho, core_pt=(0.0, 0.0), name=f'ring{N}')


def ringpath(N=60, k=3, rho=1):
    R = 1 / (2 * math.sin(math.pi / N))
    Y = [(R * math.cos(2 * math.pi * j / N), R * math.sin(2 * math.pi * j / N)) for j in range(N)
         if j % (k + 1) != k]
    return Config([(0.0, 0.0)], R, Y, rho, core_pt=(0.0, 0.0), name=f'ringpath{N}_{k}')


def eis(Nn=7 * 13 * 19, rho=2):
    R = math.sqrt(Nn)
    Y = []
    M = int(R) + 3
    for a in range(-2 * M, 2 * M + 1):
        for b in range(-2 * M, 2 * M + 1):
            nrm = a * a + a * b + b * b
            if nrm <= Nn and R - math.sqrt(nrm) < rho + 0.5:
                Y.append((a + b / 2, b * math.sqrt(3) / 2))
    return Config([(0.0, 0.0)], R, Y, rho, core_pt=(0.0, 0.0), name=f'eis{Nn}_rho{rho}')


def Lfam(k, R=50, rho=2):
    import r6_gap_L_family as L
    paths = L.build(k, L.mp.mpf(R))
    pts = []
    for p in paths:
        for z in p['P']:
            pts.append(complex(z))
        for (_, q) in p['rungs']:
            pts.append(complex(q))
    Y = []
    for z in pts:
        if all(abs(z - w) > 1e-9 for w in Y):
            Y.append(z)
    Y = [(z.real, z.imag) for z in Y]
    return Config([(0.0, 0.0)], float(R), Y, rho, core_pt=(0.0, 0.0), name=f'L{k}_R{R}')


def Mpair(R=50.0, nchords=24, rho=2):
    import mpmath as mp
    mp.mp.dps = 30
    R = mp.mpf(R)

    def build(L, nch):
        a1 = 2 * mp.asin(1 / (2 * R))
        aL = 2 * mp.asin(L / (2 * R))
        angs = [mp.mpf(0)]
        for j in range(nch):
            angs.append(angs[-1] - (a1 if j % 2 == 0 else aL))
        P = [R * mp.expj(t) for t in angs]

        def apex(p, q):
            m = (p + q) / 2
            d = abs(q - p)
            hh = mp.sqrt(1 - (d / 2) ** 2)
            return m + hh * (-m / abs(m))
        C = [apex(P[i], P[i + 1]) for i in range(nch)]
        return P, C

    L = mp.findroot(lambda L: abs(build(L, 2)[1][1] - build(L, 2)[1][0]) - 1, mp.mpf('1.0002'))
    P, C = build(L, nchords)
    Y = [(float(z.real), float(z.imag)) for z in P + C]
    return Config([(0.0, 0.0)], float(R), Y, rho, core_pt=(0.0, 0.0), name=f'Mpair_R{float(R)}')


# ------------------------------------------------------------------ random growth
def boundary_points(centers, R, step_lo=1.0, step_hi=1.4, rng=None, corners=True):
    """A-points along bK = intersection of discs: sample the boundary finely, then greedily
    keep points at mutual distance >= 1 with random extra spacing."""
    fine = []
    m = len(centers)
    for w in centers:
        for k in range(20000):
            t = 2 * math.pi * k / 20000
            z = (w[0] + R * math.cos(t), w[1] + R * math.sin(t))
            if min(R - dist(z, v) for v in centers) > -1e-12:
                fine.append((math.atan2(z[1] - cy(centers), z[0] - cx(centers)), z))
    fine.sort()
    out = []
    if corners:
        from l97A_common import circle_inter
        for i in range(m):
            for j in range(i + 1, m):
                for z in circle_inter(centers[i], centers[j], R):
                    if min(R - dist(z, v) for v in centers) > -1e-9:
                        out.append(z)
    need = rng.uniform(step_lo, step_hi)
    for _, z in fine:
        if all(dist(z, q) >= need for q in out):
            # snap exactly onto the circle it lies on (already exact up to float)
            out.append(z)
            need = rng.uniform(step_lo, step_hi)
    return out


def cx(c):
    return sum(w[0] for w in c) / len(c)


def cy(c):
    return sum(w[1] for w in c) / len(c)


def grow(centers, R, rho, seed, n_iter=4000, name='rand', gap=(1.0, 1.4), corners=True):
    rng = random.Random(seed)
    A = boundary_points(centers, R, gap[0], gap[1], rng, corners)
    pts = list(A)

    def depth(z):
        return min(R - dist(z, w) for w in centers)

    def ok(z):
        d = depth(z)
        return 1e-6 < d < rho - 1e-6 and all(dist(z, q) > 1 - 1e-9 for q in pts)

    # grid hash for speed
    for it in range(n_iter):
        if rng.random() < 0.8:
            p = rng.choice(pts)
            near = [q for q in pts if 1 - 1e-9 < dist(p, q) < 2 - 1e-9]
            if not near:
                continue
            q = rng.choice(near)
            d = dist(p, q)
            mx, my = (p[0] + q[0]) / 2, (p[1] + q[1]) / 2
            hh = math.sqrt(1 - (d / 2) ** 2)
            ux, uy = (q[0] - p[0]) / d, (q[1] - p[1]) / d
            for sgn in (1, -1):
                z = (mx - sgn * hh * uy, my + sgn * hh * ux)
                if ok(z):
                    pts.append(z)
                    break
        else:
            p = rng.choice(pts)
            t = rng.uniform(0, 2 * math.pi)
            z = (p[0] + math.cos(t), p[1] + math.sin(t))
            if ok(z):
                pts.append(z)
    # fix A-points to exact boundary (they are, up to float); interior points have depth > 1e-6
    return Config(centers, R, pts, rho, name=f'{name}_s{seed}')


def reuleaux(R=20.0):
    return [(0.0, 0.0), (R, 0.0), (R / 2, R * math.sqrt(3) / 2)]


def lens(R=20.0, d=30.0):
    return [(0.0, 0.0), (d, 0.0)]


def pentagon(R=20.0, s=0.9):
    # 5 centers on a circle of radius s*R  -> a rounded pentagon-like K
    return [(s * R * math.cos(2 * math.pi * k / 5), s * R * math.sin(2 * math.pi * k / 5)) for k in range(5)]


def all_configs(quick=False):
    out = [ring(24), ring(60), ringpath(60, 3), ringpath(60, 1), Mpair(), Lfam(1), Lfam(2), Lfam(3),
           Lfam(4)]
    out.append(eis(7 * 13, 2) if quick else eis(7 * 13 * 19, 2))
    seeds = range(2) if quick else range(6)
    for s in seeds:
        out.append(grow(reuleaux(16.0), 16.0, 2, s, n_iter=1500 if quick else 3000, name='reul'))
        out.append(grow(lens(16.0, 24.0), 16.0, 2, 100 + s, n_iter=1500 if quick else 3000, name='lens'))
        out.append(grow(pentagon(16.0, 0.35), 16.0, 3, 200 + s, n_iter=1500 if quick else 3000,
                        name='pent', gap=(1.0, 1.1)))
        # tight: A-points at unit arc spacing (many A-A edges, ring-like A-paths), dense shell
        out.append(grow(reuleaux(14.0), 14.0, 2, 300 + s, n_iter=2500 if quick else 6000,
                        name='reulT', gap=(1.0, 1.0)))
        out.append(grow(lens(14.0, 20.0), 14.0, 3, 400 + s, n_iter=2500 if quick else 6000,
                        name='lensT', gap=(1.0, 1.0)))
    if not quick:
        out.append(eis(7 * 13 * 19, 3))
        out.append(eis(7 * 13 * 19 * 31, 2))
    return out

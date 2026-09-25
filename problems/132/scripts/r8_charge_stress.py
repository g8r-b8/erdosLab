"""R8 Charge Lemma: floating-point adversarial stress test of each step of the proof.

NOT part of the proof (the proof in angle_R8_charge.md is complete without computation).
Purpose: independently confirm, on dense grids that include every equality stratum
(2s=1, 2t=1, 2s=Delta, 2t=Delta, and all angles where some new distance equals 1 or Delta),
that each intermediate claim of the proof holds, and that the whole core configuration has
no realisation even when only the hypotheses actually used by the proof are imposed.

usage: python3 r8_charge_stress.py N     (grid resolution; N=60 takes ~1 min)
"""
from __future__ import annotations

import math
import sys
from collections import Counter

Pt = tuple[float, float]


def cross(o: Pt, a: Pt, b: Pt) -> float:
    """Signed area (a-o) x (b-o)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def circle_pts(p: Pt, q: Pt, r1: float, r2: float) -> list[Pt]:
    """Intersection points of C(p, r1) and C(q, r2) (0, 1 or 2 points)."""
    dd = math.dist(p, q)
    if dd < 1e-14 or dd > r1 + r2 + 1e-12 or dd < abs(r1 - r2) - 1e-12:
        return []
    a = (r1 * r1 - r2 * r2 + dd * dd) / (2 * dd)
    h = math.sqrt(max(r1 * r1 - a * a, 0.0))
    ux, uy = (q[0] - p[0]) / dd, (q[1] - p[1]) / dd
    mx, my = p[0] + a * ux, p[1] + a * uy
    if h < 1e-15:
        return [(mx, my)]
    return [(mx - h * uy, my + h * ux), (mx + h * uy, my - h * ux)]


TOL = 1e-9


def dist_ok(dd: float, Dl: float) -> bool:
    """The only hypothesis on distances: every distance of distinct points is <= 1 or = Delta."""
    return dd <= 1 + TOL or abs(dd - Dl) < TOL


def trapezoid(s: float, t: float) -> tuple[float, dict[str, Pt]] | None:
    """Hook-1 + trapezoid configuration in frame T, or None if a hypothesis fails.

    Hypotheses checked: 0<s<1, |t-s|<1; all 10 distances among x,p,u,b,w in (0,1] u {Delta};
    u strictly beyond line xw from p; b strictly beyond line pw from x.
    """
    if not (0 < s < 1 and t > 0 and abs(t - s) < 1):
        return None
    d, k = math.sqrt(1 - (t - s) ** 2), math.sqrt(1 - s * s)
    Dl = math.sqrt(1 + 4 * s * t)
    P = {'x': (-s, 0.0), 'p': (s, 0.0), 'u': (-t, -d), 'b': (t, -d), 'w': (0.0, -k)}
    x, p, u, b, w = P['x'], P['p'], P['u'], P['b'], P['w']
    if not (cross(x, w, u) * cross(x, w, p) < 0 and cross(p, w, b) * cross(p, w, x) < 0):
        return None
    names = list(P)
    for i in range(5):
        for j in range(i + 1, 5):
            if not dist_ok(math.dist(P[names[i]], P[names[j]]), Dl):
                return None
    return Dl, P


def is_extreme(q: Pt, pts: list[Pt]) -> bool:
    """True iff q is a strict vertex of conv(pts) (largest angular gap > pi)."""
    angs = sorted(math.atan2(r[1] - q[1], r[0] - q[0]) for r in pts if math.dist(q, r) > 1e-9)
    if len(angs) < 2:
        return True
    gaps = [(angs[(i + 1) % len(angs)] - angs[i]) % (2 * math.pi) for i in range(len(angs))]
    if len(angs) >= 2 and max(gaps) == 0:
        return True
    return max(gaps) > math.pi + 1e-9


def st_grid(N: int) -> list[tuple[float, float]]:
    """(s,t) grid including the strata 2s=1, 2t=1, 2s=Delta, 2t=Delta, s=2t."""
    out: list[tuple[float, float]] = []
    for i in range(1, N):
        s = i / N
        out += [(s, j / N + 1e-6) for j in range(1, 2 * N)]      # generic
        out += [(s, 0.5), (s, s / 2), (s, s / 2 + 1e-7)]          # 2t = 1, s = 2t (and just above)
        out.append((s, (4 * s + math.sqrt(16 * s * s + 16)) / 8))  # 2t = Delta: 4t^2 = 1 + 4st
        if s > 0.5:
            out.append((s, (4 * s * s - 1) / (4 * s)))              # 2s = Delta: 4s^2 = 1 + 4st
    out += [(0.5, j / N + 1e-6) for j in range(1, 2 * N)]          # 2s = 1
    phi = (1 + math.sqrt(5)) / 2
    out += [(0.5, phi / 2), (phi / 2, 0.5)]                          # regular-pentagon corners
    return out


def to_frame_F(P: dict[str, Pt]) -> dict[str, complex]:
    """Frame F: x = 0, u on the positive real axis, w in the upper half-plane."""
    x = complex(*P['x'])
    Z = {k_: complex(*v) - x for k_, v in P.items()}
    rot = abs(Z['u']) / Z['u']
    Z = {k_: v * rot for k_, v in Z.items()}
    if Z['w'].imag < 0:
        Z = {k_: v.conjugate() for k_, v in Z.items()}
    return Z


def in_closed_triangle(q: complex, a: complex, b: complex, c: complex, eps: float = 1e-12) -> bool:
    """q in the closed triangle abc (orientation-free)."""
    cr_ = lambda o, a_, b_: ((a_ - o).conjugate() * (b_ - o)).imag
    s1, s2, s3 = cr_(a, b, q), cr_(b, c, q), cr_(c, a, q)
    return (s1 >= -eps and s2 >= -eps and s3 >= -eps) or (s1 <= eps and s2 <= eps and s3 <= eps)


def stress_step1(N: int) -> Counter:
    """Step 1: every admissible (p', b') has b' = b; each other case dies for the stated reason.

    b' is swept over C(x, Delta) (N*40 angles plus the special points b, p, and the point
    b'_ii of C(x,Delta) n C(p,Delta) on the u-side); p' ranges over C(u,1) n C(b',1).  Only
    the hypotheses used in the proof are imposed on (p', b'): p' strictly on w's side of xu,
    p' != x, b' strictly beyond line up' from x.
    """
    C: Counter = Counter()
    ang = lambda z: math.atan2(z.imag, z.real)
    cr_ = lambda o, a_, b_: ((a_ - o).conjugate() * (b_ - o)).imag
    for (s, t) in st_grid(N):
        T = trapezoid(s, t)
        if T is None:
            continue
        Dl, P = T
        Z = to_frame_F(P)
        U, Pp, B = Z['u'], Z['p'], Z['b']
        thp, Ab = ang(Pp), ang(B)
        if not (0 < Ab < thp < math.pi):
            C['FAIL frame order'] += 1
            continue
        C['trapezoids'] += 1
        Asp = [2 * math.pi * a / (40 * N) - math.pi for a in range(40 * N)] + [Ab, thp]
        # b'_ii: |xb'| = |pb'| = Delta, on the u-side of line xp
        for q in circle_pts((0.0, 0.0), (Pp.real, Pp.imag), Dl, Dl):
            if cr_(0, Pp, complex(*q)) * cr_(0, Pp, U) > 0:
                Asp.append(ang(complex(*q)))
        for A in Asp:
            bp = Dl * complex(math.cos(A), math.sin(A))
            for q in circle_pts((U.real, U.imag), (bp.real, bp.imag), 1.0, 1.0):
                pp = complex(*q)
                if pp.imag <= 1e-12 or abs(pp) < 1e-12:
                    continue
                if cr_(U, pp, 0) * cr_(U, pp, bp) >= -1e-12:
                    continue
                C['admissible (p\',b\')'] += 1
                g = ang(pp)
                if not (-1e-12 <= A <= thp + 1e-12):
                    pts = [0, bp, Pp, U]
                    mx = max(abs(a_ - b_) for a_ in pts for b_ in pts)
                    C['out of cone: some distance > Delta' if mx > Dl + 1e-12 else 'FAIL crossing'] += 1
                elif A > g + 1e-12:
                    C['alpha: p\' in triangle x u b\'' if in_closed_triangle(pp, 0, U, bp)
                      else 'FAIL alpha'] += 1
                elif abs(A - g) <= 1e-12:
                    C['beta'] += 1
                elif A > Ab + 1e-12:
                    dpb = abs(pp - B)
                    C['gamma1: 1 < |p\'b| < Delta' if 1 + 1e-12 < dpb < Dl - 1e-12 else 'FAIL gamma1'] += 1
                elif abs(A - Ab) <= 1e-12:
                    C['gamma2: b\' = b'] += 1
                else:
                    dpb2 = abs(Pp - bp)
                    lub = abs(U - bp)
                    if not (dpb2 > 1 + 1e-12 and lub < 2 * t - 1e-12):
                        C['FAIL gamma3 monotone'] += 1
                    elif abs(dpb2 - Dl) > 1e-9:
                        C['gamma3: |pb\'| in (1,Delta) u (Delta,oo)'] += 1
                    elif in_closed_triangle(pp, U, bp, Pp):
                        C['gamma3+: p\' in triangle u b\' p'] += 1
                    elif abs(Pp - pp) > Dl + 1e-9 and lub <= 1 + 1e-9:
                        C['gamma3-: |pp\'| > Delta'] += 1
                    else:
                        C['FAIL gamma3 apex'] += 1
    return C


def stress_step2_3(N: int) -> Counter:
    """Steps 2-3: with b'=b, P2 fails a side condition, P1 extreme iff s>2t, and then every
    unit neighbour c' of p' in the extremality range has |c'p| > Delta.

    Also checks the extremality-range claim: a unit neighbour c' of p' strictly on x's side of
    line p'u but outside (pi/2+phi, 3pi/2-phi) makes p' non-extreme in {u, b, c'}.
    """
    C: Counter = Counter()
    worst = math.inf
    for (s, t) in st_grid(N):
        T = trapezoid(s, t)
        if T is None:
            continue
        Dl, P = T
        x, p, u, b, w = P['x'], P['p'], P['u'], P['b'], P['w']
        if t >= 1:
            continue
        d, c = -u[1], math.sqrt(1 - t * t)
        P1, P2 = (0.0, c - d), (0.0, -d - c)
        # P2: the two side conditions of hook 2 are incompatible
        sw = cross(x, u, P2) * cross(x, u, w) > 0
        sb = cross(u, P2, b) * cross(u, P2, x) < 0
        C['P2: side conditions incompatible' if not (sw and sb) else 'FAIL P2'] += 1
        # P1: extreme iff s > 2t
        ext = is_extreme(P1, [x, p, u, b, w, P1])
        if s <= 2 * t + 1e-12:
            C['P1, s<=2t: not extreme' if not ext else 'FAIL P1 extreme with s<=2t'] += 1
            continue
        C['P1, s>2t'] += 1
        phi = math.asin(t)
        for a in range(1, 2000):
            gam = math.pi / 2 - phi + (math.pi) * a / 2000        # whole open x-side of line p'u
            cp = (math.cos(gam), P1[1] + math.sin(gam))
            if cross(P1, u, cp) * cross(P1, u, x) <= 0:
                C['FAIL side param'] += 1
                continue
            inrange = math.pi / 2 + phi < gam < 3 * math.pi / 2 - phi
            if not inrange:
                C['c\' outside range: p\' not extreme' if not is_extreme(P1, [u, b, cp, P1])
                  else 'FAIL range'] += 1
                continue
            gap = math.dist(cp, p) - Dl
            if gap <= 0:
                C['FAIL step3'] += 1
            else:
                C['c\' in range: |c\'p| > Delta'] += 1
                # normalised margin: gap / (distance of gamma to the endpoint c'=u)
                worst = min(worst, gap / (3 * math.pi / 2 - phi - gam))
    C['min normalised margin x1e6'] = int(worst * 1e6)
    return C


def stress_lemma_D(N: int) -> Counter:
    """Lemma D: two same-orientation hooks through one middle vertex w never coexist.

    Frame W: w=0, x=e(0), p=e(th), p'=e(th2), 0<th<th2<pi, b' = rho e(th/2) with
    rho = 2cos(th2 - th/2), Delta := |xb'|.  Checks: rho < 0 (else Delta <= 1), and some
    pairwise distance among {w,x,p,p',b'} lies in (1,Delta) or exceeds Delta.  The equality
    stratum Delta = |xp'| is sampled separately by bisection in th2.
    """
    C: Counter = Counter()
    E = lambda a: complex(math.cos(a), math.sin(a))

    def verdict(th: float, th2: float) -> str:
        rho = 2 * math.cos(th2 - th / 2)
        if rho >= -1e-9:   # rho = 0 up to rounding when th2 - th/2 = pi/2 exactly
            return 'rho >= 0 (Delta <= 1)'
        pts = [0j, E(0), E(th), E(th2), rho * E(th / 2)]
        Dl = abs(pts[4] - pts[1])
        if Dl <= 1 + 1e-12:
            return 'FAIL Delta <= 1 with rho < 0'
        bad = any(1 + 1e-9 < abs(a - b) < Dl - 1e-9 or abs(a - b) > Dl + 1e-9
                  for i, a in enumerate(pts) for b in pts[i + 1:])
        return 'dead: a distance in (1,Delta) u (Delta,oo)' if bad else 'FAIL lemma D'

    M = 40 * N
    for i in range(1, M):
        th = math.pi * i / M
        for j in range(i + 1, M):
            C[verdict(th, math.pi * j / M)] += 1
        # stratum Delta = |xp'|: roots of f(th2) = |xb'|^2 - |xp'|^2 on (th, pi)
        f = lambda th2: abs(2 * math.cos(th2 - th / 2) * E(th / 2) - 1) ** 2 - abs(E(th2) - 1) ** 2
        grid = [th + (math.pi - th) * q / 400 for q in range(1, 400)]
        for a_, b_ in zip(grid, grid[1:]):
            if f(a_) * f(b_) < 0:
                lo, hi = a_, b_
                for _ in range(80):
                    mid = (lo + hi) / 2
                    lo, hi = (mid, hi) if f(lo) * f(mid) > 0 else (lo, mid)
                C['stratum |xp\'| = Delta: ' + verdict(th, (lo + hi) / 2)] += 1
    return C


def main() -> int:
    """Run all stress tests; return 0 iff no FAIL key appears."""
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    nfail = 0
    for name, fn, arg in (('step 1', stress_step1, N), ('steps 2-3', stress_step2_3, N),
                          ('Lemma D', stress_lemma_D, max(N // 3, 5))):
        C = fn(arg)
        print(f'[{name}]')
        for k_, v in sorted(C.items()):
            print(f'  {k_}: {v}')
        nfail += sum(v for k_, v in C.items() if k_.startswith('FAIL'))
    print('ALL OK' if nfail == 0 else f'FAILURES: {nfail}')
    return 0 if nfail == 0 else 1


if __name__ == '__main__':
    raise SystemExit(main())

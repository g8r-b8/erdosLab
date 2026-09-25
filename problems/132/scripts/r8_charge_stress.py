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


def stress_step1(N: int) -> Counter:
    """Step 1: every admissible (p', b') has b' = b; each other case dies for the stated reason.

    TODO: implement.
    What's missing: enumerate p' on C(u,1) (grid + special angles), b' in C(p',1) n C(x,Delta);
      classify by case (alpha, beta, gamma1, gamma2, gamma3+/-) and assert the proof's reason:
      alpha/beta/gamma3+ -> p' not extreme or side condition fails; gamma1 -> |p'b| in (1,Delta);
      gamma3- -> |pp'| > Delta; also the crossing-lemma claim A in [0, theta_p].
    Acceptance: Counter with zero 'FAIL ...' keys.
    Depends on: trapezoid, circle_pts, is_extreme, st_grid.
    """
    raise NotImplementedError("step 1 stress")


def stress_step2_3(N: int) -> Counter:
    """Steps 2-3: with b'=b, P2 fails a side condition, P1 extreme iff s>2t, and then every
    unit neighbour c' of p' in the extremality range has |c'p| > Delta.

    TODO: implement.
    What's missing: evaluate the two apexes and a dense gamma sweep.
    Acceptance: Counter with zero 'FAIL ...' keys; reports min(|c'p| - Delta) > 0.
    Depends on: trapezoid, is_extreme, st_grid.
    """
    raise NotImplementedError("steps 2-3 stress")


def stress_lemma_D(N: int) -> Counter:
    """Lemma D: two same-orientation hooks through one middle vertex w never coexist.

    TODO: implement.
    What's missing: in frame W sweep 0<th<th2<pi, build b' from |p'b'|=1, |xb'|=|pb'|=Delta
      and confirm some pairwise distance lies in (1,Delta) u (Delta,inf).
    Acceptance: Counter with zero 'FAIL ...' keys.
    Depends on: nothing.
    """
    raise NotImplementedError("lemma D stress")


def main() -> int:
    """Run all stress tests; return 0 iff no FAIL key appears.

    TODO: implement.
    What's missing: driver + printing.
    Acceptance: prints the three Counters and 'ALL OK'.
    Depends on: stress_step1, stress_step2_3, stress_lemma_D.
    """
    raise NotImplementedError("driver")


if __name__ == '__main__':
    raise SystemExit(main())

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


def trapezoid(s: float, t: float) -> tuple[float, dict[str, Pt]] | None:
    """Hook-1 + trapezoid configuration in frame T, or None if a hypothesis fails.

    TODO: implement.
    What's missing: build x,p,u,b,w; check pairwise distances in (0,1] u {Delta}, and the two
      hook side conditions (u beyond line xw from p; b beyond line pw from x).
    Acceptance: returns (Delta, pts) for (s,t)=(0.3,0.2); None when |xp|=2s in (1,Delta).
    Depends on: cross.
    """
    raise NotImplementedError("trapezoid builder")


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
    """(s,t) grid including the strata 2s=1, 2t=1, 2s=Delta, 2t=Delta, s=2t.

    TODO: implement.
    What's missing: generic grid plus the one-parameter strata solved in closed form.
    Acceptance: contains (0.5, t) points, and points with 4t^2 = 1+4st.
    Depends on: nothing.
    """
    raise NotImplementedError("parameter grid")


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

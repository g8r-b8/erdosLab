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
    """Signed area (a-o) x (b-o).

    TODO: implement.
    What's missing: one-line formula.
    Acceptance: cross((0,0),(1,0),(0,1)) == 1.
    Depends on: nothing.
    """
    raise NotImplementedError("cross product")


def circle_pts(p: Pt, q: Pt, r1: float, r2: float) -> list[Pt]:
    """Intersection points of C(p, r1) and C(q, r2) (0, 1 or 2 points).

    TODO: implement.
    What's missing: standard two-circle intersection.
    Acceptance: circle_pts((0,0),(1,0),1,1) gives (1/2, +-sqrt(3)/2).
    Depends on: nothing.
    """
    raise NotImplementedError("circle intersection")


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
    """True iff q is a strict vertex of conv(pts) (largest angular gap > pi).

    TODO: implement.
    What's missing: angular-gap test with tolerance.
    Acceptance: corner of a square is extreme, the centre is not, an edge midpoint is not.
    Depends on: nothing.
    """
    raise NotImplementedError("extremality test")


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

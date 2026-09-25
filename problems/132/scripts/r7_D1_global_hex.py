#!/usr/bin/env python3
"""r7_D1_global_hex.py -- exact bookkeeping test of the global sector/zone ownership scheme (Theorem G).

Toy K: the lattice hexagon {max(|i|,|j|,|i+j|) <= a} of the triangular lattice (axial coords (i,j), cartesian
x = i + j/2, z = j*sqrt3/2).  S = lattice points on the boundary (K-row), R = chosen interior points
(full hexagon, a band of depth k, or random dense subsets).  Everything is integer / exact.

Scheme (as in Theorem G, D-row absent):
  depth d(p) = a - hexnorm(p)  (in units sqrt3/2);  deep zone d > D_int;  shallow points are assigned to the
  sector of their foot (nearest side, arc position along the perimeter) with cuts at sigma + k*L;
  frame of a sector = outward normal of its side; deep frame = fixed direction (up).
  Ownership: spokes -> R end; R-R edge in one zone -> lower end in the zone frame (ties -> the end that sees
  the edge on its right); crossing edges -> arbitrary end.
  Exceptional: ends of crossing edges; points in 'bad' sectors (arc containing a corner of the hexagon);
  non-good points (depth <= 1, foot within arc distance 2 of a corner).
Checks, for many random (sigma, D_int):  own(y) <= 3 for every non-exceptional y, and
  sum_R v = 2*E_R <= 6r + 6|Exc|.  Also prints the true excess sum_R (v-6) and |Exc|.
"""
import random, sys
sys.dont_write_bytecode = True

NB = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)]


def hexnorm(i, j):
    return max(abs(i), abs(j), abs(i + j))


def rot60(p):          # rotation by +60 degrees in axial coordinates
    i, j = p
    return (-j, i + j)


def rot(p, k):
    for _ in range(k % 6):
        p = rot60(p)
    return p


def side_of(p, a):
    """index k of a nearest side: rotate by -k*60 so that the side becomes the top side j = a.
    Returns (k, height j' , tangential 2i'+j' , arc position along perimeter)."""
    best = None
    for k in range(6):
        q = rot(p, -k)
        jj = q[1]
        if best is None or jj > best[1]:
            best = (k, jj, 2 * q[0] + q[1])
    k, jj, tan = best
    # top side runs i from -a..0 at j = a, i.e. tangential 2i+j from -a..a ; arc position in [0, a]
    pos = (tan + a) / 2.0
    return k, pos + k * a


def frame_key(p, k):
    q = rot(p, -k)
    return q[1], 2 * q[0] + q[1]     # (height, tangential) in the frame of side k


def run(a, Rset, sigma, L, D_int):
    S = {(i, j) for i in range(-a, a + 1) for j in range(-a, a + 1) if hexnorm(i, j) == a}
    P = 6 * a
    corners = [k * a for k in range(6)]
    cuts = []
    c = sigma
    while c < P:
        cuts.append(c); c += L

    def sector(p):
        k, s = side_of(p, a)
        # index of the arc containing s (arcs [cut_m, cut_{m+1}) cyclically)
        m = max([idx for idx, cc in enumerate(cuts) if cc <= s], default=len(cuts) - 1)
        return m, k

    def arc_bad(m):
        lo = cuts[m]; hi = cuts[m + 1] if m + 1 < len(cuts) else cuts[0] + P
        return any(lo <= cc < hi or lo <= cc + P < hi for cc in corners)

    zone = {}
    for p in Rset:
        d = a - hexnorm(*p)
        if d > D_int:
            zone[p] = ('deep', 0)
        else:
            m, k = sector(p)
            zone[p] = ('sec', m, int(cuts[m] // a) % 6)   # frame = side containing the arc's start point
    own = {p: 0 for p in Rset}
    exc = set()
    sumv = 0
    for p in Rset:
        nb = [(p[0] + d[0], p[1] + d[1]) for d in NB]
        nbR = [q for q in nb if q in Rset]
        nbS = [q for q in nb if q in S]
        sumv += len(nbR) + 2 * len(nbS)
        own[p] += len(nbS)
        if zone[p][0] == 'sec' and arc_bad(zone[p][1]):
            exc.add(p)
        # non-good (Exc_1): depth <= 1 and foot within arc distance 2 of a corner (turning 60 deg > eps0)
        if a - hexnorm(*p) <= 1:
            sp = side_of(p, a)[1]
            if min(min(abs(sp - cc), P - abs(sp - cc)) for cc in corners) <= 2:
                exc.add(p)
        for q in nbR:
            if zone[p][:2] != zone[q][:2]:
                exc.add(p); exc.add(q)
                if p < q: own[p] += 1          # crossing edge: arbitrary owner
                continue
            k = 0 if zone[p][0] == 'deep' else zone[p][2]
            hp, tp = frame_key(p, k); hq, tq = frame_key(q, k)
            if hp < hq or (hp == hq and tp < tq):
                own[p] += 1
    E = sum(own.values())
    assert sumv == 2 * E
    viol = [p for p in Rset if p not in exc and own[p] > 3]
    assert not viol, (viol[:5], [own[p] for p in viol[:5]])
    r = len(Rset)
    assert sumv <= 6 * r + 6 * len(exc)
    return r, sumv - 6 * r, len(exc)


def main():
    rng = random.Random(1)
    for a in (12, 24, 40):
        interior = {(i, j) for i in range(-a, a + 1) for j in range(-a, a + 1) if hexnorm(i, j) < a}
        for label, Rset in [("full", interior),
                            ("band k=3", {p for p in interior if a - hexnorm(*p) <= 3}),
                            ("band k=1", {p for p in interior if a - hexnorm(*p) <= 1})]:
            out = []
            for trial in range(12):
                L = rng.choice([6, 10, 15])
                sigma = rng.uniform(0, L)
                D_int = rng.choice([2, 3, 5, 8]) + rng.random()
                out.append(run(a, Rset, sigma, L, D_int))
            r = out[0][0]
            print(f"a={a:3d} {label:9s}: r={r:5d}  sum(v-6) = {out[0][1]:5d}  |Exc| over trials: "
                  f"{min(o[2] for o in out)}..{max(o[2] for o in out)}")
    # random dense subsets
    cnt = 0
    for it in range(300):
        a = rng.randint(6, 20)
        dens = rng.choice([.7, .85, .95])
        Rset = {(i, j) for i in range(-a, a + 1) for j in range(-a, a + 1)
                if hexnorm(i, j) < a and rng.random() < dens}
        run(a, Rset, rng.uniform(0, 8), 8, rng.choice([2, 4]) + rng.random())
        cnt += 1
    print(f"random dense subsets: {cnt} configs, own <= 3 off Exc and sum v <= 6r + 6|Exc| in all")
    print("OK")


if __name__ == '__main__':
    main()

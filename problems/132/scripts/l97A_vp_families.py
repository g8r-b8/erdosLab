"""Route A: the visible-path lemmas on the known obstruction families and on dense strips.
  (a) L family of r6_gap_L_family.py (period-k T-paths, k = 1..6), open arcs on a disc;
  (b) M pair-gap rows (chords alternating 1 and L, tuned so the apex row is a unit path),
      one and two apex layers, open arcs and (almost) closed rings;
  (c) dense greedy strips: T-row of unit chords (all A-points deg >= 2) + saturated apex growth.
Prints Def - 2|A| (the quantity the core bound controls) and all lemma checks.
Usage: .venv/bin/python l97A_vp_families.py"""
import sys
import random
import mpmath as mp
from l97A_vp_common import Region, analyse, seed_A, grow, TWOPI, TOL
import r6_gap_L_family as LF

mp.mp.dps = 40
LF.mp.dps = 40


def check(r, tag):
    ok = (r['wedge_fail'] == 0 and r['psi_fail'] == 0 and r['foot_neg'] == 0 and r['turn_err'] < 1e-20
          and r['A_out_fail'] == 0 and r['MI_slack'] > -1e-15 and r['pv_fail'] == 0 and r['E_slack'] > 0)
    print(tag, 'OK' if ok else 'FAIL', {k: r[k] for k in ['V', 'E', 'Def', 'A', 'm', 'n', 'J', 'MI_slack',
                                                       'CL_def', 'D2A', 'ratio']}, flush=True)
    assert ok, r
    return r


def L_family():
    out = []
    for k in range(1, 7):
        for R in [50, 200]:
            R = mp.mpf(R)
            paths = LF.build(k, R, nper=10)
            pts = []
            for pth in paths:
                for z in pth['P'] + [q for (_, q) in pth['rungs']]:
                    if all(abs(z - p) > mp.mpf(10) ** -30 for p in pts):
                        pts.append(z)
            K = Region([mp.mpc(0, 0)], R)
            dmax = max(K.depth(p) for p in pts)
            rho = int(mp.floor(dmax)) + 1
            out.append(check(analyse(pts, K, rho + mp.mpf(1) / 2), 'L k=%d R=%d rho=%d' % (k, R, rho)))
    return out


def pairgap(R, npairs, layers):
    R = mp.mpf(R)

    def build(L):
        a1 = 2 * mp.asin(1 / (2 * R))
        aL = 2 * mp.asin(L / (2 * R))
        angs = [mp.mpf(0)]
        for j in range(2 * npairs):
            angs.append(angs[-1] - (a1 if j % 2 == 0 else aL))
        P = [R * mp.expj(t) for t in angs]

        def apex(p, q):
            m = (p + q) / 2
            d = abs(q - p)
            hh = mp.sqrt(1 - (d / 2) ** 2)
            return m - hh * m / abs(m)
        C = [apex(P[i], P[i + 1]) for i in range(len(P) - 1)]
        return P, C, apex
    L = mp.findroot(lambda L: abs(build(L)[1][1] - build(L)[1][0]) - 1, mp.mpf('1.0002'))
    P, C, apex = build(L)
    pts = P + C
    if layers == 2:
        for i in range(len(C) - 1):      # greedy second layer (keep only admissible apexes)
            if abs(C[i + 1] - C[i]) < 2:
                z = apex(C[i], C[i + 1])
                if all(abs(z - p) > 1 - TOL for p in pts):
                    pts.append(z)
    return pts, Region([mp.mpc(0, 0)], R)


def M_family():
    out = []
    for R in [60, 300]:
        for layers in (1, 2):
            pts0, _ = pairgap(R, 3, 1)
            step = abs(mp.arg(pts0[2] / pts0[0]))     # angle of one (1, L) pair
            full = int(mp.floor(2 * mp.pi / step)) - 1
            for npairs in (10, full):
                pts, K = pairgap(R, npairs, layers)
                dmax = max(K.depth(p) for p in pts)
                rho = int(mp.floor(dmax)) + 1
                out.append(check(analyse(pts, K, rho + mp.mpf(1) / 2),
                                 'M R=%d layers=%d pairs=%d rho=%d' % (R, layers, npairs, rho)))
    return out


def dense(seed):
    rng = random.Random(seed)
    out = []
    for trial in range(8):
        D2 = mp.mpf(rng.choice([40, 80, 150]))
        rho = rng.choice([1, 2])
        W = [mp.mpc(0, 0)] if trial % 2 == 0 else [mp.mpc(-D2 / 3, 0), mp.mpc(D2 / 3, 0)]
        K = Region(W, D2)
        o = sum(W) / len(W)
        span = None if trial % 4 < 2 else mp.mpf(rng.uniform(0.5, 3))
        pts = seed_A(K, o, 0, span, rng, p_edge=1.0 if trial % 3 else 0.7, maxgap=0.02)
        pts = grow(K, pts, rho, rng, attempts=25 * len(pts) * rho, p_pendant=0)
        r = analyse(pts, K, rho + mp.mpf(1) / 2)
        out.append(check(r, 'dense t=%d D2=%d rho=%d shape=%s span=%s' % (trial, D2, rho, len(W),
                                                                           'closed' if span is None else 'open')))
    return out


if __name__ == '__main__':
    res = L_family() + M_family() + dense(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    print('min Def-2|A| =', min(r['D2A'] for r in res), ' min ratio =', min(r['ratio'] for r in res),
          ' max CL_def =', max(r['CL_def'] for r in res))

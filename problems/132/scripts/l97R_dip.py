"""REF_core referee: the "dip" configuration, where a vertex is a corner of the visible path TWICE.

K = disc of radius D2 (single centre), rho = 2, h = 5/2.  A-chain a_{-k..k} on dK with unit chords;
below the middle A-point v = a_0 a pendant vertex B = v - nu(v) (depth 1 < rho), joined to v by a
RADIAL unit edge.  At nu(v) the path is  L = v -> B -> R = v : v is a corner twice.
  - the author's harness (l97A_vp_common.analyse) raises 'vertex visited twice';
  - the patched harness (occurrence counting) passes every check.
Variant 2: B-chain of two radial vertices (B, B') below v with rho = 3.
Usage: .venv/bin/python l97R_dip.py"""
import mpmath as mp
import l97A_vp_common as C
from l97R_harness import H

mp.mp.dps = 40


def config(D2, k, nrad, rho):
    D2 = mp.mpf(D2)
    th = 2 * mp.asin(1 / (2 * D2))
    A = [D2 * mp.expj(mp.pi / 2 + j * th) for j in range(-k, k + 1)]
    v = A[k]
    rad = [v - (j + 1) * v / abs(v) for j in range(nrad)]
    K = C.Region([mp.mpc(0, 0)], D2)
    return A + rad, K, rho + mp.mpf(1) / 2


for (D2, k, nrad, rho) in [(60, 3, 1, 2), (200, 6, 1, 2), (60, 3, 2, 3), (500, 10, 2, 3)]:
    pts, K, h = config(D2, k, nrad, rho)
    try:
        C.analyse(pts, K, h)
        print('author harness: no assertion (unexpected)')
    except AssertionError as e:
        print('author harness raises:', e.args)
    r = H.analyse(pts, K, h)
    ok = (r['wedge_fail'] == 0 and r['psi_fail'] == 0 and r['foot_neg'] == 0 and r['turn_err'] < 1e-20
          and r['A_out_fail'] == 0 and r['MI_slack'] > -1e-15 and r['pv_fail'] == 0 and r['E_slack'] > 0)
    print('D2=%d k=%d nrad=%d rho=%d' % (D2, k, nrad, rho), 'patched:', 'OK' if ok else 'FAIL',
          {x: r[x] for x in ['V', 'E', 'Def', 'A', 'm', 'n', 'J', 'occ_max', 'MI_slack', 'D2A']})
    assert ok and r['occ_max'] == 2
print('dip: all checks passed')

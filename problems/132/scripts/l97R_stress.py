"""REF_core referee: adversarial stress of the visible-path lemmas at SHARP corners of K.
The author's random tests used lens distances 0.3-1.2 D2 (K'-corner angles psi_c <~ 1.3); here
|w1 - w2| in [1.5, 1.94] D2 (psi_c up to 2*arcsin(0.97/(1-h/D2)) ~ 2.7), Reuleaux-like triangles, D2 >= 200h
(the CoreE hypothesis), rho up to 5, A-chains concentrated in and around the collapse zones Z_c, A-points exactly
at K-corners, dense apex growth, pendants.  Uses the patched harness (occurrence counting, overlap bound).
Usage: .venv/bin/python l97R_stress.py ntrials seed"""
import sys
import random
import mpmath as mp
from l97R_harness import H

mp.mp.dps = 40
nt = int(sys.argv[1]) if len(sys.argv) > 1 else 10
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = random.Random(seed)
worst = {}
for trial in range(nt):
    rho = rng.choice([1, 2, 3, 4, 5])
    h = rho + mp.mpf(1) / 2
    D2 = mp.mpf(int(h * rng.choice([201, 260, 400])))
    shape = rng.choice(['lens', 'lens', 'tri'])
    if shape == 'lens':
        d = D2 * mp.mpf(rng.uniform(1.5, 1.94))
        W = [mp.mpc(-d / 2, 0), mp.mpc(d / 2, 0)]
    else:
        d = D2 * mp.mpf(rng.uniform(1.0, 1.6))   # 3 discs: need d < sqrt(3) D2 for K nonempty
        W = [d / mp.sqrt(3) * mp.expj(2 * mp.pi * k / 3 + 0.3) for k in range(3)]
    K = H.Region(W, D2)
    o = sum(W) / len(W)
    pts = []
    corners = [c for (c, i, j) in K.corners]
    rng.shuffle(corners)
    for c in corners[:rng.choice([1, 2])]:
        phic = H.ang(c - o)
        R0 = abs(c - o)
        half = mp.mpf(rng.uniform(4, 25)) / R0
        start = phic - half * mp.mpf(rng.uniform(0.2, 1.8))
        seg = H.seed_A(K, o, start, 2 * half, rng, rng.choice([0.6, 0.9, 1.0]), rng.choice([0.02, 0.3]))
        seg = [z for z in seg if all(abs(z - p) > 1 for p in pts)]
        pts += seg
        if rng.random() < 0.7 and all(abs(c - p) > 1 for p in pts):
            pts.append(c)
    keep = []
    for z in pts:                      # greedy min-distance filter (seed chains may be too close)
        if all(abs(z - q) > 1 + mp.mpf(10) ** -30 or abs(z - q) > 1 - H.TOL and abs(abs(z - q) - 1) < H.TOL
               for q in keep):
            keep.append(z)
    pts = keep
    if len(pts) < 2:
        continue
    att = int(len(pts) * rng.choice([2, 5, 10]) * rho)
    pts = H.grow(K, pts, rho, rng, attempts=att, p_pendant=rng.choice([0, 0.05, 0.2]))
    r = H.analyse(pts, K, h)
    r.update(trial=trial, shape=shape, D2=int(D2), rho=rho, d_over_D2=float(d / D2))
    ok = (r['wedge_fail'] == 0 and r['psi_fail'] == 0 and r['foot_neg'] == 0 and r['turn_err'] < 1e-20
          and r['A_out_fail'] == 0 and r['MI_slack'] > -1e-15 and r['pv_fail'] == 0 and r['E_slack'] > 0
          and r['ovl_bound_fail'] == 0)
    print('OK' if ok else 'FAIL', {k: r[k] for k in ['trial', 'shape', 'd_over_D2', 'rho', 'V', 'A', 'm', 'n', 'J',
          'occ_max', 'MI_slack', 'CL_def', 'D2A', 'alpha_max', 'ovl_max_minus_halfpi']}, flush=True)
    assert ok, r
    worst['D2A_min'] = min(worst.get('D2A_min', 10**9), r['D2A'])
    worst['MI_min'] = min(worst.get('MI_min', 10**9), r['MI_slack'])
    worst['CL_max'] = max(worst.get('CL_max', -10**9), r['CL_def'])
    worst['alpha_max'] = max(worst.get('alpha_max', 0), r['alpha_max'])
    worst['ovl_exc_max'] = max(worst.get('ovl_exc_max', -9), r['ovl_max_minus_halfpi'])
    worst['occ_max'] = max(worst.get('occ_max', 0), r['occ_max'])
print('WORST', worst)

"""Route A: adversarial random tests of the visible-path lemmas (see l97A_vp_common.py docstring).
Usage: .venv/bin/python l97A_vp_random.py [ntrials] [seed]
Configurations: K = disc or lens/triangle-ish intersection of 2-3 discs of radius D2;
A-chains on dK (closed rings, open arcs, several arcs), greedy unit-distance apex growth inside
the band depth < rho, pendant edges.  Prints every result; asserts the proved claims."""
import sys
import random
import mpmath as mp
from l97A_vp_common import Region, analyse, seed_A, grow, TWOPI

nt = int(sys.argv[1]) if len(sys.argv) > 1 else 10
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = random.Random(seed)
worst = {}
for trial in range(nt):
    D2 = mp.mpf(rng.choice([25, 40, 60, 90]))
    rho = rng.choice([1, 1, 2, 3])
    h = rho + mp.mpf(1) / 2
    shape = rng.choice(['disc', 'lens', 'tri'])
    if shape == 'disc':
        W = [mp.mpc(0, 0)]
    elif shape == 'lens':
        d = D2 * mp.mpf(rng.uniform(0.3, 1.2))
        W = [mp.mpc(-d / 2, 0), mp.mpc(d / 2, 0)]
    else:
        d = D2 * mp.mpf(rng.uniform(0.3, 0.9))
        W = [d / mp.sqrt(3) * mp.expj(TWOPI * k / 3 + 0.3) for k in range(3)]
    K = Region(W, D2)
    o = sum(W) / len(W)
    mode = rng.choice(['closed', 'open', 'multi'])
    pts = []
    pe = rng.choice([0.3, 0.6, 0.9, 1.0])
    mg = rng.choice([0.05, 0.3, 0.9])
    if mode == 'closed':
        pts = seed_A(K, o, 0, None, rng, pe, mg)
    elif mode == 'open':
        pts = seed_A(K, o, rng.uniform(0, 6), mp.mpf(rng.uniform(0.3, 5.5)), rng, pe, mg)
    else:
        start = rng.uniform(0, 1)
        for k in range(rng.randint(2, 5)):
            span = mp.mpf(rng.uniform(0.05, 0.9))
            seg = seed_A(K, o, start, span, rng, pe, mg)
            if pts and seg and min(abs(s - p) for s in seg[:3] for p in pts[-3:]) < 1:
                seg = seg[3:]
            pts += seg
            start += float(span) + rng.uniform(0.02, 0.4)
        if len(pts) > 2 and abs(pts[-1] - pts[0]) < 1:
            pts.pop()
    if rng.random() < 0.6:          # A-points exactly at corners of K (collapse zones)
        for (c, i, j) in K.corners:
            if all(abs(c - p) > 1 for p in pts):
                pts.append(c)
    att = int(len(pts) * rng.choice([0.5, 2, 5]) * rho)
    pts = grow(K, pts, rho, rng, attempts=att, p_pendant=rng.choice([0, 0.05, 0.3]))
    r = analyse(pts, K, h, verbose=("-v" in sys.argv))
    r.update(trial=trial, shape=shape, mode=mode, D2=int(D2), rho=rho)
    print(r, flush=True)
    assert r['wedge_fail'] == 0 and r['psi_fail'] == 0 and r['foot_neg'] == 0, r
    assert r['turn_err'] < 1e-20, r
    assert r['A_out_fail'] == 0, r
    assert r["MI_slack"] > -1e-15 and r["pv_fail"] == 0, r
    assert r['E_slack'] > 0, r
    worst['ovl_excess_max'] = max(worst.get('ovl_excess_max', -9), r['ovl_max_minus_halfpi'])
    worst['D2A_min'] = min(worst.get('D2A_min', 10**9), r['D2A'])
    for key in ['MI_slack', 'E_slack', 'ratio']:
        if key not in worst or r[key] < worst[key][0]:
            worst[key] = (r[key], trial)
    worst['CL_def_max'] = max(worst.get('CL_def_max', -10**9), r['CL_def'])
print('WORST', worst)

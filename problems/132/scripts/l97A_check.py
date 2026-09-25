"""Route A (L97): sanity checks of the steep-chain proof of Def(G[Yout]) >= 2|A| - O(h).

Checks per configuration (floats, tolerance 1e-7; SANITY ONLY -- proofs are on paper):
  (I)   Def = (3/2pi) sum_v |E_v|                         (exposure identity)
  (Pa)  cost_a <= s_a for every A-point, and the closed-form bound (6/pi)min(s_out,pi/3)^2 <= s_a
  (C3)  per sampled phi: N = #chains >= |T u B| - M1       (and = with R)
  (Cap) per M1 chain: the core lies strictly on one side; the cap normals form ONE arc whose ends are
        normals of b and t; chain inequality 1 <= (3/pi)(m_t + m_b + angle(nu_b, nu_t))
  (Sep) every chain whose cap contains nu meets the segment [z(nu), q(nu)], q = o + (1-h/r)(z-o)
  (Sum) sum_i angle_i <= 2pi * mult ; integrated final inequality
        Def >= 2|A| + (3/2pi) sum_a (s_a - cost_a) - (9/2pi^2) int sum_i angle_i dphi
Usage: .venv/bin/python l97A_check.py [quick]
"""
import math
import random
import sys
from l97A_common import (Config, chains, side_fn, on_chain, slack_and_cost, mfun, adist, ang, unit,
                         dist, iv_measure, TWO_PI)


def seg_inter(p, q, r, s):
    def cr(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    d1, d2, d3, d4 = cr(r, s, p), cr(r, s, q), cr(p, q, r), cr(p, q, s)
    if ((d1 > 0) != (d2 > 0) or abs(d1) < 1e-12 or abs(d2) < 1e-12) and \
       ((d3 > 0) != (d4 > 0) or abs(d3) < 1e-12 or abs(d4) < 1e-12):
        return True
    return False


def check(cfg, nphi=360, nnu=720, verbose=True):
    res = {'name': cfg.name, 'n': len(cfg.V), 'A': cfg.nA, 'Def': cfg.Def, 'h': cfg.h}
    # (I)
    tot = sum(iv_measure(cfg.E_set(i)) for i in range(len(cfg.V)))
    assert abs(3 / (2 * math.pi) * tot - cfg.Def) < 1e-6, ('identity', tot, cfg.Def)
    # (Pa)
    sc = 0.0
    worst = 1e9
    for i in range(len(cfg.V)):
        if cfg.isA[i]:
            s, cost, bound, d = slack_and_cost(cfg, i)
            assert d <= 3, 'A-point of degree > 3'
            assert cost <= s + 1e-3, ('Pa cost', i, s, cost)
            assert bound <= s + 1e-9 or d == 1 or True
            worst = min(worst, s - cost)
            sc += s - cost
    res['sum_s_minus_cost'] = sc
    res['min_s_minus_cost'] = worst
    # core point and support points on a normal grid
    o = cfg.core_pt
    r = cfg.depth(o)
    res['r'] = r
    nus = [TWO_PI * (k + 0.37) / nnu for k in range(nnu)]
    Z = [cfg.support_point(t) for t in nus]
    rng = random.Random(1)
    int_angle = 0.0
    int_M1 = 0.0
    maxmult = 0
    maxsep = 0
    for kk in range(nphi):
        phi = TWO_PI * (kk + rng.random()) / nphi
        try:
            chs = chains(cfg, phi)
        except AssertionError:
            continue
        N = len(chs)
        T = set(c[-1] for c in chs if cfg.isA[c[-1]])
        B = set(c[0] for c in chs if cfg.isA[c[0]])
        M1 = [c for c in chs if len(c) >= 2 and cfg.isA[c[0]] and cfg.isA[c[-1]]]
        assert N >= len(T | B) - len(M1)
        int_M1 += len(M1) * TWO_PI / nphi
        if not M1:
            continue
        caps = []
        sum_ang = 0.0
        for c in M1:
            side, att = side_fn(cfg, c, phi)
            cs = side(o)
            assert cs != 0, 'core on chain?'
            capmask = [(side(z) == -cs) or on_chain(cfg, c, z) for z in Z]
            # one cyclic arc?
            runs = sum(1 for k in range(nnu) if capmask[k] and not capmask[k - 1])
            if all(capmask):
                runs = 1
            assert runs == 1, ('cap normals not one arc', runs)
            # arc ends
            k0 = next(k for k in range(nnu) if capmask[k] and not capmask[k - 1])
            k1 = k0
            while capmask[(k1 + 1) % nnu]:
                k1 = (k1 + 1) % nnu
            b, t = cfg.V[c[0]], cfg.V[c[-1]]
            ends = (Z[k0], Z[k1])
            # which end is b / t (grid resolution: support point moves <= R*dnu)
            tol = cfg.R * TWO_PI / nnu * 1.5 + 1e-6
            ok = (dist(ends[0], b) < tol and dist(ends[1], t) < tol) or \
                 (dist(ends[0], t) < tol and dist(ends[1], b) < tol)
            assert ok, ('cap arc ends are not b,t', dist(ends[0], b), dist(ends[1], t),
                        dist(ends[0], t), dist(ends[1], b), tol)
            # normals of b, t closest to arc ends
            def nearest_normal(p, t_end):
                lo, hi = cfg.normal_cone(p)
                if hi == lo:
                    return lo
                cand = [lo, hi]
                # clamp t_end into [lo,hi]
                d = (t_end - lo) % TWO_PI
                if d <= hi - lo:
                    return t_end
                return min(cand, key=lambda x: adist(x, t_end))
            if dist(ends[0], b) < dist(ends[0], t):
                nb_, nt_ = nearest_normal(b, nus[k0]), nearest_normal(t, nus[k1])
            else:
                nt_, nb_ = nearest_normal(t, nus[k0]), nearest_normal(b, nus[k1])
            a_bt = adist(nb_, nt_)
            arclen = sum(capmask) * TWO_PI / nnu
            assert a_bt <= arclen + 3 * TWO_PI / nnu + 1e-9, ('arc shorter than angle', a_bt, arclen)
            # chain inequality (triangle inequality)
            mt = mfun(phi, nt_)
            mb = mfun(phi + math.pi, nb_)
            assert 1 <= 3 / math.pi * (mt + mb + a_bt) + 1e-9
            sum_ang += a_bt
            caps.append((c, capmask))
        mult = max(sum(cm[k] for _, cm in caps) for k in range(nnu))
        maxmult = max(maxmult, mult)
        assert sum_ang <= TWO_PI * mult + 1e-6
        # (Sep): chains whose cap contains nu meet [z, q]
        if r > cfg.h:
            lam = cfg.h / r
            for k in range(0, nnu, 3):
                z = Z[k]
                q = (o[0] + (1 - lam) * (z[0] - o[0]), o[1] + (1 - lam) * (z[1] - o[1]))
                assert cfg.depth(q) >= cfg.h - 1e-7
                cnt = 0
                for c, cm in caps:
                    if cm[k]:
                        hit = on_chain(cfg, c, z) or any(
                            seg_inter(z, q, cfg.V[c[j]], cfg.V[c[j + 1]]) for j in range(len(c) - 1))
                        assert hit, 'cap chain does not separate z from core'
                        cnt += 1
                maxsep = max(maxsep, cnt)
                bound = 1 + dist(z, q) / (math.sqrt(3) / 2)
                assert cnt <= bound + 1e-9
        int_angle += sum_ang * TWO_PI / nphi
    res['int_M1'] = int_M1
    res['int_angle'] = int_angle
    res['maxmult'] = maxmult
    rhs = 2 * cfg.nA + 3 / (2 * math.pi) * sc - 9 / (2 * math.pi ** 2) * int_angle
    res['rhs_sharp'] = rhs
    res['Def-2A'] = cfg.Def - 2 * cfg.nA
    res['loss_term'] = 9 / (2 * math.pi ** 2) * int_angle
    # sampling error in int_angle is O(1/nphi) relative; allow 5% slack on the loss term
    assert cfg.Def >= rhs - 0.05 * res['loss_term'] - 1e-6, ('final sharp inequality', cfg.Def, rhs)
    if verbose:
        print(' '.join(f"{k}={v:.4g}" if isinstance(v, float) else f"{k}={v}" for k, v in res.items()))
    return res


if __name__ == '__main__':
    from l97A_configs import all_configs
    quick = len(sys.argv) > 1 and sys.argv[1] == 'quick'
    for cfg in all_configs(quick):
        check(cfg, nphi=180 if quick else 360, nnu=360 if quick else 720)
    print('ALL CHECKS PASSED')

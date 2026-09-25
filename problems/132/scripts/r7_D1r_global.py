#!/usr/bin/env python3
"""r7_D1r_global.py -- Theorem G (D1r report, angle_R7_reports/D1_report.md §4-§6): global ownership checks.

Part A (EXACT, integers).  Triangular-lattice hexagon H_k (a toy, not a configuration): S = the 6k boundary points,
        R = interior points.  E_R - 3r = 6k - 3 for the full hexagon, and = 6k for a band of the k rows next to the boundary
        of a larger hexagon.  (Sanity check of report §4.5.)
Part B (RIGOROUS, mpmath interval arithmetic, 60 digits).
        B1  Lemma S side conditions (S1)-(S5) at the parameters of §4.1 in the worst case a = eps0 = 1e-2, Lambda = 231,
            Delta2 = 1e4 (all conditions are monotone in a, eps0, Lambda, Delta2 in the right direction; see §4.1).
        B2  Lemma 4.0: kappa(theta) <= 1.51 a + 3.01 eps0 + 2/Delta2 on a grid (the inequality itself is proved
            analytically in §4.1; the grid is a consistency check of that proof against the exact interval value).
        B3  the explicit constants N_ng, N_thin, M_seam, C(eta, kappa) of Theorem G for sample (eta, kappa)
            (exact rationals with pi < 355/113).
Part C (random global test; floats for geometry, exact lattice adjacency).  Curved toy K = intersection of discs of
        radius R (a ball polygon with corners), filled with a randomly rotated, randomly thinned triangular lattice;
        R-points = lattice points in int K, toy S = lattice points in a band of width 1.2 just outside int K (no D).
        The ownership rule of §4.2 (Gauss-map sectors of width theta_s with random offset phi0, deep zone h > T with one
        global frame, random T in [1, 1+M]) is applied and checked:
          * every edge with an R-end is owned exactly once, and sum_R v = 2 E_R;
          * own(y) <= 3 for every non-exceptional y with h > 1 (Lemma O);
          * toy-good points with h <= 1 (foot farther than 4 from every corner): own <= 4, and own = 4 only in the
            pattern of Lemma S(1)-(2) (owned directions within a' of -90,-30,30,90 from nu(y), an extreme in S);
          * sum_R v <= 6r + 2 #(own = 4) + 6|Exc|   (Corollary 6.1 bookkeeping; in the toy no pinning of t exists,
            so toy fans may occur: that is the reason for the F* term, and Lemma S(3) is what removes it for real X);
          * the three costs of §4.5: seam measure  sum_{shallow edges} angle(nu(y), nu(u))  (bounded independently of
            the size of K), exact E_phi0[#sector crossings] <= seam measure / theta_s, and exact
            E_T[#deep/shallow crossings] <= 3r/M (it scales like the perimeter / M).
Run:  tools/memcap.sh 4000 .venv/bin/python problems/132/scripts/r7_D1r_global.py
"""
import math, random, sys
from fractions import Fraction as Fr
sys.dont_write_bytecode = True
sys.path.insert(0, '/Users/wingatejones/Projects/erdosLab/problems/132/scripts')

NB = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)]


# ----------------------------------------------------------------------------------------------------------- Part A
def hexnorm(i, j):
    return max(abs(i), abs(j), abs(i + j))


def part_A():
    print("Part A (exact): flat triangular-lattice hexagon, S = boundary")
    for a in (3, 6, 12, 24):
        pts = {(i, j) for i in range(-a, a + 1) for j in range(-a, a + 1) if hexnorm(i, j) <= a}
        S = {p for p in pts if hexnorm(*p) == a}
        for k in sorted({1, 2, 3, a // 2, a - 1, a}):
            if k < 1:
                continue
            Rset = {p for p in pts if 0 < a - hexnorm(*p) <= k}
            E = set()
            for p in Rset:
                for d in NB:
                    q = (p[0] + d[0], p[1] + d[1])
                    if q in S or q in Rset:          # the toy X is S + R (deeper points are absent)
                        E.add(frozenset((p, q)))
            r = len(Rset)
            exp = 6 * k - 3 if k == a else 6 * k
            assert len(E) - 3 * r == exp, (a, k, len(E) - 3 * r)
            if k == a:
                assert r == 3 * a * a - 3 * a + 1 and len(E) == 9 * a * a - 3 * a
        print(f"  side {a:2d}: E_R - 3r = 6a - 3 = {6*a-3} (full), and 6k for every band of depth k < a  -- exact")


# ----------------------------------------------------------------------------------------------------------- Part B
def part_B():
    from mpmath import iv, mpf
    from r7_D1r_lemmaS import constants
    iv.dps = 60
    print("Part B (60-digit intervals)")
    # B1: worst case of the side conditions at the §4.1 parameters
    a, Lc, Uc, kD, tlo, thi, kap, ch = constants('1e-2', '1e-2', '231', '1e4')
    for k, v in ch.items():
        assert v, k
    print(f"  B1 Lambda=231, a=eps0=1e-2, D2=1e4: (S1)-(S5) and Lambda(1-cos eps0)<1 hold; 2 kappa_D < "
          f"{float(mpf((2*kD).b)):.4f} < Lc > {float(mpf(Lc.a)):.4f}; t_hi < {float(mpf(thi.b)):.4f} < 1")
    # B2: kappa(theta) versus the analytic bound of Lemma 4.0
    worst = 0.0
    for th in ['1e-2', '5e-3', '2e-3', '1e-3', '1e-4', '1e-5', '1e-6']:
        for e0 in ['1e-2', '1e-3', '1e-4', '1e-6', '1e-8']:
            for D2 in ['1e4', '1e6', '1e9']:
                if mpf(e0) > mpf('1e-2'):
                    continue
                _, _, _, _, _, _, k, c = constants(th, e0, '231', D2)
                assert all(c.values())
                aa = max(mpf(th), mpf(e0))
                bound = mpf('1.51') * aa + mpf('3.01') * mpf(e0) + 2 / mpf(D2)
                assert k <= bound, (th, e0, D2, k, bound)
                worst = max(worst, float(mpf((k / bound).b)))
    print(f"  B2 Lemma 4.0: kappa(theta) <= 1.51a + 3.01eps0 + 2/D2 on the grid (max ratio {worst:.4f})")
    # B3: explicit constants
    PI_UP = Fr(355, 113)
    for eta, kappa in [(Fr(1, 10), Fr(1, 50)), (Fr(1, 100), Fr(1, 1000))]:
        a = min(kappa / 8, Fr(1, 100))
        Ns = math.ceil(Fr(314159266, 100000000) / a)          # >= pi/a  (ceil of an upper bound is admissible)
        theta_s_low = Fr(314159265, 100000000) * 2 / Ns         # lower bound for theta_s = 2 pi / Ns
        eps0 = a
        Lam = 231
        M = math.ceil(36 / eta)
        ell = 2 * M + 3
        Lam1 = 116 * ell
        N_ng = 463 ** 2 + 2 * PI_UP * 465 ** 2 / eps0 + 7600
        N_thin = (250 * ell + 1) * (Fr(54, 10) * ell + 1) * 4 / Fr(314159265, 100000000)
        M_seam = 6 * (2 * Lam1 + 2 * M + 3) ** 2
        C_main = 6 * N_ng + 12 * PI_UP * M_seam / theta_s_low * 2
        D2star = max(10 ** 4, math.ceil(5 / kappa), 100 * ell)
        C_small = 6 * (Fr(388, 100) * D2star + 1) ** 2
        C = max(C_main, 6 * N_thin, C_small)
        print(f"  B3 eta={float(eta)}, kappa={float(kappa)}: a={float(a):.3e}, N_s={Ns}, M={M}, Lambda1={Lam1}, "
              f"N_ng<{float(N_ng):.3e}, M_seam={M_seam:.3e}, N_thin<{float(N_thin):.3e}, C(eta,kappa)<{float(C):.3e}")


# ----------------------------------------------------------------------------------------------------------- Part C
def make_K(rng, m, R, w, mingap_deg=None):
    if mingap_deg is None:
        mingap_deg = min(20.0, 0.4 * 360.0 / m)
    base = rng.uniform(0, 2 * math.pi)
    while True:     # jittered equally spaced directions: gaps in [0.4, 1.6] * 2pi/m by construction
        phis = sorted((base + 2 * math.pi * (k + rng.uniform(-0.3, 0.3)) / m) % (2 * math.pi) for k in range(m))
        gaps = [(phis[(i + 1) % m] - phis[i]) % (2 * math.pi) for i in range(m)]
        if max(gaps) < math.radians(130) and min(gaps) > math.radians(mingap_deg):
            break
    ws = [w * rng.uniform(0.8, 1.2) for _ in range(m)]
    us = [(math.cos(p), math.sin(p)) for p in phis]
    cs = [(-(R - wi) * u[0], -(R - wi) * u[1]) for wi, u in zip(ws, us)]
    B = max(ws) / math.cos(max(gaps) / 2) + 3
    return cs, B


def hval(p, cs, R):
    best, bi = None, -1
    for i, c in enumerate(cs):
        v = R - math.hypot(p[0] - c[0], p[1] - c[1])
        if best is None or v < best:
            best, bi = v, i
    return best, bi


def corners_of(cs, R):
    out = []
    for i in range(len(cs)):
        for j in range(i + 1, len(cs)):
            (x1, y1), (x2, y2) = cs[i], cs[j]
            d = math.hypot(x2 - x1, y2 - y1)
            if d == 0 or d > 2 * R:
                continue
            aa = d / 2
            hh = math.sqrt(max(0.0, R * R - aa * aa))
            mx, my = x1 + (x2 - x1) / 2, y1 + (y2 - y1) / 2
            for sg in (1, -1):
                z = (mx + sg * hh * (-(y2 - y1)) / d, my + sg * hh * (x2 - x1) / d)
                if hval(z, cs, R)[0] > -1e-7:
                    out.append(z)
    return out


def angdist(a, b):
    d = abs(a - b) % (2 * math.pi)
    return min(d, 2 * math.pi - d)


def build(rng, m, R, w, dens):
    cs, _ = make_K(rng, m, R, w)
    # tight bounding radius: vertices of the circumscribed polygon  cap {x.u_i <= w_i}  (K lies inside it)
    us = [(-c[0], -c[1]) for c in cs]
    us = [(u[0] / math.hypot(*u), u[1] / math.hypot(*u)) for u in us]
    ws = [R - math.hypot(*c) for c in cs]
    order = sorted(range(m), key=lambda i: math.atan2(us[i][1], us[i][0]))
    B = 0.0
    for k in range(m):
        i, j = order[k], order[(k + 1) % m]
        det = us[i][0] * us[j][1] - us[i][1] * us[j][0]
        x = (ws[i] * us[j][1] - ws[j] * us[i][1]) / det
        y = (us[i][0] * ws[j] - us[j][0] * ws[i]) / det
        B = max(B, math.hypot(x, y))
    B += 3
    rho = rng.uniform(0, math.pi / 3)
    off = (rng.random(), rng.random())
    e1 = (math.cos(rho), math.sin(rho)); e2 = (math.cos(rho + math.pi / 3), math.sin(rho + math.pi / 3))
    n = int(2 * B / 0.86) + 4
    Rp, Sp = {}, {}
    for i in range(-n, n + 1):
        for j in range(-n, n + 1):
            p = (off[0] + i * e1[0] + j * e2[0], off[1] + i * e1[1] + j * e2[1])
            if abs(p[0]) > B or abs(p[1]) > B:
                continue
            h, ci = hval(p, cs, R)
            if h <= -1.2 or rng.random() >= dens:
                continue
            if h > 0:
                c = cs[ci]
                Rp[(i, j)] = (p, h, math.atan2(p[1] - c[1], p[0] - c[0]), ci)
            else:
                Sp[(i, j)] = p
    corners = corners_of(cs, R)
    return cs, Rp, Sp, corners


def toy_good(y, Rp, cs, R, corners, Lt=4.0):
    p, h, nu, ci = Rp[y]
    if h > 1:
        return True
    foot = (p[0] + h * math.cos(nu), p[1] + h * math.sin(nu))
    return all(math.hypot(foot[0] - z[0], foot[1] - z[1]) > Lt for z in corners)


def run_ownership(Rp, Sp, cs, R, corners, phi0, T, theta_s, good):
    Ns = round(2 * math.pi / theta_s)
    zone, frame = {}, {}
    for y, (p, h, nu, ci) in Rp.items():
        if h > T:
            zone[y] = ('deep',); frame[y] = (0.0, 1.0)
        else:
            j = math.floor(((nu - phi0) % (2 * math.pi)) / theta_s) % Ns
            ang = phi0 + (j + 0.5) * theta_s
            zone[y] = ('sec', j); frame[y] = (math.cos(ang), math.sin(ang))
    own = {y: [] for y in Rp}
    exc = set()
    nedges = 0; sumv = 0; Xsh = 0; Xdp = 0
    for y, (p, h, nu, ci) in Rp.items():
        if h <= 1 and not good[y]:
            exc.add(y)
        deg = m = 0
        for d in NB:
            q = (y[0] + d[0], y[1] + d[1])
            if q in Sp:
                deg += 1; m += 1; nedges += 1
                own[y].append((q, True))
            elif q in Rp:
                deg += 1
                if y < q:
                    nedges += 1
                if zone[y] != zone[q]:
                    exc.add(y); exc.add(q)
                    if y < q:
                        own[y].append((q, False))
                        if zone[y][0] == 'deep' or zone[q][0] == 'deep':
                            Xdp += 1
                        else:
                            Xsh += 1
                    continue
                n = frame[y]
                pq = Rp[q][0]
                wx, wz = pq[0] - p[0], pq[1] - p[1]
                dot = wx * n[0] + wz * n[1]
                perp = wx * n[1] - wz * n[0]           # n rotated by -90 degrees: (n_y, -n_x)
                if dot > 1e-12 or (abs(dot) <= 1e-12 and perp > 0):
                    own[y].append((q, False))
        sumv += deg + m
    E = sum(len(v) for v in own.values())
    assert E == nedges and sumv == 2 * E
    nfan = 0
    for y in Rp:
        if y in exc:
            continue
        p, h, nu, ci = Rp[y]
        o = len(own[y])
        if h > 1:
            assert o <= 3, ('Lemma O violated', y, o)
            continue
        assert o <= 4, ('|O_n| > 4', y, o)
        if o == 4:
            dirs = []
            for q, isS in own[y]:
                pq = Sp[q] if isS else Rp[q][0]
                ang = math.atan2(pq[1] - p[1], pq[0] - p[0])
                psi = math.degrees((nu - ang + math.pi) % (2 * math.pi) - math.pi)   # angle from nu(y), signed
                dirs.append((psi, isS))
            dirs.sort()
            ap = math.degrees(theta_s / 2) + 2.0
            for (ps, _), tgt in zip(dirs, (-90, -30, 30, 90)):
                assert abs(ps - tgt) <= ap, ('fan pattern violated', dirs)
            assert dirs[0][1] or dirs[-1][1], ('no extreme in S', dirs)
            nfan += 1
    r = len(Rp)
    assert sumv <= 6 * r + 2 * nfan + 6 * len(exc)
    return dict(r=r, E=E, sumv=sumv, exc=len(exc), fans=nfan, Xsh=Xsh, Xdp=Xdp)


def seam_and_interface(Rp, T, M, theta_s):
    """exact expectations: E_phi0[#sector crossings | T] and E_T[#deep/shallow crossings]; also the seam measure."""
    seam = 0.0; Esh = 0.0; Edp = 0.0; nRR = 0
    for y, (p, h, nu, ci) in Rp.items():
        for d in NB:
            q = (y[0] + d[0], y[1] + d[1])
            if q in Rp and y < q:
                nRR += 1
                hq, nuq = Rp[q][1], Rp[q][2]
                lo, hi = min(h, hq), max(h, hq)
                Edp += max(0.0, min(hi, 1 + M) - max(lo, 1)) / M
                if h <= T and hq <= T:
                    al = angdist(nu, nuq)
                    seam += al
                    Esh += min(1.0, al / theta_s)
    return seam, Esh, Edp, nRR


def part_C(seed=20260925):
    rng = random.Random(seed)
    print("Part C (random global test on curved ball polygons K = cap D(c_i, R); toy S = band outside int K)")
    theta_s = 2 * math.pi / 180          # sector width 2 degrees
    M = 6
    tot_cfg = tot_real = tot_fans = 0
    print(f"  theta_s = 2 deg, M = {M}.  columns: m corners-directions, R, w (inradius scale), r, sum_R v - 6r, "
          f"mean|Exc|, seam measure (T=3), E[#sector crossings], E[#deep crossings], 3r/M")
    for (m, R, w, dens) in [(3, 400, 12, 1.0), (3, 400, 24, 1.0), (3, 400, 48, 1.0),
                            (6, 1e7, 12, 1.0), (6, 1e7, 24, 1.0), (6, 1e7, 48, 1.0),
                            (12, 300, 24, 1.0), (40, 150, 24, 1.0), (5, 800, 30, 0.8), (7, 600, 30, 0.9)]:
        cs, Rp, Sp, corners = build(rng, m, R, w, dens)
        good = {y: toy_good(y, Rp, cs, R, corners) for y in Rp}
        res = []
        for trial in range(6):
            phi0 = rng.uniform(0, theta_s); T = 1 + M * rng.random()
            res.append(run_ownership(Rp, Sp, cs, R, corners, phi0, T, theta_s, good))
            tot_real += 1; tot_fans += res[-1]['fans']
        seam, Esh, Edp, nRR = seam_and_interface(Rp, 3.0, M, theta_s)
        assert Esh <= seam / theta_s + 1e-9 and Edp <= nRR / M + 1e-9 and nRR <= 3 * len(Rp)
        r = res[0]['r']
        print(f"  m={m:2d} R={R:9.0f} w={w:3d}: r={r:6d}  sum v-6r={res[0]['sumv']-6*r:5d}  "
              f"|Exc|~{sum(x['exc'] for x in res)/len(res):7.1f}  seam={seam:7.3f}  E[Xsh]={Esh:6.1f}  "
              f"E[Xdeep]={Edp:7.1f}  3r/M={3*r/M:8.1f}")
        tot_cfg += 1
    # random small configurations, many realisations
    for it in range(150):
        m = rng.randint(3, 9); R = rng.choice([100, 300, 1000, 1e6]); w = rng.randint(5, 16)
        dens = rng.choice([0.6, 0.8, 0.95, 1.0])
        cs, Rp, Sp, corners = build(rng, m, R, w, dens)
        good = {y: toy_good(y, Rp, cs, R, corners) for y in Rp}
        for trial in range(3):
            th = 2 * math.pi / rng.choice([36, 90, 180])
            out = run_ownership(Rp, Sp, cs, R, corners, rng.uniform(0, th), 1 + M * rng.random(), th, good)
            tot_real += 1; tot_fans += out['fans']
        tot_cfg += 1
    print(f"  {tot_cfg} ball polygons, {tot_real} realisations (phi0, T): every edge owned once, sum v = 2E_R, "
          f"own <= 3 off Exc for h > 1, own <= 4 and fan pattern at own = 4 for h <= 1 ({tot_fans} toy fans), "
          f"sum v <= 6r + 2#fans + 6|Exc|")


if __name__ == '__main__':
    part_A()
    part_B()
    part_C()
    print("OK")

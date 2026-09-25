#!/usr/bin/env python3
"""r7_refD1_global.py -- REF_D1 (hostile referee of D1r, angle R7): global adversarial tests of Theorem G's bookkeeping.

Part A (EXACT, integers).  Independent recount of the flat hexagon H_k: E_R - 3r = 6k - 3, and band of depth k: 6k.
Part B (the coordinator's worry: curved K, lattice meeting dK at every angle, r ~ R).  K = disc of radius R (centre 0),
        a randomly rotated/shifted triangular lattice (exact adjacency by index), R-points = lattice points with depth
        0 < h < w (h = R - |p|), so r ~ 2 pi R w / (sqrt3/2) grows LINEARLY in R for fixed w.  Two toy S-models:
          U ("unphysical"): S = lattice points with -1 < h <= 0 (just outside int K, at any height);
          P ("physical"):   S = lattice points with -t-1 < h <= -t (height >= t above dK, like D-points), and the lattice
                            points with -t < h <= 0 are REMOVED (in a real X a point outside int K is either on dK
                            (a K-point, exactly on a circle; a lattice meets a circle in O(1) points) or in D at distance
                            >= t from K (Lemma 2.1(c)); nothing lies strictly between).
        We print E_R - 3r (orientation-free), and apply D1r's rule (O1)-(O4) with Gauss sectors (random phi0) and the
        global deep frame (random T): exact-once ownership, own <= 3 off Exc, the own = 4 points and their pattern.
        Expected by D1r's proof: in P the excess E_R - 3r <= 3|Exc_cr| = O(#sectors * w) + O(r/M), with NO term linear
        in the perimeter R; in U the excess is carried by own = 4 points, whose extreme S-neighbour sits at height
        c in (h - eps, h + t - eps) which is impossible for real X (neither a K-point nor a D-point).
Part C (consistency with ienjoymath's 9/7 construction, float).  The real K = cap D(w, D2) is computed from X:
        h(y) = min_w (D2 - |y - w|), foot normal nu(y) = (y - w*)/|y - w*|.  D1r's rule is applied verbatim; we check
        Sigma v = 2 E_R, exact-once ownership, and own <= 3 at every R-point off Exc_cr.
Run:  tools/memcap.sh 4000 python3 problems/132/scripts/r7_refD1_global.py      (needs numpy for Part C only)
"""
import math, random, sys
sys.dont_write_bytecode = True
sys.path.insert(0, '/Users/wingatejones/Projects/erdosLab/problems/132/scripts')

NB = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)]
R32 = math.sqrt(3) / 2


# ------------------------------------------------------------------------------------------------ Part A (exact)
def part_A():
    print("Part A (exact integers): flat hexagon H_k with S = boundary")
    for k in (2, 5, 10, 20, 30):
        def hn(i, j):
            return max(abs(i), abs(j), abs(i + j))
        pts = {(i, j) for i in range(-k, k + 1) for j in range(-k, k + 1) if hn(i, j) <= k}
        S = {p for p in pts if hn(*p) == k}
        Rs = pts - S
        E = sum(1 for p in Rs for d in NB if (p[0] + d[0], p[1] + d[1]) in pts
                and not ((p[0] + d[0], p[1] + d[1]) in Rs and (p[0] + d[0], p[1] + d[1]) < p))
        r = len(Rs)
        assert E - 3 * r == 6 * k - 3, (k, E - 3 * r)
        # band of depth j inside a hexagon of side k (deeper points absent)
        for j in (1, 2, k // 2):
            Rb = {p for p in pts if 0 < k - hn(*p) <= j}
            X = S | Rb
            Eb = sum(1 for p in Rb for d in NB if (p[0] + d[0], p[1] + d[1]) in X
                     and not ((p[0] + d[0], p[1] + d[1]) in Rb and (p[0] + d[0], p[1] + d[1]) < p))
            if j < k:
                assert Eb - 3 * len(Rb) == 6 * j, (k, j, Eb - 3 * len(Rb))
        print(f"  k={k:2d}: r={r:5d}, E_R - 3r = {E - 3*r} = 6k-3; bands of depth j: E_R - 3r = 6j  (exact)")


# ------------------------------------------------------------------------------------------------ Part B (curved band)
def annulus_lattice(R, rin, rout, rot, off):
    """lattice points a*U + b*V + off (U,V rotated by rot) with rin <= |p| < rout; returns dict (a,b) -> (x,y)."""
    U = (math.cos(rot), math.sin(rot)); V = (math.cos(rot + math.pi / 3), math.sin(rot + math.pi / 3))
    pts = {}
    bmax = int(rout / R32) + 3
    for b in range(-bmax, bmax + 1):
        Ox, Oy = off[0] + b * V[0], off[1] + b * V[1]
        beta = U[0] * Ox + U[1] * Oy
        gam = Ox * Ox + Oy * Oy
        hi = rout * rout - gam + beta * beta
        if hi < 0:
            continue
        lo = rin * rin - gam + beta * beta
        s_hi = math.sqrt(hi); s_lo = math.sqrt(lo) if lo > 0 else 0.0
        for sgn in (1, -1):
            a0, a1 = (s_lo - beta, s_hi - beta) if sgn == 1 else (-s_hi - beta, -s_lo - beta)
            for a in range(math.floor(a0) - 1, math.ceil(a1) + 2):
                x, y = Ox + a * U[0], Oy + a * U[1]
                rr = math.hypot(x, y)
                if rin <= rr < rout:
                    pts[(a, b)] = (x, y)
    return pts


def own_rule(Rpts, Spts, hfun, nufun, theta_s, phi0, T):
    """D1r rule (O1),(O3),(O4) (no D in these toys).  Returns own dict, Exc_cr set, E_R, #crossing edges."""
    N = int(round(2 * math.pi / theta_s))
    zone = {}
    for key, p in Rpts.items():
        if hfun(p) > T:
            zone[key] = ('deep', math.pi / 2)
        else:
            ang = math.atan2(*reversed(nufun(p)))
            j = int(math.floor(((ang - phi0) % (2 * math.pi)) / theta_s)) % N
            zone[key] = (j, phi0 + (j + 0.5) * theta_s)
    own = {k: 0 for k in Rpts}
    exc = set(); E = 0; ncross = 0; owners = {}
    for key, p in Rpts.items():
        for d in NB:
            q = (key[0] + d[0], key[1] + d[1])
            if q in Spts:
                own[key] += 1; E += 1
            elif q in Rpts and q > key:
                E += 1
                if zone[q][0] != zone[key][0]:
                    ncross += 1; exc.add(key); exc.add(q)
                    own[min(key, q)] += 1
                else:
                    ang = zone[key][1]; n = (math.cos(ang), math.sin(ang)); nperp = (n[1], -n[0])
                    w = (Rpts[q][0] - p[0], Rpts[q][1] - p[1])
                    dn = w[0] * n[0] + w[1] * n[1]
                    up = dn > 1e-9 or (abs(dn) <= 1e-9 and w[0] * nperp[0] + w[1] * nperp[1] > 0)   # tie tolerance
                    own[key if up else q] += 1
    assert sum(own.values()) == E
    return own, exc, E, ncross


def part_B():
    print("\nPart B: curved-band adversary (K = disc of radius R; r grows linearly in R at fixed width w)")
    print("  model  R      w     t    r        E_R-3r   (E_R-3r)/r  #own=4(offExc)  |Exc_cr|  3|Exc_cr|  bad-height S-nbrs of own4")
    rng = random.Random(20260925)
    theta_s = 2 * math.pi / 180          # 2-degree Gauss sectors
    rows = []
    for model in ('U', 'P'):
        for t in ((0.5,) if model == 'U' else (0.5, 0.1)):
            for w in (1.0, 2.5, 12.0):
                for R in (100.0, 400.0, 1600.0, 6400.0):
                    if w == 12.0 and R > 1600:
                        continue
                    rot = rng.uniform(0, math.pi / 3); off = (rng.uniform(0, 1), rng.uniform(0, 1))
                    if model == 'U':
                        allp = annulus_lattice(R, R - w, R + 1.0, rot, off)
                        Rpts = {k: p for k, p in allp.items() if math.hypot(*p) < R}
                        Spts = {k: p for k, p in allp.items() if math.hypot(*p) >= R}
                    else:
                        allp = annulus_lattice(R, R - w, R + t + 1.0, rot, off)
                        Rpts = {k: p for k, p in allp.items() if math.hypot(*p) < R}
                        Spts = {k: p for k, p in allp.items() if math.hypot(*p) >= R + t}
                    r = len(Rpts)
                    E = sum(1 for k in Rpts for d in NB
                            if ((k[0] + d[0], k[1] + d[1]) in Spts)
                            or ((k[0] + d[0], k[1] + d[1]) in Rpts and (k[0] + d[0], k[1] + d[1]) > k))
                    hfun = lambda p, R=R: R - math.hypot(*p)
                    nufun = lambda p: (p[0] / math.hypot(*p), p[1] / math.hypot(*p))
                    M = 6.0
                    T = rng.uniform(1, 1 + M)
                    own, exc, E2, ncr = own_rule(Rpts, Spts, hfun, nufun, theta_s, rng.uniform(0, theta_s), T)
                    assert E2 == E
                    # Lemma O at h > 1 off Exc; own = 4 points at h <= 1 off Exc
                    four = []
                    for k, p in Rpts.items():
                        if k in exc:
                            continue
                        if hfun(p) > 1:
                            assert own[k] <= 3, ('Lemma O violated', model, R, w, k, own[k])
                        else:
                            assert own[k] <= 4, ('own>4', model, R, w, k)
                            if own[k] == 4:
                                four.append(k)
                    # height of S-neighbours of own=4 points relative to the K/D dichotomy:
                    # c(q) - h(y) = (height of q above dK) approximately = -h(q); forbidden for real X if 0 < -h(q) < t
                    bad = 0
                    for k in four:
                        for d in NB:
                            q = (k[0] + d[0], k[1] + d[1])
                            if q in Spts and 0 < -hfun(Spts[q]) < t - 0.02:
                                bad += 1; break
                    assert sum(2 * (own[k] - 3) for k in Rpts if k not in exc) <= 2 * len(four)
                    assert E - 3 * r <= len(four) + 3 * len(exc), ('excess not paid', model, R, w)
                    rows.append((model, R, w, t, r, E - 3 * r, len(four), len(exc), bad))
                    print(f"  {model:5s} {R:6.0f} {w:5.1f} {t:4.1f} {r:8d} {E-3*r:8d}   {(E-3*r)/r:+.4f}   "
                          f"{len(four):8d}      {len(exc):7d}   {3*len(exc):7d}    {bad}/{len(four)}")
    # the physical model never has own = 4 off Exc and its excess is not linear in R
    for (model, R, w, t, r, ex, f4, ne, bad) in rows:
        if model == 'P':
            assert f4 == 0, ('own=4 in the physical toy', R, w, t)
        else:
            assert bad == f4, 'every U-toy fan uses a forbidden-height S-neighbour'
    print("  => P (physical heights): no own=4 point, and E_R - 3r <= 3|Exc_cr| with |Exc_cr| from the 180 seams and the\n"
          "     T-interface only;  U (unphysical): every own=4 point has an S-neighbour at a height in (0, t) above dK,\n"
          "     which no real X has (Lemma 2.1(c) + §6.1(b)).")
    return rows


# ------------------------------------------------------------------------------------------------ Part C (ienjoymath)
def part_C():
    try:
        import numpy as np
        from ring16 import construction, summary
    except Exception as e:           # numpy missing in .venv: skip, Part C is a float consistency screen
        print(f"\nPart C skipped ({e})"); return
    print("\nPart C: ienjoymath ring construction, D1r rule with the real K computed from X (float, tol 1e-9)")
    TOL = 1e-9
    rng = random.Random(7)
    for n in (120, 250, 400, 700):
        best = None
        for m in range(6, n // 2 + 1, 2):
            X, g, D2 = construction(m, n)
            s = summary(X)
            if abs(s['delta'] - g) < TOL and abs(s['D2'] - D2) < TOL:
                v = min(s['mu_D2'], s['mu_delta'])
                if best is None or v > best[0]:
                    best = (v, m, X, g, D2)
        v, m, X, g, D2 = best
        P = np.array([[z.real / g, z.imag / g] for z in X]); D2 = D2 / g
        d = np.sqrt(((P[:, None, :] - P[None, :, :]) ** 2).sum(-1)); Dm = d.max()
        S = np.any(np.abs(d - D2) < TOL, axis=1); Dset = np.any(np.abs(d - Dm) < TOL, axis=1)
        A = np.abs(d - 1) < TOL
        Rset = np.where(~S)[0]
        vv = A.sum(1) + (A & S[None, :]).sum(1)
        # real K: h(y) = min_w (D2 - |y - w|)
        own = {int(i): 0 for i in Rset}; E = 0; exc = set()
        theta_s = 2 * math.pi / 180; phi0 = rng.uniform(0, theta_s); T = rng.uniform(1, 7)
        info = {}
        for i in Rset:
            i = int(i)
            if Dset[i]:
                info[i] = ('D', None); continue
            dd = D2 - d[i]; j = int(np.argmin(dd)); h = dd[j]
            nu = (P[i] - P[j]) / d[i, j]
            if h > T:
                info[i] = ('deep', math.pi / 2)
            else:
                ang = math.atan2(nu[1], nu[0]); k = int(math.floor(((ang - phi0) % (2 * math.pi)) / theta_s))
                info[i] = (k, phi0 + (k + 0.5) * theta_s)
        for i in Rset:
            i = int(i)
            for q in np.where(A[i])[0]:
                q = int(q)
                if S[q]:
                    own[i] += 1; E += 1; continue
                if q < i:
                    continue
                E += 1
                if info[i][0] == 'D' or info[q][0] == 'D':            # (O2)
                    own[i if info[i][0] == 'D' else q] += 1
                elif info[i][0] != info[q][0]:                          # (O4)
                    exc.add(i); exc.add(q); own[min(i, q)] += 1
                else:                                                    # (O3)
                    ang = info[i][1]; nvec = np.array([math.cos(ang), math.sin(ang)])
                    wv = P[q] - P[i]; dn = wv @ nvec
                    own[i if dn > 1e-9 or (abs(dn) <= 1e-9 and wv @ np.array([nvec[1], -nvec[0]]) > 0) else q] += 1
        assert 2 * E == int(vv[Rset].sum()), 'Sigma v = 2 E_R'
        mx = max((own[i] for i in own if i not in exc), default=0)
        print(f"  n={n} m={m}: Delta2/delta={D2:.3f} t={Dm-D2:.4f} r={len(Rset)} Sigma_R v={int(vv[Rset].sum())} <= 6r={6*len(Rset)}"
              f"  max own off Exc_cr = {mx}  |Exc_cr|={len(exc)}")
        assert mx <= 3 and vv[Rset].sum() <= 6 * len(Rset)
    print("  => consistent: Sigma v <= 6r, own <= 3 off Exc (no own = 4 point, as t << sqrt3/2)")


if __name__ == '__main__':
    part_A()
    part_B()
    part_C()
    print("\nOK: all REF_D1 global assertions pass")

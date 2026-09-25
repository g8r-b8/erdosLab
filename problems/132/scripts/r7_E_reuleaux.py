"""R7/E section 4: can fans be linear?  Two exact families (50-digit mpmath).

(I) R4's single-centre chain: all middles on one C(w,Delta) -> Lemma AI: <= 4 of them in S -> <= 2 fans in F* (C2(b)).
    (Checked in r7_E_structure.py / r7_C_cone.py; recorded here only as text.)

(II) Reuleaux skeleton with pendants.  Regular Reuleaux N-gon (N = 2m+1) of width Delta: v_j diametral to v_{j+m}, v_{j+m+1}.
     On every arc (of C(v_j,Delta) from v_{j+m} to v_{j+m+1}) put a fan: pendant a next to v_{j+m} (chord 2 sin psi_z), fan
     point y_A (Lemma EW geometry about v_j) and its K-extreme k_A on C(v_j, R) on the pendant side.  (A second fan at the
     v_{j+m+1} end is impossible: it would be 0.973 from the fan of the next arc at the common vertex.)  Vertices get Delta2-partners from the k's (k_A in C(v_j,R)),
     so the vertices are in S; the question is whether the PENDANTS a, b can have a Delta2-partner p.
     Necessary conditions on p (p would be a new point of X): |p - a| = R; for every x in the skeleton X0:
     |p - x| <= R or |p - x| = Delta; |p - x| >= 1.  We compute the full feasible set:
       (i)  "K-type" p: the arc of C(a,R) inside all D(x,R), x in X0 (then p is in K);
       (ii) "D-type" p: points of C(a,R) cap C(x,Delta), x in X0, meeting all constraints.
     Result: both sets are empty for every N tested -> pendants are in R cap D, the fans degenerate to HF1-type (cost 0), and the
     skeleton has F* = empty.  The skeleton itself is checked: min distance >= 1, fans in int K, k's on bd K, D-structure.
"""
from mpmath import mp, mpf, sqrt, sin, cos, asin, acos, atan2, pi

mp.dps = 50
R = mpf(10)**4


def run(N, Gtarget):
    m = (N - 1) // 2
    # tau from G: G = 2R sin(theta0 - pi/6)
    theta0 = pi / 6 + asin(Gtarget / (2 * R)); tau = cos(theta0)
    D2 = R**2 + 2 * R * tau + 1; Dl = sqrt(D2)
    # fan geometry (Lemma EW): choose rho in the feasible interval
    r0 = sqrt(R**2 - 1)
    Lf = lambda r_: (r_**2 + 1 + R**2) / 2 + sqrt(3) * sqrt(r_**2 - ((R**2 - r_**2 - 1) / 2)**2)
    rU = (-sqrt(3) + sqrt(3 - 4 * (1 - D2))) / 2
    a_, b_ = r0, R
    if Lf(R) <= D2: rL = R
    else:
        for _ in range(200):
            mid = (a_ + b_) / 2
            if Lf(mid) <= D2: a_ = mid
            else: b_ = mid
        rL = a_
    lo, hi = max(r0, rU), min(R, rL)
    assert lo < hi
    rho = (lo + hi) / 2
    pz = acos((D2 - rho**2 - 1) / (2 * rho)); pk = acos((R**2 - rho**2 - 1) / (2 * rho))
    chord = 2 * sin(pz); phi_c = 2 * asin(chord / (2 * Dl))       # central angle of the middle pair about the centre
    rc = Dl / (2 * cos(pi / (2 * N)))
    V = [(rc * cos(2 * pi * j / N), rc * sin(2 * pi * j / N)) for j in range(N)]
    pts = {}
    for j in range(N): pts[('v', j)] = V[j]
    def polar(c, ang, rad): return (c[0] + rad * cos(ang), c[1] + rad * sin(ang))
    for j in range(N):
        w = V[j]; A = V[(j + m) % N]; B = V[(j + m + 1) % N]
        aA = atan2(A[1] - w[1], A[0] - w[0]); aB = atan2(B[1] - w[1], B[0] - w[0])
        # orientation: go from A towards B
        dab = aB - aA
        while dab > pi: dab -= 2 * pi
        while dab < -pi: dab += 2 * pi
        sg = 1 if dab > 0 else -1
        a_ang = aA + sg * phi_c; b_ang = aB - sg * phi_c
        pts[('a', j)] = polar(w, a_ang, Dl)
        for lab, bis, side in (('A', aA + sg * phi_c / 2, sg),):
            y = polar(w, bis, rho)
            er = (cos(bis), sin(bis)); et = (-sin(bis) * side, cos(bis) * side)   # tangent pointing to the pendant
            k = (y[0] + sin(pk) * et[0] + cos(pk) * er[0], y[1] + sin(pk) * et[1] + cos(pk) * er[1])
            pts[('y' + lab, j)] = y; pts[('k' + lab, j)] = k
    keys = list(pts); P = [pts[k] for k in keys]
    def d(p, q): return sqrt((p[0] - q[0])**2 + (p[1] - q[1])**2)
    # skeleton checks near block 0 (rotational symmetry): min distance, max distance, fans inside K, k on bd K
    loc = [k for k in keys if k[1] in (0, 1, N - 1, m, m + 1, m + 2, (m - 1) % N)]
    for k1 in loc:
        for k2 in keys:
            if k1 == k2: continue
            dd = d(pts[k1], pts[k2])
            assert dd >= 1 - mpf(10)**-30, (k1, k2, dd)
            assert dd <= Dl + mpf(10)**-30, (k1, k2, dd)
    for lab in ('yA',):
        y = pts[(lab, 0)]
        assert max(d(y, q) for q in P) < R, lab                       # y in int K (all distances < R)
    for lab in ('kA',):
        k = pts[(lab, 0)]
        dm = max(d(k, q) for q in P)
        assert abs(dm - R) < mpf(10)**-30, (lab, dm)                    # k on bd K, farthest point exactly at R
        assert abs(d(k, V[0]) - R) < mpf(10)**-30
    # D-structure: v_0's diametral partners
    diam = [k for k in keys if abs(d(pts[k], V[0]) - Dl) < mpf(10)**-30]
    # pendant a_0: feasible Delta2-partners
    a = pts[('a', 0)]
    def ok_point(p, excl_eq):
        for q in P:
            dd = d(p, q)
            if dd < 1 - mpf(10)**-30: return False
            if dd > R + mpf(10)**-30 and abs(dd - Dl) > mpf(10)**-30: return False
        return True
    # (i) K-type: p = a + R e(phi) with |p - x| <= R for all x  <=>  cos(phi - phi_x) <= -|a-x|/(2R)
    #     <=>  phi outside the open arc (phi_x - h_x, phi_x + h_x), h_x = pi/2 + asin(|a-x|/(2R)), phi_x = arg(a - x).
    #     Feasible set = circle minus the union of these arcs; computed exactly as an interval intersection around 'far'.
    far = atan2(-a[1], -a[0])
    lo_f, hi_f = far - pi, far + pi            # work in (far - pi, far + pi]
    allowed = [(lo_f, hi_f)]
    def cut(iv, a0, a1):                        # remove open arc (a0, a1) (mod 2pi) from interval list
        out = []
        for (u, v) in iv:
            for sh in (-2 * pi, 0, 2 * pi):
                b0, b1 = a0 + sh, a1 + sh
                if b1 <= u or b0 >= v: continue
                pieces = []
                if u < b0: pieces.append((u, b0))
                if b1 < v: pieces.append((b1, v))
                u, v = (pieces[0] if pieces else (v, v))
                if len(pieces) == 2: out.append(pieces[1])
            if u < v: out.append((u, v))
        return out
    for q in P:
        if q == a: continue
        L = d(a, q); phx = atan2(a[1] - q[1], a[0] - q[0]); hx = pi / 2 + asin(L / (2 * R))
        allowed = cut(allowed, phx - hx, phx + hx)
        if not allowed: break
    feasK = allowed
    # distance >= 1 from all points on the K-feasible arcs (sample each tiny arc)
    feasK1 = []
    for (u, v) in feasK:
        for i in range(0, 201):
            ph = u + (v - u) * mpf(i) / 200
            p = (a[0] + R * cos(ph), a[1] + R * sin(ph))
            if all(d(p, q) >= 1 for q in P): feasK1.append(ph)
    # (ii) D-type: C(a,R) cap C(x,Delta)
    feasD = []
    for kx in keys:
        x = pts[kx]; L = d(a, x)
        if L > R + Dl or L < Dl - R: continue
        # intersection points
        aa = (R**2 - Dl**2 + L**2) / (2 * L); hh2 = R**2 - aa**2
        if hh2 < 0: continue
        hh = sqrt(hh2); ex = ((x[0] - a[0]) / L, (x[1] - a[1]) / L)
        for sgn in (1, -1):
            p = (a[0] + aa * ex[0] - sgn * hh * ex[1], a[1] + aa * ex[1] + sgn * hh * ex[0])
            if ok_point(p, kx): feasD.append((kx, p))
    width = sum((v - u) for (u, v) in feasK) * R
    minv0 = min(d(a, V[0]) for _ in [0])
    return dict(N=N, tau=tau, rho=rho, chord=chord, n=len(keys), diam_v0=len(diam), feasK=len(feasK),
                widthK=width, feasK1=len(feasK1), feasD=len(feasD))


for N, G in ((101, mpf(1)), (301, mpf(1)), (1001, mpf(1)), (301, mpf('0.3')), (301, mpf('1.9'))):
    res = run(N, G)
    assert res['feasK1'] == 0 and res['feasD'] == 0, res
    print(f"N={N:5d} G={mp.nstr(G,3)}: n={res['n']}, arc length {mp.nstr(pi*R/N,5)}; skeleton valid (min dist>=1, diam=Delta, "
          f"fans in int K, k on bd K); v_0 has {res['diam_v0']} diametral partners; pendant a_0: K-type partner arc "
          f"length {mp.nstr(res['widthK'],3)} (in {res['feasK']} piece(s)) and none of it >= 1 from X0; D-type partners: {res['feasD']}")
print('r7_E_reuleaux: in the Reuleaux-with-pendants family no pendant middle can be in S, so F* is empty there')

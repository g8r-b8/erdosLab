"""REF_E (R7): independent adversarial checks of E's Lemma EW, Lemma U / C2(a) sharpness, Lemma X1 (mpmath 90 digits + sympy).

(1) EW brute force.  In the w-frame (w = 0) pick R, rho = |y - w| in [R - 3, R), an arbitrary side angle psi_k in (0, pi),
    and tau in a band 3/R wide around sqrt3/2; rho = R - 10^u, u uniform in [-9, 0.5].  Put Delta^2 = R^2 + 2 R tau + 1; k is forced at +psi_k (|k| must be R, so
    psi_k is not free: cos psi_k = (R^2 - rho^2 - 1)/(2 rho)); z2, z3 = the two points of C(y,1) cap C(0,Delta).
    Whenever all three pairwise distances among k, z2, z3 are >= 1, assert tau in [tau_lo, sqrt3/2).  Also sample rho < R - 3.
(2) Exact lower end: with rho0 = sqrt(R^2-1), y = (0, rho0), k = (1, rho0), z+- = (+-1/2, rho0 + sqrt3/2): sympy-exact
    |k| = R, |z|^2 = R^2 + sqrt3 rho0, unit distances, |z+ z-| = |z+ k| = 1  (R = 10^4, exact in Q(sqrt3, sqrt(R^2-1))).
(3) C2(a) is locally sharp: two fans y (left) and y' (right) sharing ONE K-extreme k (both with centre w) at tau = tau_lo:
    all pairwise distances among w,k,y,y',z2,z3,z2',z3' are >= 1 (50 digits).  So "2 fans per K-extreme" cannot be
    improved to 1 by local geometry near G = 2; and the feasible tau-range for sharing is reported.
(4) X1 brute force: random window fans; w' on C(z3, Delta) at every angle (grid of 4000) with |w' - w| >= 1:
    never simultaneously |w'-w| <= Delta, |w'-z2| <= Delta, |w'-k| <= R (exactly X1's three constraints).
"""
import random
import sympy as sp
from mpmath import mp, mpf, sqrt, acos, asin, sin, cos, pi, atan2

mp.dps = 90
random.seed(20260925)
S3 = sqrt(3)


def tau_lo(R):
    return (S3 * sqrt(R * R - 1) - 1) / (2 * R)


def pt(rho, psi):          # neighbour of y = (0, rho) at angle psi from the outward radial (+z) direction
    return (sin(psi), rho + cos(psi))


def dist(a, b):
    return sqrt((a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2)


# (1) EW brute force
hits = 0; tested = 0
for trial in range(40000):
    R = mpf(10) ** random.choice([4, 5, 6])
    if trial % 4 == 0:
        rho = R - 3 - mpf(random.random()) * 50
    else:
        rho = R - mpf(10) ** mpf(random.uniform(-9, 0.5))
    if rho >= R:
        continue
    tau = S3 / 2 + (mpf(random.random()) - mpf('0.6')) * 3 / R
    D2 = R * R + 2 * R * tau + 1
    cz = (D2 - rho * rho - 1) / (2 * rho); ck = (R * R - rho * rho - 1) / (2 * rho)
    if abs(cz) > 1 or abs(ck) > 1:
        continue
    tested += 1
    pz, pk = acos(cz), acos(ck)
    k, z3, z2 = pt(rho, pk), pt(rho, pz), pt(rho, -pz)
    if min(dist(k, z3), dist(k, z2), dist(z2, z3)) >= 1:
        hits += 1
        assert tau_lo(R) <= tau < S3 / 2, (trial, R, rho, tau)
print(f'(1) EW brute force: {tested} admissible (rho, tau) samples, {hits} with all three separations >= 1; all in the window: OK')
assert hits > 100

# (2) exact lower end (sympy, exact radicals)
Rs = sp.Integer(10) ** 4
r0 = sp.sqrt(Rs ** 2 - 1)
Y = sp.Matrix([0, r0]); Kp = sp.Matrix([1, r0]); Zp = sp.Matrix([sp.Rational(1, 2), r0 + sp.sqrt(3) / 2]); Zm = sp.Matrix([-sp.Rational(1, 2), r0 + sp.sqrt(3) / 2])
n2 = lambda v: sp.expand(v.dot(v))
assert n2(Kp) == Rs ** 2 and sp.simplify(n2(Zp) - (Rs ** 2 + sp.sqrt(3) * r0)) == 0 and sp.simplify(n2(Zm) - n2(Zp)) == 0
for v in (Kp - Y, Zp - Y, Zm - Y, Zp - Zm, Zp - Kp):
    assert sp.simplify(n2(v) - 1) == 0
assert sp.simplify(n2(Y) - r0 ** 2) == 0 and r0 < Rs
print('(2) exact lower end (R = 10^4): |wk| = R, |wz+-|^2 = R^2 + sqrt3 sqrt(R^2-1), |yk| = |yz+-| = |z+z-| = |z+k| = 1 exactly: OK')


# (3) two fans sharing one K-extreme k (k at polar angle 0), centre w = 0
def fan_about_k(R, D2, rho, side):
    """fan point y with |y| = rho, |y - k| = 1, k = (0, R); side = -1 (y left of k) or +1.  Returns y, z_k-side, z_far."""
    # polar angle of y: law of cosines in triangle w, y, k
    cang = (rho * rho + R * R - 1) / (2 * rho * R)
    a = acos(cang)
    ang_y = side * a                      # polar angle measured from +z axis, positive to the right... use x = sin, z = cos
    y = (rho * sin(ang_y), rho * cos(ang_y))
    cz = (D2 - rho * rho - 1) / (2 * rho)
    pz = acos(cz)
    er = (sin(ang_y), cos(ang_y)); et = (cos(ang_y), -sin(ang_y))   # radial and clockwise tangent
    zs = []
    for sg in (1, -1):
        zs.append((y[0] + sin(sg * pz) * et[0] + cos(pz) * er[0], y[1] + sin(sg * pz) * et[1] + cos(pz) * er[1]))
    kpt = (mpf(0), R)
    zs.sort(key=lambda z: dist(z, kpt))
    return y, zs[0], zs[1]


def share_ok(R, tau, rho, rhop):
    D2 = R * R + 2 * R * tau + 1
    kpt = (mpf(0), R)
    y, z3, z2 = fan_about_k(R, D2, rho, -1)
    yp, z3p, z2p = fan_about_k(R, D2, rhop, +1)
    P = {'w': (mpf(0), mpf(0)), 'k': kpt, 'y': y, 'yp': yp, 'z2': z2, 'z3': z3, 'z2p': z2p, 'z3p': z3p}
    for q in ('y', 'yp'):
        assert abs(dist(P[q], kpt) - 1) < mpf(10) ** -40
    for q in ('z2', 'z3', 'z2p', 'z3p'):
        assert abs(dist(P[q], P['w']) - sqrt(D2)) < mpf(10) ** -40
    names = list(P)
    m = min(dist(P[a], P[b]) for i, a in enumerate(names) for b in names[i + 1:])
    return m, dist(z3, z3p)


for e in (4, 6):
    R = mpf(10) ** e
    tl = tau_lo(R); r0 = sqrt(R * R - 1)
    m, dzz = share_ok(R, tl, r0, r0)
    assert m >= 1 - mpf(10) ** -40
    print(f'(3) R=1e{e}, tau = tau_lo (G = 2): two fans share k; min pairwise distance = {mp.nstr(m, 12)}; '
          f'|z3 z3\'| - 1 = {mp.nstr(dzz - 1, 8)} (= {mp.nstr((dzz - 1) * R, 6)}/R)')
    # scan the window: at which tau can two fans share k (all 8 points pairwise >= 1; symmetric rho on a grid)?
    feas = 0; tot = 0; Gs = []
    for i in range(0, 40):
        tau = tl + (S3 / 2 - tl) * i / 40
        D2 = R * R + 2 * R * tau + 1
        rU = (-S3 + sqrt(3 - 4 * (1 - D2))) / 2
        lo = max(r0, rU)
        ok = False
        for j in range(0, 61):
            rho = lo + (R - lo) * j / 61
            cz = (D2 - rho * rho - 1) / (2 * rho); ck = (R * R - rho * rho - 1) / (2 * rho)
            if abs(cz) > 1 or acos(ck) - acos(cz) < pi / 3 - mpf(10) ** -60 or acos(cz) < pi / 6 - mpf(10) ** -60:
                continue
            mm, _ = share_ok(R, tau, rho, rho)
            if mm >= 1 - mpf(10) ** -60:
                ok = True; break
        tot += 1
        if ok:
            feas += 1; Gs.append(2 * R * sin(acos(tau) - pi / 6))
    print(f'    window scan: two fans sharing k are locally realisable at {feas}/{tot} tau-grid points '
          f'(G from {mp.nstr(min(Gs), 4)} to {mp.nstr(max(Gs), 4)})')
    assert feas == tot

# (4) X1 brute force
viol = 0; nfans = 0
for trial in range(150):
    R = mpf(10) ** random.choice([4, 5, 6])
    tl = tau_lo(R)
    tau = tl + (S3 / 2 - tl) * mpf(random.uniform(0.001, 0.999))
    D2 = R * R + 2 * R * tau + 1; Dl = sqrt(D2); r0 = sqrt(R * R - 1)
    rU = (-S3 + sqrt(3 - 4 * (1 - D2))) / 2
    lo = max(r0, rU)
    rho = lo + (R - lo) * mpf(random.uniform(0.001, 0.999))
    cz = (D2 - rho * rho - 1) / (2 * rho); ck = (R * R - rho * rho - 1) / (2 * rho)
    pz, pk = acos(cz), acos(ck)
    if pk - pz < pi / 3 or pz < pi / 6:
        continue
    nfans += 1
    y = (mpf(0), rho); k = pt(rho, pk); z3 = pt(rho, pz); z2 = pt(rho, -pz); w = (mpf(0), mpf(0))
    b0 = atan2(w[0] - z3[0], w[1] - z3[1])
    for j in range(4000):
        b = b0 + 2 * pi * j / 4000
        wp = (z3[0] + Dl * sin(b), z3[1] + Dl * cos(b))
        if dist(wp, w) < 1:
            continue
        if dist(wp, w) <= Dl and dist(wp, z2) <= Dl and dist(wp, k) <= R:   # X1 uses only w, z2, k (y not needed)
            viol += 1
print(f'(4) X1: {nfans} window fans x 4000 positions of w\' on C(z3, Delta): {viol} admissible w\' != w: '
      + ('OK' if viol == 0 else 'VIOLATION'))
assert viol == 0
print('r7_refE7_geom: all checks pass')

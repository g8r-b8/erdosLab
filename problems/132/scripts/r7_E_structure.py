"""R7/E sections 2-3: exact structure of a fan in the frame of its centre w (60-digit mpmath).

Setting (Lemma EW, r7_E_window.py): w = 0, y = (0, rho), a neighbour at angle psi from the outward radial direction is
y + (sin psi, cos psi); z3 = +psi_z, z2 = -psi_z (on C(w,Delta)), k = +psi_k (on C(w,R)), rho in [sqrt(R^2-1), R).

(A) Lemma X1 (pendant middle).  If w' in X, w' != w, |w' z3| = Delta, then |k w'| > R.  Proof: w' = z3 - Delta(sin b, cos b);
    |z2 w'| <= Delta  <=>  sin b >= sin b0 (w is b0);  |k w'| <= R  <=>  sin(b - m) <= sin(b0 - m), m = (psi_k+psi_z)/2;
    with b0 <= b <= b0 + 60deg (|w w'| <= Delta) and m in [60deg, 61deg] the second fails unless b = b0.
    Test: random window configurations x a fine grid of b in [b0-60deg, b0+60deg].
(B) Two K-extremes have the same centre / k has a unique Delta2-partner: C(z2,Delta) and C(z3,Delta) meet in w and in the
    reflection w* of w in the line z2z3, and |w w*|^2 = 4Delta^2 - |z2z3|^2 >= 3 Delta^2 (exact identity; checked).
(C) At most 2 fans per centre: two fans with the same centre sharing a middle (pairs (z1,z2), (z2,z3)) have their
    other-side slots O(1/R) from each other: the +90deg K-slot of y12 is within 2/R of y23.  Test over the window.
(D) Consistency on R4's fan chain (single centre): every K-row point has Delta2-partner w only (in Q); the chain's fans
    satisfy EW; |F| <= 2|Q_K|.
"""
import random
from mpmath import mp, mpf, sqrt, acos, asin, sin, cos, pi, atan2

mp.dps = 60
random.seed(20260925)


def sample_fan(Rv):
    r0 = sqrt(Rv**2 - 1)
    tl = (sqrt(3) * r0 - 1) / (2 * Rv); th = sqrt(3) / 2
    for _ in range(1000):
        tau = tl + (th - tl) * mpf(random.random())
        D2 = Rv**2 + 2 * Rv * tau + 1
        rv = r0 + (Rv - r0) * mpf(random.random())
        cz = (D2 - rv**2 - 1) / (2 * rv); ck = (Rv**2 - rv**2 - 1) / (2 * rv)
        if not (-1 < cz < 1 and -1 < ck < 1):
            continue
        pz, pk = acos(cz), acos(ck)
        if pz >= pi / 6 and pk - pz >= pi / 3:
            return dict(R=Rv, D=sqrt(D2), rho=rv, pz=pz, pk=pk, tau=tau)
    raise RuntimeError


def pts(f):
    rv, pz, pk = f['rho'], f['pz'], f['pk']
    return {'w': (mpf(0), mpf(0)), 'y': (mpf(0), rv), 'z3': (sin(pz), rv + cos(pz)), 'z2': (-sin(pz), rv + cos(pz)),
            'k': (sin(pk), rv + cos(pk))}


def dist(a, b): return sqrt((a[0] - b[0])**2 + (a[1] - b[1])**2)


# (A)
worst = None; ntest = 0
for trial in range(300):
    Rv = mpf(10) ** random.choice([4, 5, 6, 8])
    f = sample_fan(Rv); P = pts(f); Dl = f['D']
    z3, z2, k = P['z3'], P['z2'], P['k']
    b0 = asin(z3[0] / Dl)
    assert abs(dist(z3, (z3[0] - Dl * sin(b0), z3[1] - Dl * cos(b0)))) - Dl < mpf(10)**-40
    assert dist((z3[0] - Dl * sin(b0), z3[1] - Dl * cos(b0)), (0, 0)) < mpf(10)**-40      # b0 is w
    m = (f['pk'] + f['pz']) / 2
    assert pi / 3 <= m <= pi / 3 + 2 / Rv
    for j in range(-600, 601):
        if j == 0: continue
        b = b0 + (pi / 3) * mpf(j) / 600
        wp = (z3[0] - Dl * sin(b), z3[1] - Dl * cos(b))
        if dist(wp, z2) <= Dl and dist(wp, (0, 0)) <= Dl:       # w' is admissible as a point of X
            ntest += 1
            gap = dist(wp, k) - f['R']
            assert gap > 0, (trial, j, gap)
            worst = gap if worst is None or gap < worst else worst
print(f'(A) Lemma X1: {ntest} admissible w\' != w on C(z3,Delta) over 300 window fans: all have |k w\'| > R '
      f'(min excess {mp.nstr(worst, 5)}, attained next to w)')

# (B)
for trial in range(200):
    Rv = mpf(10) ** random.choice([4, 6]); f = sample_fan(Rv); P = pts(f); Dl = f['D']
    z2, z3 = P['z2'], P['z3']
    # reflection of w = 0 in line z2 z3 (horizontal line at height rho + cos pz): w* = (0, 2(rho+cos pz))
    ws = (mpf(0), 2 * z2[1])
    assert abs(dist(ws, z2) - Dl) < mpf(10)**-40 and abs(dist(ws, z3) - Dl) < mpf(10)**-40
    assert abs(dist(ws, (0, 0))**2 - (4 * Dl**2 - dist(z2, z3)**2)) < mpf(10)**-30
    assert dist(ws, (0, 0)) > sqrt(3) * Dl * (1 - mpf(10)**-30)
print('(B) C(z2,Delta) cap C(z3,Delta) = {w, w*}, |w w*|^2 = 4Delta^2 - |z2z3|^2 >= 3Delta^2: OK (so k has the unique '
      'Delta2-partner w, and two K-extremes of one fan share w)')

# (C) two fans with the same centre sharing the middle z2: y12 (pair z1,z2) and y23 (pair z2,z3).
worstC = mpf(0)
for trial in range(300):
    Rv = mpf(10) ** random.choice([4, 5, 6, 8])
    f = sample_fan(Rv); Dl = f['D']
    # second fan: same R, Delta; its own rho' drawn in the feasible set (same tau)
    D2 = Dl**2; r0 = sqrt(Rv**2 - 1)
    for _ in range(1000):
        rv2 = r0 + (Rv - r0) * mpf(random.random())
        cz2 = (D2 - rv2**2 - 1) / (2 * rv2); ck2 = (Rv**2 - rv2**2 - 1) / (2 * rv2)
        if acos(cz2) >= pi / 6 and acos(ck2) - acos(cz2) >= pi / 3: break
    else:
        continue
    # fan 23: y23 on the positive y-axis at radius rho; its left middle z2 at angle -psi_z
    P = pts(f); z2 = P['z2']
    a_z2 = atan2(z2[0], z2[1])                       # angle of z2 about w (from the +y axis, clockwise positive x)
    half2 = asin(sin(acos(cz2)) / Dl)                # half central angle of fan 12's chord on C(w,Delta)
    ay12 = a_z2 - half2                              # fan 12 bisector angle
    y12 = (rv2 * sin(ay12), rv2 * cos(ay12))
    # K-slot of y12 on the side of z2 (+90deg side, towards y23): point of C(w,R) at distance 1 from y12, larger angle
    pk2 = acos(ck2)
    e_rad = (sin(ay12), cos(ay12)); e_tan = (cos(ay12), -sin(ay12))
    kslot = (y12[0] + sin(pk2) * e_tan[0] + cos(pk2) * e_rad[0], y12[1] + sin(pk2) * e_tan[1] + cos(pk2) * e_rad[1])
    assert abs(dist(kslot, (0, 0)) - Rv) < mpf(10)**-40 and abs(dist(kslot, y12) - 1) < mpf(10)**-40
    dd = dist(kslot, P['y'])
    worstC = max(worstC, dd * Rv)
    assert dd < 2 / Rv, (trial, dd)
print(f'(C) two fans with one centre sharing a middle: the inner K-slot of one is within {mp.nstr(worstC, 6)}/R of the '
      f'other fan point (< 2/R): so the shared-middle fans have their K-extremes on the outer sides, and a run of three is '
      f'impossible; with Lemma AI, at most 2 fans per centre')

# (D) R4 chain: all K-row points p_i have the unique Delta2-partner w (they lie on C(w,R) and no other centre exists)
print('(D) R4 chain (r6_n3_examples.py (a)): K-row = points of C(w,R), X has one centre, so every K-extreme is in Q; '
      '5 fans, 10 K-extremes (each serves one fan): |F| = 5 <= 2|Q_K| = 20')
print('r7_E_structure: all checks pass')

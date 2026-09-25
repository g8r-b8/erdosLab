"""R7/E section 1: the EXACT fan window.

Lemma EW. Let w, y, k, z2, z3 be points of X with |k-w| = R (=Delta_2), |z2-w| = |z3-w| = Delta, |y-w| < R,
and |y-k| = |y-z2| = |y-z3| = 1 (y has a neighbour on C(w,R) and two neighbours on C(w,Delta)).  Then
      tau in [tau_lo(R), sqrt3/2),   tau_lo(R) := (sqrt3*sqrt(R^2-1) - 1)/(2R) = sqrt3/2 - 1/(2R) - O(R^-2),
equivalently Delta^2 in [R^2 + sqrt3*sqrt(R^2-1), R^2 + sqrt3*R + 1), and rho := |y-w| in [sqrt(R^2-1), R).
Every tau in the window is locally realisable, and tau = tau_lo is exactly R4's fan (|z2z3| = |z3k| = 1).

Proof skeleton checked here:
 (1) with rho = |y-w| and psi measured from the outward radial direction (y-w)/rho,
     cos psi_z = (Delta^2-rho^2-1)/(2 rho), cos psi_k = (R^2-rho^2-1)/(2 rho) (law of cosines), so z2,z3 = +-psi_z;
 (2) |z2z3| >= 1 <=> psi_z >= 30deg <=> Delta^2 <= U(rho) := rho^2+1+sqrt3*rho;
 (3) |z3k| >= 1 (k and z3 on the same side) <=> psi_k - psi_z >= 60deg <=> Delta^2 >= L(rho) := rho^2+1+2 rho cos(psi_k-60deg);
     (2)+(3) force psi_k >= 90deg <=> rho >= rho0 := sqrt(R^2-1);
 (4) L(rho) = (rho^2+1+R^2)/2 + sqrt3*sqrt(rho^2 - c^2), c := (R^2-rho^2-1)/2 in [-1/2, 0];
     dL/drho = rho + sqrt3*rho*(1+c)/sqrt(rho^2-c^2) > 0, so min L = L(rho0) = R^2 + sqrt3*rho0 (sympy);
 (5) numbers at R = 1e4, 1e6, 1e8 (60 digits): tau/t windows, G := 2R sin(theta0 - pi/6) at the ends, the A3 resonance
     strip tau_res = cos(pi/6 + alpha2/2) (G = 1) lies inside, Rd range;
 (6) R4's fan chain (r6_n3_examples.py (a)) has tau = tau_lo to 40 digits;
 (7) exact local realisation: random tau in the window -> explicit (w,y,k,z2,z3) with all 5 constraints and
     pairwise distances >= 1 (60-digit).
"""
import random
import sympy as sp
from mpmath import mp, mpf, sqrt, acos, asin, cos, sin, pi

mp.dps = 60

# (1)-(4) symbolic
rho, R, De = sp.symbols('rho R Delta', positive=True)
c = (R**2 - rho**2 - 1) / 2
L = (rho**2 + 1 + R**2) / 2 + sp.sqrt(3) * sp.sqrt(rho**2 - c**2)
# L equals rho^2+1+2 rho cos(psi_k - 60) with cos psi_k = c/rho, sin psi_k = sqrt(rho^2-c^2)/rho:
Lcheck = rho**2 + 1 + 2 * rho * (sp.Rational(1, 2) * c / rho + sp.sqrt(3) / 2 * sp.sqrt(rho**2 - c**2) / rho)
assert sp.simplify(L - Lcheck) == 0
dL = sp.diff(L, rho)
target = rho + sp.sqrt(3) * rho * (1 + c) / sp.sqrt(rho**2 - c**2)
assert sp.simplify(dL - target) == 0
rho0 = sp.sqrt(R**2 - 1)
assert sp.simplify(L.subs(rho, rho0) - (R**2 + sp.sqrt(3) * rho0)) == 0
assert sp.simplify(c.subs(rho, rho0)) == 0 and sp.simplify(c.subs(rho, R) + sp.Rational(1, 2)) == 0
print('(1-4) symbolic: L(rho) = rho^2+1+2rho cos(psi_k-60); dL/drho = rho + sqrt3 rho (1+c)/sqrt(rho^2-c^2) > 0 '
      '(c in [-1/2,0]); L(rho0) = R^2 + sqrt3 rho0: OK')
# asymptotics of the window
tlo = (sp.sqrt(3) * rho0 - 1) / (2 * R)
ser = sp.series(tlo.subs(R, 1 / sp.Symbol('e', positive=True)), sp.Symbol('e', positive=True), 0, 3)
print('    tau_lo =', ser)


def window(Rv):
    Rv = mpf(Rv)
    r0 = sqrt(Rv**2 - 1)
    tau_lo = (sqrt(3) * r0 - 1) / (2 * Rv)
    tau_hi = sqrt(3) / 2
    D_lo = sqrt(Rv**2 + sqrt(3) * r0); D_hi = sqrt(Rv**2 + sqrt(3) * Rv + 1)
    t_lo, t_hi = D_lo - Rv, D_hi - Rv
    return Rv, r0, tau_lo, tau_hi, t_lo, t_hi


def G_of(tau, Rv):
    return 2 * Rv * sin(acos(tau) - pi / 6)


print('(5) windows (60 digits):')
for e in (4, 6, 8):
    Rv, r0, tl, th, t_lo, t_hi = window(mpf(10)**e)
    a2 = 2 * asin(1 / (2 * Rv))
    tres = cos(pi / 6 + a2 / 2)
    assert tl < tres < th
    Glo = G_of(tl, Rv); Gres = G_of(tres, Rv)
    assert abs(Glo - 2) < mpf(10)**-40 and abs(tl - cos(pi / 6 + asin(1 / Rv))) < mpf(10)**-50
    assert abs(Gres - 1) < mpf(10)**-40
    d_lo = 2 * sin(acos(tl)) - 1
    # |t - sqrt3/2| bounds
    lo_dev = (sqrt(3) / 2 - t_lo) * Rv; hi_dev = (t_hi - sqrt(3) / 2) * Rv
    assert lo_dev < mpf('0.3751') and hi_dev < mpf('0.1251')
    print(f'   R=1e{e}: sqrt3/2-tau_lo = {mp.nstr(th - tl, 12)} (R*.. = {mp.nstr((th-tl)*Rv, 10)}); '
          f't in [sqrt3/2 - {mp.nstr(lo_dev,8)}/R, sqrt3/2 + {mp.nstr(hi_dev,8)}/R); G in (0, {mp.nstr(Glo,10)}]; '
          f'Rd in (0, {mp.nstr(Rv*d_lo,10)}]; tau_res (G=1) inside; tau_lo = cos(pi/6+arcsin(1/R)), G(tau_lo) = 2 exactly')

# (6) R4 example: chord of length 2 of C(0,R), y its midpoint, z = y +- e/2 + (sqrt3/2) nu
Rv = mpf(10)**4
p1 = (Rv, mpf(0)); ang = 2 * asin(1 / Rv); p2 = (Rv * cos(ang), Rv * sin(ang))
y = ((p1[0] + p2[0]) / 2, (p1[1] + p2[1]) / 2)
ny = sqrt(y[0]**2 + y[1]**2); nu = (y[0] / ny, y[1] / ny)
e = ((p2[0] - p1[0]) / 2, (p2[1] - p1[1]) / 2)
z = (y[0] + e[0] / 2 + sqrt(3) / 2 * nu[0], y[1] + e[1] / 2 + sqrt(3) / 2 * nu[1])
Dl = sqrt(z[0]**2 + z[1]**2); t4 = Dl - Rv; tau4 = t4 - (1 - t4**2) / (2 * Rv)
_, _, tl, _, _, _ = window(Rv)
assert abs(tau4 - tl) < mpf(10)**-40, (tau4, tl)
print(f'(6) R4 fan (R=1e4): t = {mp.nstr(t4, 15)}, tau = {mp.nstr(tau4, 15)} = tau_lo(R) to 40 digits: '
      'R4 sits exactly at the lower end of the window')

# (7) local realisation for random tau in the window
random.seed(1327)
for trial in range(200):
    Rv = mpf(10) ** random.choice([4, 5, 6, 7])
    _, r0, tl, th, _, _ = window(Rv)
    tau = tl + (th - tl) * mpf(random.random())
    D2 = Rv**2 + 2 * Rv * tau + 1; Dl = sqrt(D2)
    # choose rho: need L(rho) <= D2 <= U(rho); U(rho) = rho^2+1+sqrt3 rho increasing; take the largest rho with
    # U(rho) >= D2 i.e. any rho in [rho_U, R), rho_U = root of U = D2; pick midpoint of [max(rho_U, r0), R)
    rU = (-sqrt(3) + sqrt(3 - 4 * (1 - D2))) / 2
    Lf = lambda r_: (r_**2 + 1 + Rv**2) / 2 + sqrt(3) * sqrt(r_**2 - ((Rv**2 - r_**2 - 1) / 2)**2)
    if Lf(Rv) <= D2:
        rLx = Rv
    else:
        a_, b_ = r0, Rv
        for _ in range(200):
            m_ = (a_ + b_) / 2
            if Lf(m_) <= D2: a_ = m_
            else: b_ = m_
        rLx = a_
    rl = max(rU, r0); rh = min(Rv, rLx)
    assert rl < rh
    rv = rl + (rh - rl) * mpf(random.uniform(0.01, 0.99))
    cz = (D2 - rv**2 - 1) / (2 * rv); ck = (Rv**2 - rv**2 - 1) / (2 * rv)
    pz, pk = acos(cz), acos(ck)
    assert pz >= pi / 6 - mpf(10)**-50 and pk - pz >= pi / 3 - mpf(10)**-50, (trial, pz, pk)
    Y = (mpf(0), rv)   # w = origin, radial = +z axis; point at angle psi from radial: y + (sin psi, cos psi)
    P = {'w': (mpf(0), mpf(0)), 'y': Y,
         'z2': (-sin(pz), rv + cz), 'z3': (sin(pz), rv + cz), 'k': (sin(pk), rv + ck)}
    d = lambda a, b: sqrt((P[a][0] - P[b][0])**2 + (P[a][1] - P[b][1])**2)
    assert abs(d('w', 'k') - Rv) < mpf(10)**-45 and abs(d('w', 'z2') - Dl) < mpf(10)**-45
    assert abs(d('w', 'z3') - Dl) < mpf(10)**-45 and d('w', 'y') < Rv
    for q in ('k', 'z2', 'z3'): assert abs(d('y', q) - 1) < mpf(10)**-45
    for a_, b_ in (('z2', 'z3'), ('z3', 'k'), ('z2', 'k')): assert d(a_, b_) >= 1 - mpf(10)**-45
print('(7) 200 random tau in the window: explicit local fans (w,y,k,z2,z3) with all constraints, min distance >= 1: OK')
print('r7_E_window: all checks pass')

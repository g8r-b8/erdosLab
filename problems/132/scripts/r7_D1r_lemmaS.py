#!/usr/bin/env python3
"""r7_D1r_lemmaS.py -- rigorous constants for Lemma S (D1r reconstruction, angle R7).

Lemma S (see angle_R7_reports/D1_report.md §3).  y in R\\D at depth h <= 1 is good (frame lemma with Lambda >= 100,
rho = 1, eps0 <= 1/50, perimeter >= 2 Lambda), Delta2 >= 1e4, and n is a unit vector with angle(n, n_0(y)) <= theta.
O_n(y) := S-neighbours  U  {u in R\\D neighbour : (u-y).n > 0, or (u-y).n = 0 and (u-y).n_perp > 0}.
Put a := max(theta, eps0).  If |O_n(y)| >= 4 then |O_n(y)| = 4, the directions are within a of -90,-30,30,90 (degrees,
from n_0), one extreme is a K-neighbour, both middles are S∩D, and t in [t_lo, t_hi] with
    Lc   := cos(30deg + a) - sin a                 (lower bound for the height difference Dc)
    Uc   := cos(30deg - a) + tan eps0              (upper bound for Dc)
    t_lo := Lc cos eps0 - 2 sin eps0 - 1/(2 Delta2)
    t_hi := Uc + 2 sin eps0 + 2/Delta2
The proof needs:
  (S1) 2 sin eps0 - Lc cos eps0 < 0          (the middle D-point is an exception for the K-point)
  (S2) Lc > 2 kappa_D, kappa_D := ((Lambda-1) tan eps0 + 1)/(Lambda-2)   (two D-points at different levels impossible)
  (S3) t_hi < 1                                (used to bound t^2 <= 1)
  (S4) 4*60 > 180 + 2a (in degrees)          (five owned directions impossible)
  (S5) a < 30deg                              (the ranges of psi_2, psi_3 are as claimed)
kappa(theta) := max(sqrt3/2 - t_lo, t_hi - sqrt3/2).
All quantities are evaluated in mpmath interval arithmetic at 60 decimal digits (rigorous enclosures); the asserted
inequalities are checked on the interval endpoints.
"""
import sys
sys.dont_write_bytecode = True
from mpmath import iv, mpf

iv.dps = 60
PI = iv.pi
R3 = iv.sqrt(3) / 2


def deg(x):
    return iv.mpf(x) * PI / 180


def lt(A, B):
    """rigorous A < B for intervals"""
    return (A - B).b < 0


def constants(theta, eps0, Lam, D2min):
    a = iv.mpf(max(mpf(theta), mpf(eps0)))          # a = max(theta, eps0), exact decimal input
    theta = iv.mpf(theta); eps0 = iv.mpf(eps0); Lam = iv.mpf(Lam)
    eps = iv.tan(eps0)
    Lc = iv.cos(deg(30) + a) - iv.sin(a)
    Uc = iv.cos(deg(30) - a) + eps
    kD = ((Lam - 1) * eps + 1) / (Lam - 2)
    D2 = iv.mpf(D2min)
    tlo = Lc * iv.cos(eps0) - 2 * iv.sin(eps0) - 1 / (2 * D2)
    thi = Uc + 2 * iv.sin(eps0) + 2 / D2
    checks = {
        'S1 exception': lt(2 * iv.sin(eps0) - Lc * iv.cos(eps0), iv.mpf(0)),
        'S2 D-levels': lt(2 * kD, Lc),
        'S3 t_hi<1': lt(thi, iv.mpf(1)),
        'S4 five impossible': lt(deg(180) + 2 * a, deg(240)),
        'S5 a<30deg': lt(a, deg(30)),
        'frame Lam(1-cos eps0)<1': lt(Lam * (1 - iv.cos(eps0)), iv.mpf(1)),
    }
    kap = max((R3 - tlo).b, (thi - R3).b)
    return a, Lc, Uc, kD, tlo, thi, kap, checks


def main():
    print("Lemma S, D1's parameters: theta_s = 1e-3, eps0 = 1e-6, Lambda = 1e9, Delta2 >= 1e4")
    a, Lc, Uc, kD, tlo, thi, kap, ch = constants('1e-3', '1e-6', '1e9', '1e4')
    for k, v in ch.items():
        print(f"  {k:26s}: {v}")
        assert v, k
    print(f"  Lc = {float(mpf(Lc.a)):.12f}, Uc = {float(mpf(Uc.b)):.12f}, kappa_D < {float(mpf(kD.b)):.3e}")
    print(f"  t in [{float(mpf(tlo.a)):.10f}, {float(mpf(thi.b)):.10f}] ;  kappa1 := max dev from sqrt3/2 < {float(mpf(kap)):.6e}")
    assert kap < mpf('1.56e-3') and kap < mpf('2.1e-3')
    # region margins (paper v3): Region I t <= t_I = sqrt3/2 - 2beta + 1e-15; Region II t >= sqrt3/2 + 3 beta (tau<=1)
    tI = R3 - iv.mpf('0.02') + iv.mpf('1e-15')
    print(f"  Region I margin sqrt3/2 - t_I = {float(mpf((R3 - tI).a)):.6e} > kappa1: {(R3 - tI).a > kap}")
    assert (R3 - tI).a > kap
    print(f"  Region II margin 0.03 > kappa1: {mpf('0.03') > kap};  tau>1 => t>1 > sqrt3/2 + kappa1: {1 > (R3).b + kap}")
    assert mpf('0.03') > kap and 1 > R3.b + kap
    # Delta2 >= 2e15 (the P4 threshold): the 1/Delta2 terms are negligible
    a, Lc, Uc, kD, tlo, thi, kap2, ch = constants('1e-3', '1e-6', '1e9', '2e15')
    assert all(ch.values())
    print(f"  (with Delta2 >= 2e15: kappa1 < {float(mpf(kap2)):.6e})")
    print()
    print("Lemma S for general sector tilt theta (eps0 = 1e-6, Lambda = 1e9, Delta2 >= 1e4 resp. 1e8):")
    for th in ['1e-2', '5e-3', '1e-3', '1e-4', '1e-5']:
        _, _, _, _, _, _, k4, c4 = constants(th, '1e-6', '1e9', '1e4')
        _, _, _, _, _, _, k8, c8 = constants(th, '1e-6', '1e9', '1e8')
        assert all(c4.values()) and all(c8.values())
        print(f"  theta = {th:6s}: kappa(theta) < {float(mpf(k4)):.4e} (D2>=1e4),  < {float(mpf(k8)):.4e} (D2>=1e8);  "
              f"ratio kappa/theta (D2>=1e8) = {float(mpf(k8)/mpf(th)):.4f}")
    # the worst case of (S2) over all admissible Lambda >= 100, eps0 <= 1/50, theta <= 1e-2
    _, Lc, _, kD, _, _, _, ch = constants('2e-2', '2e-2', '100', '1e4')
    print(f"\n  (S2) worst case Lambda=100, eps0=theta=1/50: 2 kappa_D < {float(mpf((2*kD).b)):.4f} < Lc > {float(mpf(Lc.a)):.4f}: {ch['S2 D-levels']}")
    assert ch['S2 D-levels'] and ch['S1 exception']
    print("OK: Lemma S constants verified in 60-digit interval arithmetic")


if __name__ == '__main__':
    main()

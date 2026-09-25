#!/usr/bin/env python3
"""r7_refD1_lemmaS.py -- REF_D1: independent rigorous check of Lemma S / Lemma 4.0 (D1r report §3-§4.1), and a sharper,
theta-independent pinning bound (referee remark R1).

Part 1 (60-digit mpmath intervals).  Independent re-implementation of
    L_c = cos(30deg + a) - sin a,  U_c = cos(30deg - a) + tan eps0,
    t_lo = L_c cos eps0 - 2 sin eps0 - 1/(2 D2),  t_hi = U_c + 2 sin eps0 + 2/D2,  kappa = max(sqrt3/2 - t_lo, t_hi - sqrt3/2)
  and of the side conditions (S1) 2 sin eps0 < L_c cos eps0, (S2) 2 kappa_D < L_c with kappa_D = ((Lam-1) tan eps0 + 1)/(Lam-2),
  (S3) t_hi < 1, (S4) 180 + 2a < 240 (deg), frame condition Lam(1 - cos eps0) < 1, eps0 <= 1/50.
  Checks: D1's value kappa(1e-3) < 1.553e-3 (eps0 = 1e-6, D2 >= 1e4); Lemma 4.0 bound kappa <= 1.51 a + 3.01 eps0 + 2/D2 on a
  grid with theta != eps0 as well; the Theorem-G parameter choice a = kappa/8, D2 >= 5/kappa gives kappa(theta) < kappa.
Part 2 (remark R1).  If |O_n(y)| = 4 then BOTH middle neighbours z2 (~ -30deg) and z3 (~ +30deg) are exceptions for the same
  K-extreme k (the (S1) computation applies to each), so with one Delta2-partner w_k of k:
      (z3 - z2).u_k = (d3^2 - d2^2)/(2 D2)   =>   |c3 - c2| <= rho := (2 sin eps0 + 2/D2)/cos eps0,
  and |c3 - c2| = 2|sin s| sin g >= |sin s| with s = (psi2+psi3)/2, g = (psi3-psi2)/2 in [30deg, 30deg + a]; so |s| <= sigma := asin rho.
  The K-extreme has c > -eps, i.e. |psi| < 90deg + eps0, whence g - 30deg < eps0 + sigma.  Hence
      t in [ (cos(30deg + 2 sigma + eps0) - sin sigma) cos eps0 - 2 sin eps0 - 1/(2 D2),  cos(30deg - sigma) + tan eps0 + 2 sin eps0 + 2/D2 ],
  a window kappa'(eps0, D2) that does NOT depend on the sector tilt theta.  We evaluate kappa' rigorously.
Run:  tools/memcap.sh 4000 .venv/bin/python problems/132/scripts/r7_refD1_lemmaS.py
"""
import sys
sys.dont_write_bytecode = True
from mpmath import iv, mpf

iv.dps = 60
PI = iv.pi
R3 = iv.sqrt(3) / 2
D30 = PI / 6


def lt(A, B):
    return (A - B).b < 0


def kappa(theta, eps0, D2, Lam='231'):
    th, e0, D2, Lam = iv.mpf(theta), iv.mpf(eps0), iv.mpf(D2), iv.mpf(Lam)
    a = th if mpf(theta) >= mpf(eps0) else e0
    eps = iv.tan(e0)
    Lc = iv.cos(D30 + a) - iv.sin(a)
    Uc = iv.cos(D30 - a) + eps
    tlo = Lc * iv.cos(e0) - 2 * iv.sin(e0) - 1 / (2 * D2)
    thi = Uc + 2 * iv.sin(e0) + 2 / D2
    kD = ((Lam - 1) * eps + 1) / (Lam - 2)
    conds = dict(S1=lt(2 * iv.sin(e0), Lc * iv.cos(e0)), S2=lt(2 * kD, Lc), S3=lt(thi, iv.mpf(1)),
                 S4=lt(PI + 2 * a, 4 * PI / 3), frame=lt(Lam * (1 - iv.cos(e0)), iv.mpf(1)),
                 eps0=(e0.b <= mpf(1) / 50))
    return max(mpf((R3 - tlo).b), mpf((thi - R3).b)), tlo, thi, conds


def kappa_sharp(eps0, D2):
    e0, D2 = iv.mpf(eps0), iv.mpf(D2)
    eps = iv.tan(e0)
    rho = (2 * iv.sin(e0) + 2 / D2) / iv.cos(e0)
    sig = rho / iv.sqrt(1 - rho * rho)      # rigorous upper bound for asin(rho) (= tan(asin rho)); lo, hi are monotone in sig
    lo = (iv.cos(D30 + 2 * sig + e0) - iv.sin(sig)) * iv.cos(e0) - 2 * iv.sin(e0) - 1 / (2 * D2)
    hi = iv.cos(D30 - sig) + eps + 2 * iv.sin(e0) + 2 / D2
    return max(mpf((R3 - lo).b), mpf((hi - R3).b))


def main():
    print("Part 1: Lemma S constants (independent implementation, 60-digit intervals)")
    k, tlo, thi, c = kappa('1e-3', '1e-6', '1e4', Lam='1e9')
    assert all(c.values()), c
    print(f"  D1 parameters (theta=1e-3, eps0=1e-6, D2>=1e4): t in [{float(mpf(tlo.a)):.7f}, {float(mpf(thi.b)):.7f}], "
          f"kappa < {float(k):.5e}")
    assert k < mpf('1.553e-3')
    k, tlo, thi, c = kappa('1e-2', '1e-2', '1e4')
    assert all(c.values()), c
    print(f"  Theorem G worst case (a = eps0 = 1e-2, Lambda = 231, D2 = 1e4): all side conditions hold; kappa < {float(k):.5f}")
    worst = mpf(0)
    for th in ['1e-2', '3e-3', '1e-3', '1e-4', '1e-6']:
        for e0 in ['1e-2', '1e-3', '1e-4', '1e-6']:
            for D2 in ['1e4', '1e6', '1e10']:
                a = max(mpf(th), mpf(e0))
                k, _, _, c = kappa(th, e0, D2)
                assert all(c.values()), (th, e0, D2, c)
                bound = mpf('1.51') * a + mpf('3.01') * mpf(e0) + 2 / mpf(D2)
                assert k <= bound, (th, e0, D2)
                worst = max(worst, k / bound)
    print(f"  Lemma 4.0 bound holds on a 5x4x3 grid (theta != eps0 included); max kappa/bound = {float(worst):.4f}")
    # Theorem G choice: a = min(kappa/8, 1e-2), eps0 = a, theta <= a, D2 >= max(1e4, 5/kappa)
    for kap in ['0.08', '0.02', '1e-3', '1e-5']:
        K = mpf(kap); a = min(K / 8, mpf('1e-2')); D2 = max(mpf('1e4'), 5 / K)
        k, _, _, c = kappa(str(a), str(a), str(D2))
        assert all(c.values()) and k < K, kap
        print(f"  kappa = {kap:5s}: a = {float(a):.3e}, D2* >= {float(D2):.0f}: kappa(theta) < {float(k):.4e} < kappa  OK")

    print("\nPart 2 (remark R1): both middles are pinned by the same K-point => theta-independent window kappa'(eps0, D2)")
    for e0, D2 in [('1e-6', '1e4'), ('1e-6', '1e8'), ('1e-3', '1e4'), ('1e-2', '1e4'), ('1e-4', '1e6')]:
        ks = kappa_sharp(e0, D2)
        k1, _, _, _ = kappa('1e-2', e0, D2)
        k3, _, _, _ = kappa('1e-3', e0, D2)
        print(f"  eps0={e0:5s} D2={D2:4s}: kappa' < {float(ks):.4e}   (D1r: theta=1e-3 -> {float(k3):.4e}, theta=1e-2 -> {float(k1):.4e})")
        assert ks < mpf('7') * mpf(e0) + 5 / mpf(D2)
    print("  kappa' <= 7 eps0 + 5/D2 on these samples (no theta term): the Gauss sector width need not shrink with kappa.")
    print("OK: REF_D1 Lemma S checks pass")


if __name__ == '__main__':
    main()

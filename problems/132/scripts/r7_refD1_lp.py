#!/usr/bin/env python3
"""r7_refD1_lp.py -- REF_D1: exact (Fraction) check of D1r §9 LP certificates and the fan-zone value (§6).
mu(delta) = e(S) + (1/2) Sigma_R v <= e(S) + (3 + eta/2) r + C  (Theorem G),  mu(D2) <= 3/2 s - 1/2 p  (paper Lemma 3.2).
With weights 4/7, 3/7 the coefficient of s must be <= 9/7, of r <= 9/7 + 3 eta/14, and of p <= 0, in every regime row.
Also: value(c) = max{3c/(2c+1), 1 + theta/(2(theta + 1/2))} with theta the p-coefficient of e(S)."""
from fractions import Fraction as F

rows = {'Region I': F(0), 'tau > 1': F(0), 'Region II (Thm 11.3)': F(1, 2), 'Region III (Thm W)': F(2, 3)}
lam = F(4, 7)
for eta in (F(0), F(1, 100), F(1, 3), F(1)):
    c = 3 + eta / 2
    for name, th in rows.items():
        cs = lam * F(3, 2) + (1 - lam) * 1
        cr = (1 - lam) * c
        cp = -lam * F(1, 2) + (1 - lam) * th
        assert cs == F(9, 7) and cr == F(9, 7) + 3 * eta / 14 and cp <= 0, (name, eta)
        # best LP value for this regime (Remark 3.6 form, kappa = 1/2)
        val = max(3 * c / (2 * c + 1), 1 + th / (2 * (th + F(1, 2))))
        assert val <= F(9, 7) + 3 * eta / 14, (name, eta, val)
        assert val >= F(9, 7) if eta == 0 else True
print("LP certificates (4/7, 3/7): s-coeff 9/7, r-coeff 9/7 + 3 eta/14, p-coeff <= 0 in all four rows (exact)")
print("  p-coefficients:", {k: str(-lam / 2 + (1 - lam) * v) for k, v in rows.items()})
# fan zone: 2c = 6 + 2 phi  ->  3(3+phi)/(7+2phi); combined with Theorem W's 9/7
for phi in (F(0), F(1, 4), F(1, 2), F(1)):
    c = 3 + phi
    v = max(3 * c / (2 * c + 1), F(9, 7))
    assert v == F(3) * (3 + phi) / (7 + 2 * phi)
    print(f"  phi = {phi}: fan-zone value {v} = {float(v):.5f}")
assert max(F(3) * (3 + F(1)) / 9, F(9, 7)) == F(4, 3)
# monotone in phi and equals 9/7 only at phi = 0
g = lambda p: F(3) * (3 + p) / (7 + 2 * p)
assert all(g(F(k, 100)) < g(F(k + 1, 100)) for k in range(100))
print("  3(3+phi)/(7+2phi) is increasing, 9/7 at phi=0, 21/16 at phi=1/2, 4/3 at phi=1 (exact)")
# eta' = 14 eta / 3 scaling of Theorem 9.1
for eta in (F(1, 10), F(1, 5), F(1, 2)):
    etap = 14 * eta / 3
    assert F(9, 7) + 3 * etap / 14 == F(9, 7) + eta
    print(f"  eta = {eta}: eta' = {etap} {'(> 1: Theorem G stated only for eta <= 1 -- fix F2)' if etap > 1 else ''}")
print("OK")

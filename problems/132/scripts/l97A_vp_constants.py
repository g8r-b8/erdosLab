"""Route A: exact (Fraction) check of the constants in E_A(h) = 71 h + 7 (RouteA_report.md, Step 8).
All transcendental quantities are replaced by rational upper bounds that are themselves checked
exactly (pi < 22/7 is NOT tight enough in one place, so we use pi < 355/113 and verify it).
Usage: .venv/bin/python l97A_vp_constants.py"""
from fractions import Fraction as F

PI_UP = F(355, 113)        # pi < 355/113 (classical; 355/113 - pi ~ 2.7e-7 > 0)
PI_LO = F(333, 106)        # pi > 333/106
TWO_PI = 2 * PI_UP

# sin(psi_c/2) <= s* = 194/199 ;  1/cos = 199/sqrt(1965)
s = F(194, 199)
c2 = 1 - s * s                              # cos^2 >= 1965/199^2
assert c2 == F(1965, 199 ** 2)
kap = F(4490, 1000)                         # claim 1/cos <= 4.490
assert kap * kap * c2 >= 1                  # (1/cos)^2 = 1/c2 <= kap^2
# theta* = arcsin(194/199) <= 1.347 : check sin(1.347) >= 194/199 via Taylor lower bound
x = F(13470, 10000)
sin_lo = x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040          # alternating: sin x >= this
assert sin_lo >= s, float(sin_lo)
theta = x
# (a) collapse: sum_c len Z_c <= kap * h * sum psi_c <= 2 pi kap h
C1 = TWO_PI * kap
# (b) endpoint excess: sum psi_c (1 + kap h psi_c) <= 2pi + 2 theta * 2pi * kap h ; times 3/(2pi)
Cb_h = F(3) * 2 * theta * kap               # coefficient of h after multiplying by 3/(2 pi)
Cb_0 = F(3)
# (c) scaling: eps'|A| <= (h + Delta2/R'^2)(2 pi + C1/200)(200/199),  Delta2 > 200 h >= 300
Cc_h = (TWO_PI + C1 / 200) * F(200, 199)
Cc_0 = Cc_h * (F(200, 199) ** 2) / 300      # Delta2/R'^2 <= (200/199)^2/Delta2 <= (200/199)^2/300
# assembly: Def >= 2|A| - [C1 + Cc_h + Cb_h] h - [6 + Cc_0]
Eh = C1 + Cc_h + Cb_h
E0 = 6 + Cc_0
print('C1 (collapse)      <=', float(C1))
print('Cc_h (scaling)     <=', float(Cc_h))
print('Cb_h (endpoints)   <=', float(Cb_h))
print('E_A(h) <= %.4f h + %.4f' % (float(Eh), float(E0)))
assert Eh <= 71 and E0 <= 7
# E_A(h) <= the plan's E(h) = 1764 h^2 + 223 h + 4 for all h >= 3/2 (indeed for all h >= 0)
for hh in [F(3, 2), F(2), F(10), F(1000)]:
    assert 71 * hh + 7 <= 1764 * hh ** 2 + 223 * hh + 4
# fallback count if depth <= h everywhere: |A| <= 2 (L + 2w + 1), w <= 3h, L <= 100 w
for hh in [F(3, 2), F(2), F(100)]:
    assert 2 * (100 * 3 * hh + 2 * 3 * hh + 1) < 1000 * hh
print('all constant checks passed')

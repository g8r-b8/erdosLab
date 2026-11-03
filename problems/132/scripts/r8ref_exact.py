"""R8 referee: independent exact checks of angle_R8_charge.md (Theorem 5.1, Lemma D, Prop 3.1 frame).

Written from scratch by the referee; it does not import or copy r8_charge_*.py.
Run with the project venv (sympy):  .venv/bin/python problems/132/scripts/r8ref_exact.py

Parts
  A  Normal form (N) sign facts, in the referee's own coordinates.
  B  Step 1 (alpha) cross identities, (gamma1) dot identity, (gamma3) apex formula, all symbolic.
  C  Step 2: cross(x;u,P2) == cross(u;P2,x) and c^2-d^2 = s(s-2t).
  D  Step 3, coordinate-free version: |c'p|^2 - Delta^2 = 2[(u-p').(p-p') - (c'-p').(p-p')]
     (no angles), then an EXACT rational sweep: parameters s,t chosen so that c, d are
     rational (Pythagorean), c' on rational points of the unit circle around p', every c'
     satisfying (d) + the extremality window is tested exactly in Q.
  E  Lemma D: rho = 2cos(theta'-theta/2) and |xb'|^2 = 1 + rho(rho - 2cos(theta/2)), symbolic.
"""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr

import sympy as sp

OK = True


def check(name: str, cond: bool) -> None:
    """Record one check."""
    global OK
    print(('ok   ' if cond else 'FAIL ') + name)
    OK = OK and bool(cond)


def cr(o, a, b):
    """cross(o; a, b) = (a-o) x (b-o)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def dot(o, a, b):
    """(a-o).(b-o)."""
    return (a[0] - o[0]) * (b[0] - o[0]) + (a[1] - o[1]) * (b[1] - o[1])


def sq(a, b):
    """|ab|^2."""
    return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2


s, t, d, k, c = sp.symbols('s t d k c', positive=True)
REL = {d**2: 1 - (t - s)**2, k**2: 1 - s**2, c**2: 1 - t**2}


def red(e):
    """Reduce polynomial e modulo d^2, k^2, c^2 relations."""
    e = sp.expand(e)
    G = [d**2 - (1 - (t - s)**2), k**2 - (1 - s**2), c**2 - (1 - t**2)]
    return sp.expand(sp.reduced(e, G, d, k, c, s, t, order='lex')[1])


x = (-s, 0); p = (s, 0); u = (-t, -d); b = (t, -d); w = (0, -k)
D2 = 1 + 4 * s * t

# ---------------- A
check('A |xu|=|pb|=|xw|=|pw|=1', all(red(sq(*q) - 1) == 0 for q in [(x, u), (p, b), (x, w), (p, w)]))
check('A |xb|^2=|pu|^2=1+4st', red(sq(x, b) - D2) == 0 and red(sq(p, u) - D2) == 0)
check('A cross(x;u,w) = cross(p;w,b) (u-side and b-side conditions coincide)',
      red(cr(x, u, w) - cr(p, w, b)) == 0)
check('A cross(x;u,p)=2sd, cross(x;u,b)=2td, cross(x;b,p)=2sd',
      red(cr(x, u, p) - 2*s*d) == 0 and red(cr(x, u, b) - 2*t*d) == 0 and red(cr(x, b, p) - 2*s*d) == 0)

# ---------------- B  (frame F: x=0, u=(1,0))
lam, mu, D, A, g = sp.symbols('lam mu D A g', real=True)
U = (1, 0); B1 = (D * sp.cos(A), D * sp.sin(A)); O = (0, 0)
P1 = (lam * U[0] + mu * B1[0], lam * U[1] + mu * B1[1])
check('B(alpha) cross(u;p\',x) = mu*D sinA', sp.simplify(cr(U, P1, O) - mu * D * sp.sin(A)) == 0)
check('B(alpha) cross(u;p\',b\') = (lam+mu-1)*D sinA',
      sp.simplify(cr(U, P1, B1) - (lam + mu - 1) * D * sp.sin(A)) == 0)
Ab = sp.symbols('Ab', real=True)
Pp = (2 * sp.cos(g) * sp.cos(g), 2 * sp.cos(g) * sp.sin(g))
check('B p\' = 1+e(2g) = 2cos g e(g)', sp.simplify(Pp[0] - (1 + sp.cos(2*g))) == 0
      and sp.simplify(Pp[1] - sp.sin(2*g)) == 0)
Bb = (D * sp.cos(Ab), D * sp.sin(Ab))
check('B(gamma1) |p\'b|^2-|p\'b\'|^2 = 2 r D (cos(g-A)-cos(g-Ab))',
      sp.simplify(sp.expand_trig(sq(Pp, Bb) - sq(Pp, B1) - 4 * sp.cos(g) * D * (sp.cos(g - A) - sp.cos(g - Ab)))) == 0)
check('B(gamma1) |p\'b|^2-D^2 = 2r(cos g - D cos(g-Ab))',
      sp.simplify(sp.expand_trig(sq(Pp, Bb) - D**2 - 4 * sp.cos(g) * (sp.cos(g) - D * sp.cos(g - Ab)))) == 0)
L, h1, h2 = sp.symbols('ell h1 h2', positive=True)
check('B(gamma3-) (h1+h2)^2 - D^2 = 1 - l^2/2 + 2h1h2 given h1^2=1-l^2/4, h2^2=D^2-l^2/4',
      sp.expand(((1 - L**2/4) + (D**2 - L**2/4) + 2*h1*h2) - D**2 - (1 - L**2/2 + 2*h1*h2)) == 0)

# ---------------- C
P2 = (0, -d - c); Pa = (0, c - d)
check('C |P1u|=|P1b|=|P2u|=|P2b|=1', all(red(sq(P, q) - 1) == 0 for P in (P2, Pa) for q in (u, b)))
check('C cross(x;u,P2) == cross(u;P2,x) == td + c(t-s)',
      red(cr(x, u, P2) - cr(u, P2, x)) == 0 and red(cr(x, u, P2) - (t*d + c*(t - s))) == 0)
check('C cross(u;P2,b) = 2ct', red(cr(u, P2, b) - 2*c*t) == 0)
check('C c^2 - d^2 = s(s-2t)', red(c**2 - d**2 - s*(s - 2*t)) == 0)

# ---------------- D  (coordinate-free Step 3)
X_, Y_ = sp.symbols('X Y', real=True)
Cp = (Pa[0] + X_, Pa[1] + Y_)
expr = sq(Cp, p) - D2 - 2 * (dot(Pa, u, p) - dot(Pa, Cp, p))
check('D |c\'p|^2 - Delta^2 = 2[(u-p\').(p-p\') - (c\'-p\').(p-p\')]  (mod X^2+Y^2=1)',
      red(sp.expand(expr).subs(X_**2, 1 - Y_**2)) == 0)
check('D cross(p\';u,x) = -(td + c(s-t))', red(cr(Pa, u, x) + (t*d + c*(s - t))) == 0)


def pyth(m: Fr) -> tuple[Fr, Fr]:
    """Rational point (2m/(1+m^2), (1-m^2)/(1+m^2)) on the unit circle."""
    return Fr(2) * m / (1 + m * m), (1 - m * m) / (1 + m * m)


# rational (s,t) with c, d rational (Step 3 never uses w, so k need not be rational).
cands = []
ms = sorted({Fr(a, q) for q in range(1, 30) for a in range(1, 4 * q) if Fr(a, q) < 3})
sins = {}
for m in ms:
    a, b_ = pyth(m)
    for sn, cs in ((a, b_), (b_, a)):
        if 0 < sn < 1 and cs > 0:
            sins[sn] = cs
sl = sorted(sins)
sset = set(sl)
for T_ in sl:
    for E_ in sl:                       # E_ = s - t, so d = cos-partner of E_ is rational
        S_ = T_ + E_
        if 2 * T_ < S_ < 1 and 2 * T_ <= 1:
            cands.append((S_, T_))
cands.sort(key=lambda q: (q[0].denominator + q[1].denominator, q))
print(f'D rational (s,t) with s>2t and c,d rational: {len(cands)}')
unit_pts = set()
for m in ms[:400]:
    a, b_ = pyth(m)
    for X0, Y0 in ((a, b_), (b_, a)):
        for sx, sy in itertools.product((1, -1), repeat=2):
            unit_pts.add((sx * X0, sy * Y0))
tested = viol = 0
worst = None
for S_, T_ in cands[:1500]:
    C_ = sins[T_]; D_ = sins[S_ - T_]
    y_ = C_ - D_
    if y_ <= 0:
        continue
    Pp_ = (Fr(0), y_); U_ = (-T_, -D_); Bq = (T_, -D_); Xq = (-S_, Fr(0)); Pq = (S_, Fr(0))
    Dl2 = 1 + 4 * S_ * T_
    assert sq(Pp_, U_) == 1 and sq(Pp_, Bq) == 1 and sq(Xq, Bq) == Dl2
    sgn_x = cr(Pp_, U_, Xq)
    assert sgn_x < 0
    for (X0, Y0) in unit_pts:
        Cq = (Pp_[0] + X0, Pp_[1] + Y0)
        if cr(Pp_, U_, Cq) >= 0:          # (d): strictly on x's side
            continue
        # extremality window: p' not in conv{c', u, b} <=> c' outside the closed cone -(cone(u-p', b-p'))
        # i.e. NOT (both cross conditions of the reversed cone hold). Test exactly with cross products.
        vu = (U_[0] - Pp_[0], U_[1] - Pp_[1]); vb = (Bq[0] - Pp_[0], Bq[1] - Pp_[1])
        # -c' direction lies in closed cone(vu, vb) iff cross(vu,-v)>=0 and cross(-v,vb)>=0
        v = (X0, Y0)
        in_cone = (vu[0] * (-v[1]) - vu[1] * (-v[0]) >= 0) and ((-v[0]) * vb[1] - (-v[1]) * vb[0] >= 0)
        if in_cone:   # p' in conv{c',u,b}: not extreme, excluded by (a)
            continue
        tested += 1
        gap = sq(Cq, Pq) - Dl2
        if worst is None or gap < worst[0]:
            worst = (gap, S_, T_, v)
        if gap <= 0:
            viol += 1
check(f'D exact rational sweep: {tested} admissible c\' tested, |c\'p|>Delta in all', viol == 0 and tested > 0)
print('   smallest |c\'p|^2 - Delta^2 =', float(worst[0]) if worst else None)

# ---------------- E  Lemma D
th, thp, rho = sp.symbols('theta thetap rho', real=True)
Xd = (1, 0); Wd = (0, 0); Pd = (sp.cos(th), sp.sin(th)); Ppd = (sp.cos(thp), sp.sin(thp))
Bd = (rho * sp.cos(th / 2), rho * sp.sin(th / 2))
check('E |p\'b\'|^2 - 1 = rho(rho - 2cos(thp - th/2))',
      sp.simplify(sp.expand_trig(sq(Ppd, Bd) - 1 - rho * (rho - 2 * sp.cos(thp - th / 2)))) == 0)
check('E |xb\'|^2 = |pb\'|^2 = 1 + rho(rho - 2cos(th/2))',
      sp.simplify(sp.expand_trig(sq(Xd, Bd) - 1 - rho * (rho - 2 * sp.cos(th / 2)))) == 0
      and sp.simplify(sp.expand_trig(sq(Pd, Bd) - sq(Xd, Bd))) == 0)
check('E cross(x;w,p) = -sin(theta) (orientation <-> half-plane)', sp.simplify(cr(Xd, Wd, Pd) + sp.sin(th)) == 0)

print('ALL OK' if OK else 'SOME FAILED')

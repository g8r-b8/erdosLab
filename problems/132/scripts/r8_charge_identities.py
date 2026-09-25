"""R8 Charge Lemma: exact (sympy) verification of every algebraic identity used in
angle_R8_charge.md.

The proof in angle_R8_charge.md is elementary: each step is an identity between explicit
coordinates followed by a sign/monotonicity argument.  This script re-derives every identity
in exact arithmetic, so that no algebra in the document rests on hand computation alone.

Frames (as in the document):
  * trapezoid frame T:  x=(-s,0), p=(s,0), u=(-t,-d), b=(t,-d), w=(0,-k),
                        d^2 = 1-(t-s)^2, k^2 = 1-s^2, c^2 = 1-t^2, Delta^2 = 1+4st;
  * x-frame F:          x=0, u=e(0), p'=2cos(g) e(g), b'=Delta e(A), b=Delta e(A_b);
  * w-frame W (Lemma D): w=0, x=e(0), p=e(th), p'=e(th2), b'=rho e(th/2).

usage: python3 r8_charge_identities.py      (exit code 0 iff every check passes)
"""
from __future__ import annotations

import sympy as sp

s, t, d, k, c = sp.symbols('s t d k c', positive=True)


def reduce_rel(e: sp.Expr) -> sp.Expr:
    """Reduce a polynomial expression modulo d^2=1-(t-s)^2, k^2=1-s^2, c^2=1-t^2.

    The three relations have pairwise coprime leading monomials d^2, k^2, c^2 in lex order
    d > k > c > s > t, so they form a Groebner basis and the remainder is a canonical form
    (linear in each of d, k, c).  An identity holds on the variety iff its remainder is 0.
    """
    G = [d**2 - 1 + (t - s)**2, k**2 - 1 + s**2, c**2 - 1 + t**2]
    num, den = sp.fraction(sp.together(sp.expand(e)))
    _, r = sp.reduced(sp.expand(num), G, d, k, c, s, t, order='lex')
    return sp.simplify(r / den) if den != 1 else sp.expand(r)


def trapezoid_points() -> dict[str, sp.Matrix]:
    """The five hook-1/trapezoid points in frame T plus the two axis apexes P1, P2.

    P1, P2 are the two points of C(u,1) n C(b,1); both lie on the axis X=0.
    """
    return {
        'x': sp.Matrix([-s, 0]), 'p': sp.Matrix([s, 0]),
        'u': sp.Matrix([-t, -d]), 'b': sp.Matrix([t, -d]), 'w': sp.Matrix([0, -k]),
        'P1': sp.Matrix([0, c - d]), 'P2': sp.Matrix([0, -d - c]),
    }


def sq(v: sp.Matrix) -> sp.Expr:
    """Squared Euclidean norm."""
    return sp.expand(v[0]**2 + v[1]**2)


def cr(o: sp.Matrix, a: sp.Matrix, q: sp.Matrix) -> sp.Expr:
    """Signed area (a-o) x (q-o)."""
    return sp.expand((a[0] - o[0]) * (q[1] - o[1]) - (a[1] - o[1]) * (q[0] - o[0]))


def expect_zero(name: str, e: sp.Expr, fails: list[str], red: bool = True) -> None:
    """Print and record whether e is identically 0 (after reduce_rel if red)."""
    r = reduce_rel(e) if red else sp.simplify(sp.expand(e))
    ok = (r == 0)
    print(('  ok   ' if ok else '  FAIL ') + name + ('' if ok else f'   remainder = {r}'))
    if not ok:
        fails.append(name)


def check_trapezoid() -> list[str]:
    """Trapezoid Lemma (R5 Thm 2) algebra: distances, Ptolemy, the w=(0,+k) exclusion."""
    F: list[str] = []
    P = trapezoid_points()
    x, p, u, b, w = P['x'], P['p'], P['u'], P['b'], P['w']
    D2 = 1 + 4*s*t
    print('[trapezoid]')
    for a, q in (('x', 'u'), ('p', 'b'), ('x', 'w'), ('p', 'w')):
        expect_zero(f'|{a}{q}|^2 = 1', sq(P[a] - P[q]) - 1, F)
    expect_zero('|xb|^2 = 1+4st (Ptolemy: Delta^2 = 1 + |xp||ub|)', sq(b - x) - D2, F)
    expect_zero('|pu|^2 = |xb|^2', sq(u - p) - sq(b - x), F)
    expect_zero('|xb|^2 - |xu|^2 = 4st  (so s,t have the same sign)', sq(b - x) - sq(u - x) - 4*s*t, F)
    # --- w above the axis is impossible
    wp = sp.Matrix([0, k])
    expect_zero('w=(0,+k): cross(x;w,u) = -sd - k(s-t)', cr(x, wp, u) - (-s*d - k*(s - t)), F)
    expect_zero('w=(0,+k): cross(x;w,p) = -2ks', cr(x, wp, p) + 2*k*s, F)
    expect_zero('w=(0,+k): cross(p;w,b) = sd + k(s-t) (<0 iff k(t-s) > sd)', cr(p, wp, b) - (s*d + k*(s - t)), F)
    expect_zero('w=(0,+k): cross(p;w,x) = 2ks', cr(p, wp, x) - 2*k*s, F)
    expect_zero('w=(0,+k): |wu|^2 = 2 + 2kd + 2s(t-s)', sq(u - wp) - (2 + 2*k*d + 2*s*(t - s)), F)
    expect_zero('w=(0,+k): Delta^2 - |wu|^2 = 2s(s+t) - (1+2kd)',
                D2 - sq(u - wp) - (2*s*(s + t) - (1 + 2*k*d)), F)
    # sub-case 2t = Delta, 2s = Delta - 1/Delta
    D = sp.symbols('D', positive=True)
    sb, tb = (D - 1/D)/2, D/2
    expect_zero('2t=Delta: 1+4st = Delta^2 when 2s = Delta-1/Delta', 1 + 4*sb*tb - D**2, F, red=False)
    expect_zero('2t=Delta: t-s = 1/(2 Delta)', tb - sb - 1/(2*D), F, red=False)
    rhs = sp.simplify(2*sb*(sb + tb))
    expect_zero('2t=Delta: 2s(s+t) = (2D^2 - 3 + D^-2)/2', rhs - (2*D**2 - 3 + D**-2)/2, F, red=False)
    phi = (1 + sp.sqrt(5))/2
    expect_zero('2t=Delta: at Delta=phi, 2s(s+t) = phi^2/2 = (phi+1)/2',
                rhs.subs(D, phi) - (phi + 1)/2, F, red=False)
    expect_zero('d/dD (2D^2-3+D^-2)/2 = 2D - D^-3 (>0 for D>1)',
                sp.diff((2*D**2 - 3 + D**-2)/2, D) - (2*D - D**-3), F, red=False)
    ok = bool((phi + 1)/2 < sp.Rational(5, 2))
    print(('  ok   ' if ok else '  FAIL ') + '(phi+1)/2 < 5/2 <= 1 + 2kd (k >= sqrt3/2, d > sqrt3/2)')
    if not ok:
        F.append('2t=Delta bound')
    # --- w below the axis: side quantities used later
    expect_zero('w=(0,-k): cross(x;u,w) = sd - k(s-t)  [= cross_w]', cr(x, u, w) - (s*d - k*(s - t)), F)
    expect_zero('w=(0,-k): cross(x;w,u) = -cross_w', cr(x, w, u) + (s*d - k*(s - t)), F)
    expect_zero('w=(0,-k): cross(x;w,p) = 2ks', cr(x, w, p) - 2*k*s, F)
    expect_zero('cross(x;u,p) = 2sd', cr(x, u, p) - 2*s*d, F)
    expect_zero('cross(x;u,b) = 2td', cr(x, u, b) - 2*t*d, F)
    expect_zero('cross(x;b,p) = 2sd', cr(x, b, p) - 2*s*d, F)
    return F


def check_offline() -> list[str]:
    """x on the line pw is impossible: Delta=2, neighbours at cos=1/4, |ac|^2=15/4 in (1,4).

    Also verifies the Lemma M identity (VERIFY_A1c.md), used throughout:
    p=0, b=(1,0), a=(cos A,-sin A), r=b+(cos F, sin F):
        |r-a|^2 - 1 = 2(1+cos F)(1-cos A) + 2 sin F sin A.
    """
    F: list[str] = []
    print('[Lemma M identity and collinear-x exclusion]')
    A, Fa = sp.symbols('A F', real=True)
    a = sp.Matrix([sp.cos(A), -sp.sin(A)])
    r = sp.Matrix([1 + sp.cos(Fa), sp.sin(Fa)])
    expect_zero('Lemma M: |r-a|^2 - 1 = 2(1+cosF)(1-cosA) + 2 sinF sinA',
                sp.trigsimp(sp.expand(sq(r - a) - 1 - 2*(1 + sp.cos(Fa))*(1 - sp.cos(A))
                                      - 2*sp.sin(Fa)*sp.sin(A))), F, red=False)
    a0, a1 = sp.symbols('a0 a1', real=True)
    sols = sp.solve([a0**2 + a1**2 - 1, (a0 - 2)**2 + a1**2 - 4], [a0, a1], dict=True)
    xs = sorted({sp.nsimplify(z[a0]) for z in sols})
    ok = xs == [sp.Rational(1, 4)]
    print(('  ok   ' if ok else '  FAIL ') + f'|a|=1, |a-x|=2 with x=(2,0) forces a0 = 1/4  (got {xs})')
    if not ok:
        F.append('offline a0')
    ys = sorted(z[a1] for z in sols)
    ac2 = sp.simplify((ys[1] - ys[0])**2)
    ok = ac2 == sp.Rational(15, 4) and 1 < ac2 < 4
    print(('  ok   ' if ok else '  FAIL ') + f'|ac|^2 = {ac2} lies strictly in (1, Delta^2) = (1, 4)')
    if not ok:
        F.append('offline ac')
    return F


def check_lemma_D() -> list[str]:
    """Lemma D (same middle vertex, same orientation) identities in frame W.

    TODO: implement.
    What's missing: |p'b'|^2-1 = rho(rho-2cos(th2-th/2)), |xb'|^2 = 1+rho(rho-2cos(th/2)),
      chord formula |e(a)-e(b)| = 2|sin((a-b)/2)|.
    Acceptance: returns [].
    Depends on: nothing.
    """
    raise NotImplementedError("Lemma D identities")


def check_step1() -> list[str]:
    """Step 1 (b' = b) identities in frame F.

    TODO: implement.
    What's missing: 1+e(2g) = 2cos(g) e(g); |p'b|^2-|p'b'|^2 = 2 p'.(b'-b) when |b|=|b'|;
      the plus-branch cross products (lambda,mu form); |pb'|^2 law of cosines; the gamma3
      apex identity (h1+h2)^2 - Delta^2 = 1 - l^2/2 + 2 h1 h2.
    Acceptance: returns [].
    Depends on: nothing.
    """
    raise NotImplementedError("step 1 identities")


def check_step2() -> list[str]:
    """Step 2 (p' on the axis) identities in frame T.

    TODO: implement.
    What's missing: S_xu(P2) == S_{u P2}(x) == td + c(t-s); S_{u P2}(b) = 2ct;
      c^2 - d^2 = s(s-2t).
    Acceptance: returns [].
    Depends on: reduce_rel, trapezoid_points.
    """
    raise NotImplementedError("step 2 identities")


def check_step3() -> list[str]:
    """Step 3 (no third neighbour c') identities in frame T with p' = P1.

    TODO: implement.
    What's missing: u-p' = (-t,-c), b-p' = (t,-c) (unit); S(x) = t y - c s;
      |c'-p|^2 = 1 + R^2 - 2(s cos gam - y sin gam); value at c'=u equals Delta^2;
      cos(a)-sum identity sin(z-f)+sin(z+f) = 2 sin z cos f.
    Acceptance: returns [].
    Depends on: reduce_rel, trapezoid_points.
    """
    raise NotImplementedError("step 3 identities")


def main() -> int:
    """Run every check; print a summary; return 0 iff all pass.

    TODO: implement.
    What's missing: the driver.
    Acceptance: exit code 0 and 'ALL OK' printed.
    Depends on: all check_* functions.
    """
    raise NotImplementedError("driver")


if __name__ == '__main__':
    raise SystemExit(main())

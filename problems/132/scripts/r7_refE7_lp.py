"""REF_E (R7): independent exact LP for E's Theorem E, by full vertex enumeration (Fractions).

Variables (per unit n, r = 1 - s eliminated): x = (s, p, q', F, z).  Maximise z subject to
  z <= A := 3/2 s - kap * p                     (VSQ: kap = 1/2, p = |Q| = all Delta2-degree-1 points of S)
  z <= B := s + theta q' + 3 (1 - s) + F        (Cor. 6.1 + Theorem W, q' = |Q'|)
  0 <= s <= 1,  0 <= q' <= p,  p <= s  (and optionally p <= 2s/3, B2 section 0),
  0 <= F <= 1 - s,  F <= m p                    (Proposition F: m = 2)
Every 5-subset of constraints is tried as a system of equalities; feasible solutions are the vertices; max z is exact.
Then: E's dual certificates rechecked; sensitivity table (what survives if an input fails).
"""
from fractions import Fraction as Fr
from itertools import combinations


def solve(Am, bv):
    n = len(Am)
    M = [list(map(Fr, row)) + [Fr(b)] for row, b in zip(Am, bv)]
    for c in range(n):
        piv = next((i for i in range(c, n) if M[i][c] != 0), None)
        if piv is None:
            return None
        M[c], M[piv] = M[piv], M[c]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c] / M[c][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def lp(theta, kap=Fr(1, 2), m=Fr(2), cap23=False, useF_le_mp=True):
    # constraints as (a, b): a.x <= b, x = (s, p, qp, F, z)
    C = [
        ((-Fr(3, 2), kap, 0, 0, 1), 0),            # z <= A
        ((2, 0, -theta, -1, 1), 3),                # z - (3 - 2s + theta qp + F) <= 0
        ((-1, 0, 0, 0, 0), 0), ((1, 0, 0, 0, 0), 1),
        ((0, 0, -1, 0, 0), 0), ((0, -1, 1, 0, 0), 0),   # qp >= 0, qp <= p
        ((-1, 1, 0, 0, 0), 0),                          # p <= s
        ((0, 0, 0, -1, 0), 0), ((1, 0, 0, 1, 0), 1),    # F >= 0, F <= 1 - s
    ]
    if useF_le_mp:
        C.append(((0, -m, 0, 1, 0), 0))                 # F <= m p
    if cap23:
        C.append(((-Fr(2, 3), 1, 0, 0, 0), 0))          # p <= 2s/3
    best, arg = None, None
    for sub in combinations(range(len(C)), 5):
        x = solve([C[i][0] for i in sub], [C[i][1] for i in sub])
        if x is None:
            continue
        if all(sum(Fr(a) * xi for a, xi in zip(C[i][0], x)) <= C[i][1] for i in range(len(C))):
            if best is None or x[4] > best:
                best, arg = x[4], x
    return best, arg


half, two3 = Fr(1, 2), Fr(2, 3)
res = {}
for th in (half, two3):
    for cap in (False, True):
        v, x = lp(th, cap23=cap)
        res[(th, cap)] = v
        print(f'theta={th}, p<=2s/3 {"on " if cap else "off"}: V = {v} = {float(v):.6f} at (s,p,q\',F) = {[str(t) for t in x[:4]]}')
assert res[(two3, False)] == res[(two3, True)] == Fr(81, 61)
assert res[(half, False)] == res[(half, True)] == Fr(53, 40)

# E's dual certificates: lam*A + (1-lam)*B + mult_a (p - q') + mult_b (r - F) + mult_c (2p - F), coefficients <= V on s, r
def cert(theta, V, lam, a, b, c):
    l2 = 1 - lam
    cs = Fr(3, 2) * lam + l2
    cr = 3 * l2 + b
    cp = -lam / 2 + a + 2 * c
    cq = theta * l2 - a
    cF = l2 - b - c
    assert min(lam, l2, a, b, c) >= 0 and cs <= V and cr <= V and cp <= 0 and cq <= 0 and cF <= 0, (cs, cr, cp, cq, cF)
    return cs, cr, cp, cq, cF
print('certificate theta=2/3:', cert(two3, Fr(81, 61), Fr(40, 61), Fr(14, 61), Fr(18, 61), Fr(3, 61)))
print('certificate theta=1/2:', cert(half, Fr(53, 40), Fr(13, 20), Fr(7, 40), Fr(11, 40), Fr(3, 40)))

# sensitivity: what survives if an input fails or is weakened
print('\nsensitivity (vertex enumeration):')
rows = [
    ('Theorem W fails (theta=1, R4 bound e(S)<=s+p)', dict(theta=Fr(1))),
    ('C2 weakened to <=3 fans per K-extreme (F<=3p), theta=2/3', dict(theta=two3, m=Fr(3))),
    ('C2 weakened to <=4 per K-extreme (F<=4p), theta=2/3', dict(theta=two3, m=Fr(4))),
    ('Proposition F fails (F<=r only), theta=2/3', dict(theta=two3, useF_le_mp=False)),
    ('Proposition F fails, theta=1/2', dict(theta=half, useF_le_mp=False)),
    ('sharper C2: <=1 fan per K-extreme (F<=p), theta=2/3', dict(theta=two3, m=Fr(1))),
    ('sharper C2: F<=p, theta=1/2', dict(theta=half, m=Fr(1))),
    ('fallback theta=4/5 (AI, SG, NC only), F<=2p', dict(theta=Fr(4, 5))),
]
out = {}
for lab, kw in rows:
    v, x = lp(**kw)
    out[lab] = v
    print(f'  {lab:62s} V = {str(v):7s} = {float(v):.6f}')
assert out['Theorem W fails (theta=1, R4 bound e(S)<=s+p)'] == Fr(4, 3)
assert out['Proposition F fails (F<=r only), theta=2/3'] == Fr(4, 3)
assert out['sharper C2: <=1 fan per K-extreme (F<=p), theta=2/3'] == Fr(45, 34)
print('r7_refE7_lp: all checks pass')

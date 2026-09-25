"""R7/E section 3: exact LP for the fan window (Fractions; primal point + dual certificate).

Inputs (per unit n = s + r, additive constants and eta dropped):
  mu(D2)  <= 3/2 s - 1/2 q                      (paper Lemma VSQ, q = |Q|)
  mu(d)   <= e(S) + 3 r + F                     (D1r Cor. 6.1: sum_R v <= 6r + 2F, F = |F*_4|)
  e(S)    <= s + theta q',  q' <= q             (Theorem W, Q' subset of Q; theta = 2/3, or 1/2 off G = 1 by REF_C)
  F <= r (F*_4 subset of R),  F <= 2 q          (Lemmas U + C2(a): every fan's K-extreme is in Q, <= 2 fans per K-extreme)
Value V(theta) = max over the polytope of min{mu(D2), mu(d)}.
Certificate: lam1 + lam2 = 1, a, b, c >= 0 with
  s: 3/2 lam1 + lam2 <= V;  r: 3 lam2 + b <= V;  q: -lam1/2 + a + 2c <= 0;  q': theta lam2 - a <= 0;  F: lam2 - b - c <= 0.
Also: the value as a function of the density phi = F/r (with F <= 2q), and variants (F <= q; no Q information = D1r's value).
"""
from fractions import Fraction as Fr
from itertools import product


def check(theta, V, primal, dual):
    s, r, q, qp, F = primal
    assert s + r == 1 and min(primal) >= 0 and qp <= q and F <= r and F <= 2 * q
    A = Fr(3, 2) * s - q / 2
    B = s + theta * qp + 3 * r + F
    assert min(A, B) == V, (A, B, V)
    l1, l2, a, b, c = dual
    assert l1 + l2 == 1 and min(dual) >= 0
    assert Fr(3, 2) * l1 + l2 <= V and 3 * l2 + b <= V
    assert -l1 / 2 + a + 2 * c <= 0 and theta * l2 - a <= 0 and l2 - b - c <= 0
    return V


V_half = check(Fr(1, 2), Fr(53, 40), (Fr(9, 10), Fr(1, 10), Fr(1, 20), Fr(1, 20), Fr(1, 10)),
               (Fr(13, 20), Fr(7, 20), Fr(7, 40), Fr(11, 40), Fr(3, 40)))
V_23 = check(Fr(2, 3), Fr(81, 61), (Fr(55, 61), Fr(6, 61), Fr(3, 61), Fr(3, 61), Fr(6, 61)),
             (Fr(40, 61), Fr(21, 61), Fr(14, 61), Fr(18, 61), Fr(3, 61)))
print(f'theta = 1/2 (G != 1, REF_C): V = {V_half} = {float(V_half):.6f}  (primal + dual certificate exact)')
print(f'theta = 2/3 (Theorem W, all G): V = {V_23} = {float(V_23):.6f}  (primal + dual certificate exact)')
assert V_23 < Fr(4, 3) and V_half < V_23 and Fr(9, 7) < V_half


# brute-force cross-check on a rational grid (the polytope maximum is at a vertex; the grid contains the optimum)
def grid_max(theta, N=120):
    best = Fr(0)
    for i in range(N + 1):
        s = Fr(i, N); r = 1 - s
        for j in range(0, N + 1):
            F = r * Fr(j, N)
            q = F / 2  # the minimum q allowed by F <= 2q maximises A; larger q only helps mu(D2)-side... check both
            for q_ in (q, q + Fr(1, 40), q + Fr(1, 10)):
                A = Fr(3, 2) * s - q_ / 2; B = s + theta * q_ + 3 * r + F
                best = max(best, min(A, B))
    return best


for theta, V in ((Fr(1, 2), V_half), (Fr(2, 3), V_23)):
    g = grid_max(theta)
    assert g <= V, (theta, g, V)
print('grid cross-check (s, F/r on a 1/120 grid): never exceeds the certified values')


# value as a function of phi = F/r with F <= 2q (worst q' = q):  V(phi) = max_s min(...)
def val_phi(theta, phi):
    # at r = 1, q = phi/2 is optimal (larger q lowers mu(D2) and raises mu(d)); equalise:
    # 3/2 s - phi/4 = s + theta phi/2 + 3 + phi  =>  s = 2(3 + phi + theta phi/2 + phi/4)
    s = 2 * (3 + phi + theta * phi / 2 + phi / 4)
    return (Fr(3, 2) * s - phi / 4) / (s + 1)


print('fan-window value vs phi = |F*_4|/r (with |F*_4| <= 2|Q|):')
for phi in (Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)):
    v2, v3 = val_phi(Fr(1, 2), phi), val_phi(Fr(2, 3), phi)
    old = 3 * (3 + phi) / (7 + 2 * phi)
    print(f'  phi={str(phi):4s}: theta=1/2 -> {float(v2):.6f}, theta=2/3 -> {float(v3):.6f};  D1r (no Q info) 3(3+phi)/(7+2phi) = {float(old):.6f}')
assert val_phi(Fr(1, 2), Fr(1)) == V_half and val_phi(Fr(2, 3), Fr(1)) == V_23
assert val_phi(Fr(1, 2), Fr(0)) == Fr(9, 7)

# variant: one fan per K-extreme (F <= q) would give
def val_phi_q(theta, phi):
    s = 2 * (3 + phi + theta * phi + phi / 2)
    return (Fr(3, 2) * s - phi / 2) / (s + 1)
print(f'variant F <= q (not proved): theta=2/3 -> {val_phi_q(Fr(2,3), Fr(1))} = {float(val_phi_q(Fr(2,3), Fr(1))):.6f}; '
      f'theta=1/2 -> {val_phi_q(Fr(1,2), Fr(1))} = {float(val_phi_q(Fr(1,2), Fr(1))):.6f}')
print('r7_E_lp: all checks pass')

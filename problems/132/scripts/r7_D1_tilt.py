#!/usr/bin/env python3
"""r7_D1_tilt.py -- Lemma S (tilted sector frame) : screen + rigorous margins.

Setting (flat model in y's own frame): dK = line z = 0, y = (0, -h), D-row at height t (pinned) when y has a
K-neighbour, else D points at a common height H >= t.  Sector frame n_j = n_0 rotated by alpha, |alpha| <= th_s.
Owned(y) = S-nbrs  U  {R-nbrs u : (u-y).n_j > 0}  U  {R-nbr with (u-y).n_j == 0 on the right}.
Lemma S: if |t - sqrt3/2| > kappa1 then |Owned(y)| <= 3.   (kappa1 := a + a0 + eps + delta0, a0 = sin th_s, a = asin a0)

Part 1: rigorous margin (Decimal, 60 digits) for th_s = 1e-3, eps0 = 1e-6, delta0 = 1e-4 (B1's constants):
        kappa1 and the Region I / Region II margins.
Part 2: adversarial float screen.  Neighbour candidates: K-points on z=0, D-points (S or R) on z=H, int-K points
        (c < h) at dense directions incl. near-horizontal ones; all subsets that are pairwise >= 1 apart
        (greedy random + exhaustive over small candidate sets).  Reports max |Owned| per t, and the witnesses
        of |Owned| = 4 (must all have |t - sqrt3/2| small: fans).
"""
import math, random, itertools, sys
from decimal import Decimal as Dm, getcontext
sys.dont_write_bytecode = True
getcontext().prec = 60


def dsin(x):
    x = Dm(x); s = Dm(0); term = x; k = 1
    while abs(term) > Dm(10) ** -58:
        s += term; term = -term * x * x / ((k + 1) * (k + 2)); k += 2
    return s


def dasin_upper(a0):
    # asin(a0) <= a0 / sqrt(1 - a0^2) for 0 <= a0 < 1
    return a0 / (1 - a0 * a0).sqrt()


def part1():
    th = Dm('1e-3'); eps0 = Dm('1e-6'); delta0 = Dm('1e-4')
    eps = eps0 * (1 + eps0)          # tan eps0 <= eps0(1+eps0) for small eps0
    a0 = max(eps, dsin(th)); a = dasin_upper(a0)
    kappa1 = a + a0 + eps + delta0
    r3 = Dm(3).sqrt() / 2
    beta = Dm('0.01')
    tI = r3 - 2 * beta + Dm('1e-4')          # Region I upper end (B1: t <= t_I)
    tII = r3 + 3 * beta - Dm('1e-4')         # Region II lower end
    print(f"Part 1 (60 digits): th_s=1e-3, eps0=1e-6, delta0=1e-4:  kappa1 = {kappa1:.6e}")
    print(f"  Region I : sqrt3/2 - t_I  = {r3 - tI:.6e}  > kappa1 : {r3 - tI > kappa1}")
    print(f"  Region II: t_II - sqrt3/2 = {tII - r3:.6e}  > kappa1 : {tII - r3 > kappa1}")
    assert r3 - tI > kappa1 and tII - r3 > kappa1
    # also: DN contradiction margin: c2 - c_q >= sqrt3/2 - a - a0 must exceed 2*tau*, tau* < 2e-6
    assert r3 - a - a0 > 4 * Dm('2e-6')
    # also h0 = a0 + eps < sqrt3/2 - a (u2, u3 cannot be non-D)
    assert a0 + eps < r3 - a
    return float(kappa1)


def owned_count(h, alpha, nbrs):
    """nbrs: list of (x, z, isS) in y-frame with y at (0,-h).  Frame n_j = (sin alpha, cos alpha)."""
    nx, nz = math.sin(alpha), math.cos(alpha)
    tx, tz = nz, -nx
    cnt = 0
    for (x, z, isS) in nbrs:
        dx, dz = x, z + h
        if isS:
            cnt += 1
        else:
            up = dx * nx + dz * nz
            if up > 1e-13 or (abs(up) <= 1e-13 and dx * tx + dz * tz > 0):
                cnt += 1
    return cnt


EPSK = 2e-3   # exaggerated tolerances for the screen: K heights in [-EPSK, 0] (F'2), D heights +- DEL (pinning/DN)
DEL = 1e-3
TH = 2e-3     # sector tilt bound used in the screen


def candidates(h, t, pinned, H, rng, nint=30):
    C = []
    for sg in (1, -1):
        f = -rng.uniform(0, EPSK) if rng.random() < .7 else 0.0
        c = h + f
        if abs(c) < 1:
            C.append((sg * math.sqrt(1 - c * c), f, 'K'))
        Hb = (t if pinned else H) + rng.uniform(-DEL, DEL)
        c = h + Hb
        if c < 1:
            x = sg * math.sqrt(1 - c * c)
            C += [(x, Hb, 'D'), (x, Hb, 'd')]
    angs = set()
    base = math.degrees(math.acos(min(1.0, h)))
    for _ in range(nint):
        angs.add(rng.uniform(base, 180.0))
    for d in (1e-7, 1e-5, 1e-3, 0.05, 0.1, 0.2):
        angs.add(min(180.0, base + d))
    for dg in list(angs):
        p = math.radians(dg)
        for sg in (1, -1):
            C.append((sg * math.sin(p), -h + math.cos(p), 'R'))
    return C


def far(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2 >= 1 - 1e-12


def screen(trials=150000, seed=7):
    rng = random.Random(seed)
    a0 = max(EPSK, math.sin(TH)); a = math.asin(a0)
    kap = a + a0 + EPSK + DEL
    worst = {}; wit = []
    r3 = math.sqrt(3) / 2
    tgrid = [0.001, 0.3, 0.5, 0.7, 0.84, 0.85, 0.855, 0.86, r3 - 0.004, r3 - 0.002, r3, r3 + 0.002, r3 + 0.004,
             0.87, 0.875, 0.88, 0.9, 0.95]
    for it in range(trials):
        t = rng.choice(tgrid)
        h = rng.choice([1e-9, 1e-6, 1e-4, 5e-4, 1e-3, 2e-3, 3e-3, rng.uniform(0, 0.006)])
        alpha = rng.uniform(-TH, TH)
        pinned = rng.random() < 0.7
        H = t + rng.choice([0, rng.uniform(0, 0.1)])
        C = candidates(h, t, pinned, H, rng)
        if not pinned:
            C = [c for c in C if c[2] != 'K']
        special = [c for c in C if c[2] != 'R']; rest = [c for c in C if c[2] == 'R']
        rng.shuffle(special); rng.shuffle(rest)
        special = [c for c in special if rng.random() < 0.9]
        # bias: near-horizontal int-K points first
        rest.sort(key=lambda c: abs(c[1] + h) if rng.random() < .5 else rng.random())
        chosen = []
        for c in special + rest:
            if all(far(c, d) for d in chosen):
                chosen.append(c)
        nb = [(x, z, k in ('K', 'D')) for (x, z, k) in chosen]
        o = owned_count(h, alpha, nb)
        key = round(t, 4)
        worst[key] = max(worst.get(key, 0), o)
        if o >= 4:
            wit.append((t, h, alpha, chosen))
    print(f"Part 2 screen (EPSK={EPSK}, DEL={DEL}, tilt<={TH}; lemma's kappa = {kap:.4f}):")
    print("  max |Owned| per t:", worst)
    bad = [w for w in wit if abs(w[0] - r3) > kap]
    print(f"  witnesses |Owned| = 4: {len(wit)} (all t within {max([abs(w[0]-r3) for w in wit] or [0]):.4f} of sqrt3/2);"
          f" outside the fan zone: {len(bad)}")
    if wit:
        t, h, al, ch = wit[0]
        print(f"  example (fan-zone) witness: t={t:.5f}, h={h:.1e}, alpha={al:.1e}, nbr directions/kinds:",
              sorted([(round(math.degrees(math.atan2(x, z + h)), 2), k) for (x, z, k) in ch]))
    assert not bad


if __name__ == '__main__':
    k1 = part1()
    screen()
    print("OK: Lemma S margins rigorous; screen found |Owned| = 4 only in the fan zone |t - sqrt3/2| <= kappa1")

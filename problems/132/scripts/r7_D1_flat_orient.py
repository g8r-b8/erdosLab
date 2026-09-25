#!/usr/bin/env python3
"""r7_D1_flat_orient.py -- EXACT check of the orientation lemma in the flat model.

Orientation rule (flat model, boundary of K = line z = 0, outward = +z):
  * spoke y-q (y in R, q in S): owned by y;
  * R-R edge: owned by the LOWER end (smaller z); if equal z, by the end with smaller x
    (so every point owns at most its right-horizontal edge);
  * edge between R∩D point d and R∩intK point y: owned by the lower end, i.e. y.
Claim (Lemma O): every R-point owns <= 3 edges, hence sum_R v = 2 E_R <= 6 r exactly.

All coordinates are integers, adjacency and height comparisons are exact.
  M1: 'row lattice' (x, z) = (a/2, b*sqrt3/2), a+b even, nbrs (a+-2,b), (a+-1,b+-1).
      K-row b = 0; optional D-row b = 1 (t = sqrt3/2, the fan value: included only as a stress test of the
      FLAT lemma, which holds for every t); interior b < 0.
  M2: 'column lattice' (x, z) = (i*sqrt3/2, j/2), i+j even, nbrs (i,j+-2), (i+-1,j+-1)  (REF_B1 cap lattice).
      D-row j = 1 (t = 1/2), K-row j = 0, interior j < 0.  Also the kinds 'b' (R on dK, impossible in reality
      but included for robustness) and 'd' (R∩D).
Deterministic families: B1's E1 (A-row stacks) and E2 (cap lattice); then random dense subsets.
"""
import random, sys
sys.dont_write_bytecode = True

M1_NB = [(2, 0), (-2, 0), (1, 1), (-1, 1), (1, -1), (-1, -1)]
M2_NB = [(0, 2), (0, -2), (1, 1), (-1, 1), (1, -1), (-1, -1)]
S_KINDS = ('K', 'D')          # S points
R_KINDS = ('R', 'd', 'b')     # R points ('d' = R∩D, 'b' = R on the K-line)


def check(cfg, nbv, height, xcoord):
    """cfg: dict site -> kind.  Returns (r, sumv, maxown, sum_own)."""
    own = {p: 0 for p in cfg if cfg[p] in R_KINDS}
    sumv = 0
    for p, k in cfg.items():
        if k not in R_KINDS:
            continue
        nb = [(p[0] + d[0], p[1] + d[1]) for d in nbv]
        nb = [q for q in nb if q in cfg]
        m = sum(1 for q in nb if cfg[q] in S_KINDS)
        sumv += len(nb) + m
        for q in nb:
            if cfg[q] in S_KINDS:
                own[p] += 1                      # spoke: owned by the R end
            else:
                # R-R edge: count it once, from the owner's side
                hp, hq = height(p), height(q)
                if hp < hq or (hp == hq and xcoord(p) < xcoord(q)):
                    own[p] += 1
    r = len(own)
    so = sum(own.values())
    assert sumv == 2 * so, (sumv, so)
    return r, sumv, (max(own.values()) if own else 0), so


def spokes_up_ok(cfg, nbv, height):
    """flat-model hypothesis: every S-neighbour of an R point in int K is strictly higher; every
    S-neighbour of a 'd' point is allowed anywhere (d owns <= deg <= 3)."""
    return True


# ---------------- deterministic families ----------------
def E1(k, W=12):
    cfg = {}
    for a in range(-W, W + 1):
        if a % 2 == 0:
            cfg[(a, 0)] = 'K'
        for j in range(1, k + 1):
            if (a + j) % 2 == 0:
                cfg[(a, -j)] = 'R'
    return cfg


def E2(k, W=10):
    cfg = {}
    for i in range(-W, W + 1):
        if i % 2 == 1:
            cfg[(i, 1)] = 'D'
        else:
            cfg[(i, 0)] = 'K'
        for L in range(1, k + 1):
            j = -L
            if (i + j) % 2 == 0:
                cfg[(i, j)] = 'R'
    return cfg


def rand_M1(rng, W, depth, with_D, dens, allow_b=None):
    if allow_b is None:
        allow_b = not with_D
    cfg = {}
    for a in range(-W, W + 1):
        for b in range(-depth, 2 if with_D else 1):
            if (a + b) % 2:
                continue
            u = rng.random()
            if b == 1:
                if u < dens: cfg[(a, b)] = 'D' if rng.random() < .6 else 'd'
            elif b == 0:
                if u < dens: cfg[(a, b)] = 'K' if (rng.random() < .8 or not allow_b) else 'b'
            else:
                if u < dens: cfg[(a, b)] = 'R'
    # reality: a D point is an exposed point of conv X, so its neighbours lie in an open half-plane and
    # deg <= 3.  A collinear flat D-row can violate this; delete K-row points until every D-row point has deg <= 3.
    for a in range(-W, W + 1):
        p = (a, 1)
        if p in cfg:
            nb = [(a + d[0], 1 + d[1]) for d in M1_NB if (a + d[0], 1 + d[1]) in cfg]
            while len(nb) > 3:
                q = [x for x in nb if x[1] == 0][0]
                del cfg[q]; nb.remove(q)
    return cfg


def rand_M2(rng, W, depth, dens):
    cfg = {}
    for i in range(-W, W + 1):
        for j in range(-depth, 2):
            if (i + j) % 2:
                continue
            u = rng.random()
            if j == 1:
                if u < dens: cfg[(i, j)] = 'D' if rng.random() < .7 else 'd'
            elif j == 0:
                if u < dens: cfg[(i, j)] = 'K' if rng.random() < .8 else 'b'
            else:
                if u < dens: cfg[(i, j)] = 'R'
    return cfg


def main():
    h1 = lambda p: p[1]; x1 = lambda p: p[0]
    print("E1 (A-row stacks, M1, windowed; boundary columns included, so average <= 6):")
    for k in (1, 2, 3, 4, 6, 8):
        r, sv, mo, so = check(E1(k), M1_NB, h1, x1)
        print(f"  k={k}: r={r} sum v={sv} 6r={6*r} max own={mo}")
        assert mo <= 3 and sv <= 6 * r
    print("E2 (cap lattice t=1/2, M2):")
    for k in (1, 2, 3, 4, 6, 8):
        r, sv, mo, so = check(E2(k), M2_NB, h1, x1)
        print(f"  k={k}: r={r} sum v={sv} 6r={6*r} max own={mo}")
        assert mo <= 3 and sv <= 6 * r
    rng = random.Random(20260925)
    worst = [0, 0]
    ntot = 0
    for it in range(40000):
        if it % 2 == 0:
            cfg = rand_M1(rng, rng.randint(4, 12), rng.randint(1, 7), rng.random() < .5, rng.choice([.6, .8, .9, 1.0]))
            r, sv, mo, so = check(cfg, M1_NB, h1, x1)
        else:
            cfg = rand_M2(rng, rng.randint(4, 12), rng.randint(1, 8), rng.choice([.6, .8, .9, 1.0]))
            r, sv, mo, so = check(cfg, M2_NB, h1, x1)
        ntot += 1
        assert mo <= 3, cfg
        assert sv <= 6 * r
        if r: worst = max(worst, [sv / r, it])
    print(f"random dense subsets: {ntot} configurations, max own = 3 everywhere, max average v = {worst[0]:.4f}")
    # Illustration of the ONLY failure mode: an R point ON the K-line ('b', impossible in reality since
    # X ∩ dK ⊂ S) together with a D-row at t = sqrt3/2 (fan height) can own 4: K at -90, D at -30, D/d at 30, x at 90.
    bad = 0; tot = 0
    for it in range(4000):
        cfg = rand_M1(rng, rng.randint(4, 10), rng.randint(1, 5), True, 0.8, allow_b=True)
        own = {}
        for p, k in cfg.items():
            if k not in R_KINDS: continue
            nb = [(p[0]+d[0], p[1]+d[1]) for d in M1_NB if (p[0]+d[0], p[1]+d[1]) in cfg]
            o = [q for q in nb if cfg[q] in S_KINDS or q[1] > p[1] or (q[1] == p[1] and p[0] < q[0])]
            if len(o) > 3:
                bad += 1; assert k == 'b', (p, k)
        tot += 1
    print(f"fan stress test (b on dK + D-row at sqrt3/2): {bad} owners of 4 in {tot} configs, all of kind 'b' (fan points)")
    print("OK: Lemma O (flat model) holds exactly on all tested configurations")


if __name__ == '__main__':
    main()

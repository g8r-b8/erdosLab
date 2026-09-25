"""Route A (L97) common machinery: steep-chain decomposition of Def for Theorem E' / CoreE.

Floats (tolerance TOL) -- SANITY CHECKS ONLY; the statements are proved on paper in
problems/132/lean/L97_reports/RouteA_report.md.

Objects (delta = 1):
  K = intersection of discs D(w, R) (w in centers), depth(z) = min_w (R - |z - w|).
  Y = given points in K (min distance >= 1), A = Y on bK, Yout = {depth < rho}, H = G[Yout].
  For a direction phi: steep edges = unit edges within open 30 deg of +-phi.  Each vertex has <= 1
  steep-up neighbour, so steep edges form vertex-disjoint phi-monotone chains; N(phi) = #chains.
  Def(H) = (3/2pi) * integral N(phi) dphi.
  T(phi) = A-points that are chain tops, B(phi) = A-points that are chain bottoms,
  M1(phi) = chains of >= 2 vertices whose top and bottom are both A-points.
"""
import math

TOL = 1e-9
TWO_PI = 2 * math.pi


def ang(v):
    return math.atan2(v[1], v[0]) % TWO_PI


def adist(a, b):
    d = abs(a - b) % TWO_PI
    return min(d, TWO_PI - d)


def dist(p, q):
    return math.hypot(p[0] - q[0], p[1] - q[1])


def unit(t):
    return (math.cos(t), math.sin(t))


# ---------------------------------------------------------------- circle interval sets
def norm_iv(lo, hi):
    """open arc (lo, hi) going counterclockwise, length hi-lo in [0, 2pi] -> list of [a,b] in [0,2pi)"""
    L = hi - lo
    if L <= 0:
        return []
    if L >= TWO_PI:
        return [(0.0, TWO_PI)]
    lo %= TWO_PI
    hi = lo + L
    if hi <= TWO_PI:
        return [(lo, hi)]
    return [(lo, TWO_PI), (0.0, hi - TWO_PI)]


def iv_union(ivs):
    ivs = sorted(i for i in ivs if i[1] > i[0])
    out = []
    for a, b in ivs:
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def iv_measure(ivs):
    return sum(b - a for a, b in iv_union(ivs))


def iv_neg(ivs):
    out = []
    for a, b in ivs:
        out += norm_iv(a + math.pi, b + math.pi)
    return iv_union(out)


def iv_inter(X, Y):
    out = []
    for a, b in iv_union(X):
        for c, d in iv_union(Y):
            lo, hi = max(a, c), min(b, d)
            if hi > lo:
                out.append((lo, hi))
    return iv_union(out)


def iv_minus(X, Y):
    # X \ Y
    comp = []
    Yu = iv_union(Y)
    prev = 0.0
    for a, b in Yu:
        if a > prev:
            comp.append((prev, a))
        prev = max(prev, b)
    if prev < TWO_PI:
        comp.append((prev, TWO_PI))
    return iv_inter(X, comp)


def iv_contains(ivs, t):
    t %= TWO_PI
    return any(a < t < b for a, b in ivs)


# ---------------------------------------------------------------- configuration
class Config:
    def __init__(self, centers, R, Y, rho, core_pt=None, name=''):
        self.W, self.R, self.rho, self.name = list(centers), R, rho, name
        self.h = rho + 0.5
        self.Yall = list(Y)
        for p in self.Yall:
            assert self.depth(p) > -1e-7, ('point outside K', p, self.depth(p))
        n = len(self.Yall)
        for i in range(n):
            for j in range(i + 1, n):
                assert dist(self.Yall[i], self.Yall[j]) > 1 - 1e-7, ('min dist violated', i, j)
        self.V = [p for p in self.Yall if self.depth(p) < rho - 1e-7]
        self.isA = [abs(self.depth(p)) < 1e-7 for p in self.V]
        self.nA = sum(self.isA)
        self.nb = [[] for _ in self.V]
        self.E = 0
        for i in range(len(self.V)):
            for j in range(i + 1, len(self.V)):
                if abs(dist(self.V[i], self.V[j]) - 1) < 1e-7:
                    self.nb[i].append(j)
                    self.nb[j].append(i)
                    self.E += 1
        self.Def = 3 * len(self.V) - self.E
        self.core_pt = core_pt if core_pt is not None else self.find_deep()

    # geometry of K
    def depth(self, z):
        return min(self.R - dist(z, w) for w in self.W)

    def find_deep(self):
        # crude maximiser of depth (grid + refinement) -- only a sanity tool
        xs = [w[0] for w in self.W]
        ys = [w[1] for w in self.W]
        cx, cy = sum(xs) / len(xs), sum(ys) / len(ys)
        best, bp = self.depth((cx, cy)), (cx, cy)
        step = self.R / 4
        while step > 1e-6:
            improved = False
            for dx in (-step, 0, step):
                for dy in (-step, 0, step):
                    q = (bp[0] + dx, bp[1] + dy)
                    d = self.depth(q)
                    if d > best + 1e-15:
                        best, bp, improved = d, q, True
            if not improved:
                step /= 2
        return bp

    def normal_cone(self, a):
        """(lo, hi) angles of the normal cone of K at boundary point a (ccw arc lo->hi)."""
        act = [ang((a[0] - w[0], a[1] - w[1])) for w in self.W if abs(self.R - dist(a, w)) < 1e-7]
        if len(act) == 1:
            return act[0], act[0]
        # normal cone = smallest arc containing the active normals (< pi)
        best = None
        for s in act:
            L = max((t - s) % TWO_PI for t in act)
            if L < math.pi and (best is None or L < best[1]):
                best = (s, L)
        return best[0], best[0] + best[1]

    def support_point(self, t):
        """z(nu) = argmax <z, nu> over K, nu = unit(t)."""
        nu = unit(t)
        cands = []
        for w in self.W:
            z = (w[0] + self.R * nu[0], w[1] + self.R * nu[1])
            if self.depth(z) > -1e-9:
                cands.append(z)
        m = len(self.W)
        for i in range(m):
            for j in range(i + 1, m):
                for z in circle_inter(self.W[i], self.W[j], self.R):
                    if self.depth(z) > -1e-9:
                        cands.append(z)
        return max(cands, key=lambda z: z[0] * nu[0] + z[1] * nu[1])

    def hchord(self, y, e_up, e_right):
        """K meets the line {p: p.e_up = y}: return (l, r) in the e_right coordinate, or None."""
        lo, hi = -1e18, 1e18
        for w in self.W:
            wy = w[0] * e_up[0] + w[1] * e_up[1]
            wx = w[0] * e_right[0] + w[1] * e_right[1]
            d2 = self.R ** 2 - (y - wy) ** 2
            if d2 < 0:
                return None
            s = math.sqrt(d2)
            lo, hi = max(lo, wx - s), min(hi, wx + s)
        if lo > hi + 1e-12:
            return None
        return lo, hi

    # ------------------------------------------------------------ per-point exposure sets
    def nbr_angles(self, i):
        p = self.V[i]
        return sorted(ang((self.V[j][0] - p[0], self.V[j][1] - p[1])) for j in self.nb[i])

    def E_set(self, i):
        """directions phi in which vertex i is exposed (no neighbour within open 30 deg)."""
        angs = self.nbr_angles(i)
        if not angs:
            return [(0.0, TWO_PI)]
        out = []
        d = len(angs)
        for k in range(d):
            a, b = angs[k], angs[(k + 1) % d]
            gap = (b - a) % TWO_PI
            if d == 1:
                gap = TWO_PI
            out += norm_iv(a + math.pi / 6, a + gap - math.pi / 6)
        return iv_union(out)


def circle_inter(c1, c2, R):
    d = dist(c1, c2)
    if d < 1e-12 or d > 2 * R:
        return []
    a = d / 2
    hh = math.sqrt(max(R * R - a * a, 0))
    mx, my = (c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2
    ux, uy = (c2[0] - c1[0]) / d, (c2[1] - c1[1]) / d
    return [(mx - hh * uy, my + hh * ux), (mx + hh * uy, my - hh * ux)]


# ---------------------------------------------------------------- per-A-point slack and cost
def sigma(phi, nu_t):
    """sigma_nu(phi) = 2pi/3 - angle(phi, -nu)."""
    return 2 * math.pi / 3 - adist(phi, nu_t + math.pi)


def mfun(phi, nu_t):
    return min(max(sigma(phi, nu_t), 0.0), math.pi / 3)


def slack_and_cost(cfg, i, nq=4000):
    """s_a = |E u -E| - 4pi/3 ; cost_a = (6/pi) int_{E \\ -E} sup_{nu in N_K(a)} m_nu (quadrature)
    plus the closed-form upper bound (6/pi) min(s_out, pi/3)^2, s_out = (outer gap) - pi."""
    E = cfg.E_set(i)
    nE = iv_neg(E)
    s = iv_measure(iv_union(E + nE)) - 4 * math.pi / 3
    D = iv_minus(E, nE)
    lo, hi = cfg.normal_cone(cfg.V[i])
    nus = [lo] if hi == lo else [lo + (hi - lo) * k / 8 for k in range(9)]
    tot = 0.0
    for a, b in D:
        n = max(2, int(nq * (b - a) / TWO_PI) + 2)
        for k in range(n):
            phi = a + (b - a) * (k + 0.5) / n
            tot += max(mfun(phi, nu) for nu in nus) * (b - a) / n
    cost = 6 / math.pi * tot
    # outer gap relative to the worst normal: s_out = pi - ... ; neighbours' depression angles
    angs = cfg.nbr_angles(i)
    if not angs:
        sout = TWO_PI
    elif len(angs) == 1:
        sout = math.pi
    else:
        gaps = [((angs[(k + 1) % len(angs)] - angs[k]) % TWO_PI) for k in range(len(angs))]
        sout = max(gaps) - math.pi
    bound = 6 / math.pi * min(sout, math.pi / 3) ** 2
    return s, cost, bound, len(angs)


# ---------------------------------------------------------------- chains for a direction
def chains(cfg, phi):
    """returns list of chains (lists of vertex indices, bottom -> top) for direction phi."""
    n = len(cfg.V)
    up = [None] * n
    down = [None] * n
    for i in range(n):
        p = cfg.V[i]
        for j in cfg.nb[i]:
            q = cfg.V[j]
            t = ang((q[0] - p[0], q[1] - p[1]))
            dd = adist(t, phi)
            assert abs(dd - math.pi / 6) > 1e-9 and abs(dd - 5 * math.pi / 6) > 1e-9, 'degenerate phi'
            if dd < math.pi / 6:
                assert up[i] is None, 'two up-neighbours'
                up[i] = j
            elif dd > 5 * math.pi / 6:
                assert down[i] is None
                down[i] = j
    out = []
    for i in range(n):
        if down[i] is None:
            c = [i]
            while up[c[-1]] is not None:
                c.append(up[c[-1]])
            out.append(c)
    assert sum(len(c) for c in out) == n
    return out


def side_fn(cfg, chain, phi):
    """side(p) in {-1,+1} (left/right of the chain, strip rule + attachments), 0 on the chain."""
    e_up = unit(phi)
    e_r = unit(phi - math.pi / 2)
    P = [cfg.V[k] for k in chain]
    Y = [p[0] * e_up[0] + p[1] * e_up[1] for p in P]
    X = [p[0] * e_r[0] + p[1] * e_r[1] for p in P]
    yb, yt = Y[0], Y[-1]

    def c_of(y):
        for k in range(len(Y) - 1):
            if Y[k] - 1e-12 <= y <= Y[k + 1] + 1e-12:
                s = (y - Y[k]) / (Y[k + 1] - Y[k])
                return X[k] + s * (X[k + 1] - X[k])
        raise ValueError

    def attach(y0, x0):
        ch = cfg.hchord(y0, e_up, e_r)
        if ch is None:
            return 0
        l, r = ch
        if abs(x0 - l) < 1e-7 and r - l > 1e-7:
            return +1   # region beyond attaches to the right
        if abs(x0 - r) < 1e-7 and r - l > 1e-7:
            return -1
        return 0        # endpoint is an extreme point: nothing beyond

    at_top = attach(yt, X[-1])
    at_bot = attach(yb, X[0])

    def side(p):
        y = p[0] * e_up[0] + p[1] * e_up[1]
        x = p[0] * e_r[0] + p[1] * e_r[1]
        if yb <= y <= yt:
            d = x - c_of(y)
            if abs(d) < 1e-9:
                return 0
            return 1 if d > 0 else -1
        if y > yt:
            return at_top
        return at_bot
    return side, (at_top, at_bot)


def on_chain(cfg, chain, z):
    for k in range(len(chain) - 1):
        p, q = cfg.V[chain[k]], cfg.V[chain[k + 1]]
        if seg_point_dist(p, q, z) < 1e-7:
            return True
    return False


def seg_point_dist(p, q, z):
    vx, vy = q[0] - p[0], q[1] - p[1]
    L2 = vx * vx + vy * vy
    t = max(0.0, min(1.0, ((z[0] - p[0]) * vx + (z[1] - p[1]) * vy) / L2))
    return math.hypot(p[0] + t * vx - z[0], p[1] + t * vy - z[1])

"""Route A (Erdos #132, Theorem E' core): test harness for the VISIBLE-PATH proof.

Geometry: K = intersection of discs D(w, D2), w in W;  K' = {depth >= h} = intersection of D(w, D2 - h).
Normal coordinates of K': every x outside K' lies on exactly one ray r_nu = y(nu) + t*nu (t > 0),
nu = direction of x - P(x) (P = nearest point of K'), y(nu) = support point of K' in direction nu.

Visible path: for every nu the FIRST drawing point on r_nu.  Computed combinatorially: the vertex
directions nu(v) cut the circle into open intervals; on each interval the first-hit edge is constant
(unit edges do not cross).  At each vertex direction the path is  L -> B -> R  (left limit, first hit,
right limit) joined by radial jumps.  Relative angle psi = arg(direction) - nu lies in (0, pi) on
pieces, 0 on outward jumps, pi on inward jumps;  turning kappa = psi_out - psi_in at each corner.

Checked (mpmath, dps 40; tolerances 1e-25):
  (W)  wedge lemma: no edge of a corner vertex v points into the open K'-side wedge W_v
       (ccw from d_out to -d_in, measure pi - kappa_v);
  (T)  turning identity: sum kappa = 2*pi (all rays hit) or (2*pi - |E|) - pi*J (J escape arcs);
  (O)  A-points: all neighbours in the open inner half-plane; out-gap >= pi; W_a disjoint from it;
  (MI) Def >= |A| + m - 3 + (3/2pi)|E| + (3/2)J   (m = number of vertex corners);
  (CL) |A| <= n + J + err  (n = visible pieces);
  (E)  Def >= 2|A| - E1(h),  E1(h) = 35 h + 4.
"""
import mpmath as mp
import random
from collections import defaultdict

mp.mp.dps = 40
TOL = mp.mpf(10) ** -25
PI = mp.pi
TWOPI = 2 * mp.pi


def dot(a, b):
    return a.real * b.real + a.imag * b.imag


def cross(a, b):
    return a.real * b.imag - a.imag * b.real


def ang(z):
    a = mp.arg(z)
    return a + TWOPI if a < 0 else a


def mod2pi(a):
    a = mp.fmod(a, TWOPI)
    return a + TWOPI if a < 0 else a


class Region:
    """Intersection of closed discs of common radius r centred at W."""

    def __init__(self, W, r):
        self.W, self.r = list(W), mp.mpf(r)
        self.corners = []   # (point, i, j)
        for i in range(len(W)):
            for j in range(i + 1, len(W)):
                for c in self._circ_int(W[i], W[j]):
                    if self.contains(c, TOL * 10):
                        self.corners.append((c, i, j))

    def _circ_int(self, a, b):
        d = abs(b - a)
        if d == 0 or d >= 2 * self.r:
            return []
        m = (a + b) / 2
        hh = mp.sqrt(self.r ** 2 - (d / 2) ** 2)
        u = (b - a) / d * 1j
        return [m + hh * u, m - hh * u]

    def contains(self, z, tol=TOL):
        return all(abs(z - w) <= self.r + tol for w in self.W)

    def depth(self, z):   # r - max distance; >= 0 inside
        return min(self.r - abs(z - w) for w in self.W)

    def nearest(self, x):
        best, bd = None, None
        for w in self.W:
            z = w + self.r * (x - w) / abs(x - w)
            if self.contains(z, TOL * 10):
                d = abs(x - z)
                if bd is None or d < bd:
                    best, bd = z, d
        for (c, i, j) in self.corners:
            d = abs(x - c)
            if bd is None or d < bd:
                best, bd = c, d
        return best

    def support(self, nu):
        e = mp.expj(nu)
        best, bv = None, None
        for w in self.W:
            z = w + self.r * e
            if self.contains(z, TOL * 10):
                v = dot(z, e)
                if bv is None or v > bv:
                    best, bv = z, v
        for (c, i, j) in self.corners:
            v = dot(c, e)
            if bv is None or v > bv + TOL:
                best, bv = c, v
        return best

    def exit_t(self, y, e):
        """largest t with y + t e in region (y inside)."""
        best = None
        for w in self.W:
            b = dot(y - w, e)
            cc = abs(y - w) ** 2 - self.r ** 2
            t = -b + mp.sqrt(b * b - cc)
            best = t if best is None else min(best, t)
        return best


def unit_graph(pts):
    """edges at distance 1 (within TOL); asserts min distance >= 1 - TOL."""
    grid = defaultdict(list)
    for i, p in enumerate(pts):
        grid[(int(mp.floor(p.real)), int(mp.floor(p.imag)))].append(i)
    edges = []
    for i, p in enumerate(pts):
        cx, cy = int(mp.floor(p.real)), int(mp.floor(p.imag))
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for j in grid.get((cx + dx, cy + dy), []):
                    if j > i:
                        d = abs(pts[j] - p)
                        assert d > 1 - TOL, ('min distance violated', i, j, d)
                        if d < 1 + TOL:
                            edges.append((i, j))
    return edges


def gaps_of(v, pts, nbrs):
    """sorted neighbour angles of v."""
    return sorted(ang(pts[k] - pts[v]) for k in nbrs[v])


def gap_containing(angles, a):
    """(start, length) of the angular gap of the (sorted) neighbour angles containing direction a
    (a strictly inside); None if a is (within tol) a neighbour direction."""
    if not angles:
        return (mp.mpf(0), TWOPI)
    n = len(angles)
    for i in range(n):
        s = angles[i]
        e = angles[(i + 1) % n] if i + 1 < n else angles[0] + TWOPI
        L = e - s if n > 1 else TWOPI
        x = mod2pi(a - s)
        if TOL < x < L - TOL:
            return (s, L)
    return None


def analyse(pts, Kreg, h, verbose=False):
    """Everything for one configuration. Kreg = K (radius D2). Returns dict of results.
    Isolated vertices are removed first (each contributes exactly 3 >= 2 to Def); the
    visible-path lemmas are checked on the rest, the final bound (E) on the original graph."""
    edges0 = unit_graph(pts)
    deg0 = [0] * len(pts)
    for (i, j) in edges0:
        deg0[i] += 1
        deg0[j] += 1
    iso = [i for i in range(len(pts)) if deg0[i] == 0]
    isoA = sum(1 for i in iso if Kreg.depth(pts[i]) < TOL)
    pts = [pts[i] for i in range(len(pts)) if deg0[i] > 0]
    V = len(pts)
    edges = unit_graph(pts)
    nbrs = [[] for _ in range(V)]
    for (i, j) in edges:
        nbrs[i].append(j)
        nbrs[j].append(i)
    Kp = Region(Kreg.W, Kreg.r - h)
    assert Kp.corners or len(Kp.W) == 1
    D2 = Kreg.r
    # depth checks
    dep = [Kreg.depth(p) for p in pts]
    assert min(dep) > -TOL, 'point outside K'
    for (i, j) in edges:
        assert Kreg.depth((pts[i] + pts[j]) / 2) < h, 'edge midpoint too deep'
        assert not Kp.contains((pts[i] + pts[j]) / 2, -TOL), 'edge meets K prime'
    A = [i for i in range(V) if dep[i] < TOL]
    Def = 3 * V - len(edges)
    # normal coordinates
    Pv = [Kp.nearest(p) for p in pts]
    nuv = [ang(pts[i] - Pv[i]) for i in range(V)]
    # group vertex directions
    order = sorted(range(V), key=lambda i: nuv[i])
    groups = []
    for i in order:
        if groups and nuv[i] - groups[-1][0] < mp.mpf(10) ** -22:
            groups[-1][1].append(i)
        else:
            groups.append([nuv[i], [i]])
    if len(groups) > 1 and groups[0][0] + TWOPI - groups[-1][0] < mp.mpf(10) ** -22:
        groups[0][1] += groups[-1][1]
        groups.pop()
    G = len(groups)
    # edge nu-arcs and traversal direction
    einfo = []
    NB = 720
    bins = defaultdict(list)
    for k, (i, j) in enumerate(edges):
        a, b = nuv[i], nuv[j]
        if mod2pi(b - a) < PI:
            p, q, s = i, j, a
            L = mod2pi(b - a)
        else:
            p, q, s = j, i, b
            L = mod2pi(a - b)
        einfo.append((p, q, s, L))
        b0 = int(mp.floor(s / TWOPI * NB))
        b1 = int(mp.floor((s + L) / TWOPI * NB))
        for bb in range(b0, b1 + 1):
            bins[bb % NB].append(k)

    def ray_edge(k, nu):
        """t and point where edge k meets ray nu (None if not)."""
        p, q, s, L = einfo[k]
        y = Kp.support(nu)
        e = mp.expj(nu)
        P0, d = pts[p], pts[q] - pts[p]
        den = cross(e, d)
        if abs(den) < TOL:
            return None
        # y + t e = P0 + u d
        t = cross(P0 - y, d) / den
        u = cross(P0 - y, e) / den
        if -TOL < u < 1 + TOL and t > 0:
            return (t, y + t * e)
        return None

    def first_edge(nu):
        best = None
        for k in bins[int(mp.floor(nu / TWOPI * NB)) % NB]:
            p, q, s, L = einfo[k]
            x = mod2pi(nu - s)
            if TOL < x < L - TOL:
                r = ray_edge(k, nu)
                if r is not None and (best is None or r[0] < best[0]):
                    best = (r[0], k)
        return None if best is None else best[1]

    # interval after group g: (nu_g, nu_{g+1})
    ivl_edge, ivl_len = [], []
    for g in range(G):
        a = groups[g][0]
        b = groups[(g + 1) % G][0] + (TWOPI if g + 1 == G else 0)
        ivl_len.append(b - a)
        ivl_edge.append(first_edge(mod2pi((a + b) / 2)))
    # path at each group
    corners = []          # (kind, idx or None, psi_in, psi_out, nu)
    vertex_corner = {}
    results = {'wedge_fail': 0, 'psi_fail': 0}

    def psi_edge(k, nu):
        p, q, s, L = einfo[k]
        ps = mod2pi(ang(pts[q] - pts[p]) - nu)
        if not (TOL < ps < PI - TOL):
            results['psi_fail'] += 1
        return ps

    for g in range(G):
        nu, gv = groups[g]
        ein, eout = ivl_edge[g - 1], ivl_edge[g]
        # hits on this ray: vertices of the group, edges crossing
        cand = [(Kp.nearest(pts[v]) is not None and abs(pts[v] - Kp.support(nu)), pts[v], v) for v in gv]
        for k in bins[int(mp.floor(nu / TWOPI * NB)) % NB]:
            r = ray_edge(k, nu)
            if r is not None:
                cand.append((r[0], r[1], None))
        cand.sort(key=lambda c: c[0])
        B = cand[0]
        seq = []
        if ein is not None:
            r = ray_edge(ein, nu)
            assert r is not None
            seq.append([r[0], r[1]])
        seq.append([B[0], B[1]])
        if eout is not None:
            r = ray_edge(eout, nu)
            assert r is not None
            seq.append([r[0], r[1]])
        # dedupe
        dd = []
        for s_ in seq:
            if not dd or abs(dd[-1][1] - s_[1]) > mp.mpf(10) ** -20:
                dd.append(s_)
        for idx, (t, x) in enumerate(dd):
            if idx == 0:
                pin = psi_edge(ein, nu) if ein is not None else PI
            else:
                pin = PI if dd[idx - 1][0] > t else mp.mpf(0)
            if idx == len(dd) - 1:
                pout = psi_edge(eout, nu) if eout is not None else mp.mpf(0)
            else:
                pout = PI if dd[idx + 1][0] < t else mp.mpf(0)
            vid = None
            for v in gv:
                if abs(pts[v] - x) < mp.mpf(10) ** -20:
                    vid = v
            virt = (idx == 0 and ein is None) or (idx == len(dd) - 1 and eout is None)
            corners.append((vid, pin, pout, nu, virt))
    # turning identity
    J = sum(1 for e in ivl_edge if e is None)
    Emeas = sum(ivl_len[g] for g in range(G) if ivl_edge[g] is None)
    ksum = sum(c[2] - c[1] for c in corners)
    target = TWOPI if J == 0 else (TWOPI - Emeas) - PI * J
    results['turn_err'] = abs(ksum - target)
    # feet positive
    results['foot_neg'] = sum(1 for c in corners if c[0] is None and c[2] - c[1] < -TOL)
    # wedge lemma
    vc = [c for c in corners if c[0] is not None]
    vids = [c[0] for c in vc]
    assert len(set(vids)) == len(vids), 'vertex visited twice'
    m = len(vc)
    Aset = set(A)
    for (v, pin, pout, nu, virt) in vc:
        W0 = nu + pout
        Wlen = PI - (pout - pin)
        for k in nbrs[v]:
            x = mod2pi(ang(pts[k] - pts[v]) - W0)
            if TOL < x < Wlen - TOL:
                results['wedge_fail'] += 1
    # overlap |W_a cap H+_a| at A-points that are endpoints of open hit arcs (virtual turn)
    def arc_overlap(s1, l1, s2, l2):
        tot = mp.mpf(0)
        for sh in (-TWOPI, 0, TWOPI):
            lo = max(s1, s2 + sh)
            hi = min(s1 + l1, s2 + sh + l2)
            if hi > lo:
                tot += hi - lo
        return tot
    ovl = {}
    for (v, pin, pout, nu, virt) in vc:
        if virt and v in Aset:
            w = min(Kreg.W, key=lambda w: abs(D2 - abs(pts[v] - w)))
            na = ang(pts[v] - w)
            ovl[v] = arc_overlap(mod2pi(nu + pout), PI - (pout - pin), mod2pi(na - PI / 2), PI)
    results['ovl_sum'] = sum(ovl.values()) if ovl else mp.mpf(0)
    results['ovl_max_minus_halfpi'] = max([o - PI / 2 for o in ovl.values()] + [mp.mpf(-9)])
    # per-vertex claim check
    kap = {c[0]: c[2] - c[1] for c in vc}
    pv_fail = []
    for v in range(V):
        claim = mp.mpf(0)
        if v in Aset:
            claim += TWOPI / 3
        if v in kap:
            claim += TWOPI / 3 - kap[v] - ovl.get(v, 0)
        actual = (3 - mp.mpf(len(nbrs[v])) / 2) * TWOPI / 3
        if actual < claim - TOL:
            pv_fail.append((v, len(nbrs[v]), v in Aset, float(kap.get(v, 0)), float(actual - claim)))
    results['pv_fail'] = len(pv_fail)
    if verbose and pv_fail:
        print('per-vertex failures', pv_fail)
        for c in corners:
            print('corner', c[0], float(c[1]), float(c[2]), float(c[3]))
    # A-point outward gaps
    outfail = 0
    for a in A:
        w = min(Kreg.W, key=lambda w: abs(D2 - abs(pts[a] - w)))
        n_a = (pts[a] - w) / abs(pts[a] - w)
        for k in nbrs[a]:
            if dot(pts[k] - pts[a], n_a) > -TOL:
                outfail += 1
    results['A_out_fail'] = outfail
    # pieces
    n = 0
    for g in range(G):
        e = ivl_edge[g]
        if e is None:
            continue
        prev = ivl_edge[g - 1]
        # continuation if same edge and path passes straight through (single non-vertex corner at g)
        cg = [c for c in corners if c[3] == groups[g][0]]
        cont = (prev == e and len(cg) == 1 and cg[0][0] is None)
        if not cont:
            n += 1
    if J == 0 and n == 0 and G > 0:
        n = 1
    LB = len(A) + m - 3 + (mp.mpf(3) / TWOPI) * (Emeas - results['ovl_sum']) + (mp.mpf(3) / 2) * J
    E1 = 35 * h + 4
    res = dict(V=V, E=len(edges), Def=Def, A=len(A), m=m, n=n, J=J, Emeas=float(Emeas),
               MI_slack=float(Def - LB), CL_def=len(A) - (n + J),
               E_slack=float(Def + 3 * len(iso) - (2 * (len(A) + isoA) - E1)),
               ratio=float(Def + 3 * len(iso)) / max(1, len(A) + isoA), iso=len(iso),
               D2A=Def + 3 * len(iso) - 2 * (len(A) + isoA))
    res.update({k: (float(v) if not isinstance(v, int) else v) for k, v in results.items()})
    return res


# ---------------------------------------------------------------- generators
def boundary_point(Kreg, o, phi):
    e = mp.expj(phi)
    return o + Kreg.exit_t(o, e) * e


def next_boundary(Kreg, o, phi0, L):
    b0 = boundary_point(Kreg, o, phi0)
    lo, hi = phi0, phi0 + mp.mpf(1) / 2
    for _ in range(140):
        mid = (lo + hi) / 2
        if abs(boundary_point(Kreg, o, mid) - b0) < L:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def seed_A(Kreg, o, phi_start, phi_span, rng, p_edge=0.6, maxgap=0.9):
    """boundary points with chords 1 (prob p_edge) or 1+U(0, maxgap); phi_span=None -> closed ring."""
    phis = [mp.mpf(phi_start)]
    end = phi_start + (TWOPI if phi_span is None else phi_span)
    while True:
        L = mp.mpf(1) if rng.random() < p_edge else 1 + mp.mpf(rng.uniform(1e-4, maxgap))
        ph = next_boundary(Kreg, o, phis[-1], L)
        if ph > end:
            break
        phis.append(ph)
    pts = [boundary_point(Kreg, o, ph) for ph in phis]
    if phi_span is None:
        while len(pts) > 1 and abs(pts[-1] - pts[0]) < 1:
            pts.pop()
    return pts


class Grid:
    def __init__(self):
        self.g = defaultdict(list)
        self.pts = []

    def add(self, z):
        self.g[(int(mp.floor(z.real)), int(mp.floor(z.imag)))].append(len(self.pts))
        self.pts.append(z)

    def near(self, z, r=2):
        cx, cy = int(mp.floor(z.real)), int(mp.floor(z.imag))
        out = []
        for dx in range(-r, r + 1):
            for dy in range(-r, r + 1):
                out += self.g.get((cx + dx, cy + dy), [])
        return out

    def ok(self, z):
        return all(abs(self.pts[j] - z) > 1 - TOL for j in self.near(z, 1))


def grow(Kreg, seedpts, rho, rng, attempts=4000, p_pendant=0.1, max_depth=None):
    """greedy apex growth inside K at depth < rho (points strictly inside K)."""
    md = rho if max_depth is None else max_depth
    Gd = Grid()
    for z in seedpts:
        Gd.add(z)
    for _ in range(attempts):
        i = rng.randrange(len(Gd.pts))
        p = Gd.pts[i]
        if rng.random() < p_pendant:
            z = p + mp.expj(mp.mpf(rng.uniform(0, 6.283185307)))
        else:
            cands = [j for j in Gd.near(p) if 1 - TOL < abs(Gd.pts[j] - p) < 2 - mp.mpf('1e-6')]
            if not cands:
                continue
            q = Gd.pts[rng.choice(cands)]
            d = abs(q - p)
            mid = (p + q) / 2
            u = (q - p) / d * 1j * mp.sqrt(1 - (d / 2) ** 2)
            z = mid + u if rng.random() < 0.5 else mid - u
        dz = Kreg.depth(z)
        if not (TOL * 100 < dz < md):
            continue
        if Gd.ok(z):
            Gd.add(z)
    return Gd.pts

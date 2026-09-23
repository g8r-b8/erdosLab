"""Greedy search for sets X with no 4 concyclic points and large mu(Delta2) - n.
Delta2 normalised to 1; distances must be <= 1 (strictly < 1-TOL unless == 1) or == Delta.
New points are placed at intersections of unit circles around existing points (creating
>= 2 Delta2-edges each). Floating point with tolerance TOL -- exploratory only."""
import random, math, itertools, sys
TOL = 1e-9

def circ_int(p, q, r=1.0):
    dx, dy = q[0]-p[0], q[1]-p[1]; d = math.hypot(dx, dy)
    if d < 1e-12 or d > 2*r: return []
    a = d/2; h2 = r*r - a*a
    if h2 < 0: return []
    h = math.sqrt(h2); mx, my = p[0]+dx/2, p[1]+dy/2
    return [(mx - h*dy/d, my + h*dx/d), (mx + h*dy/d, my - h*dx/d)]

def circ_int_rr(p, q, r1, r2):
    d = math.dist(p, q)
    if d < 1e-12 or d > r1+r2 or d < abs(r1-r2): return []
    a = (r1*r1 - r2*r2 + d*d)/(2*d); h2 = r1*r1 - a*a
    if h2 < 0: return []
    h = math.sqrt(h2); ex, ey = (q[0]-p[0])/d, (q[1]-p[1])/d
    mx, my = p[0]+a*ex, p[1]+a*ey
    return [(mx - h*ey, my + h*ex), (mx + h*ey, my - h*ex)]

def concyclic(a, b, c, d):
    m = []
    for p in (a, b, c, d):
        m.append([p[0]-d[0], p[1]-d[1], (p[0]-d[0])**2+(p[1]-d[1])**2])
    m = m[:3]
    det = (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1]) - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
           + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
    return abs(det) < 1e-7

def ok_add(X, p, D):
    for q in X:
        d = math.dist(p, q)
        if d < 1e-6: return None
        if abs(d-1) < TOL or abs(d-D) < TOL: continue
        if d > 1 - 1e-6: return None
    for tri in itertools.combinations(X, 3):
        if concyclic(*tri, p): return None
        # also collinear-ish triples are fine
    return sum(abs(math.dist(p, q)-1) < TOL for q in X)

def run(D, steps, rng):
    X = [(0.0, 0.0), (D, 0.0)]
    # seed: point at distance 1 from both ends
    X += circ_int(X[0], X[1])[:1]
    edges = sum(abs(math.dist(a, b)-1) < TOL for a, b in itertools.combinations(X, 2))
    for _ in range(steps):
        cands = []
        pairs = list(itertools.combinations(range(len(X)), 2)); rng.shuffle(pairs)
        for i, j in pairs[:200]:
            for p in circ_int(X[i], X[j]):
                g = ok_add(X, p, D)
                if g: cands.append((g, p))
        for i in range(len(X)):
            for _k in range(20):
                t = rng.uniform(0, 2*math.pi)
                for r in (1.0, D):
                    p = (X[i][0]+r*math.cos(t), X[i][1]+r*math.sin(t))
                    g = ok_add(X, p, D)
                    if g is not None: cands.append((g, p))
            for j in range(len(X)):
                if i != j:
                    for p in circ_int_rr(X[i], X[j], 1.0, D):
                        g = ok_add(X, p, D)
                        if g is not None: cands.append((g, p))
        if not cands: break
        best = max(c[0] for c in cands)
        g, p = rng.choice([c for c in cands if c[0] == best])
        X.append(p); edges += g
    # verify Delta2 == 1 really is second-largest and a diameter exists
    ds = sorted({round(math.dist(a, b), 7) for a, b in itertools.combinations(X, 2)})
    return X, edges, ds[-1], ds[-2] if len(ds) > 1 else None

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
best = {}
for trial in range(300):
    D = rng.uniform(1.02, 1.9)
    X, e, dmax, d2 = run(D, 30, rng)
    n = len(X)
    if abs(d2-1) > 1e-6: continue
    ex = e - n
    if ex > best.get(n, (-99,))[0]: best[n] = (ex, D)
for n in sorted(best): print(n, "mu-n =", best[n][0], "D=%.4f" % best[n][1])

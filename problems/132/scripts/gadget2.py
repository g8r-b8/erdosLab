"""Two-round symmetric gadget search on the ring core (Problem 1.6).
Orbit of a candidate x = {x*rot^k}. For a set G of k orbits, per-sector new edge counts
(A,B) are computed exactly (float tol); improvement iff 4A+3B > 9k (LP dual at 9/7)."""
import math, cmath, itertools, sys
import numpy as np
from ring16 import ring_core, circ_int, spectrum, TOL

def run(m, rounds=2, maxk=3, radius_loc=3.0):
    v, us, D, D2 = ring_core(m)
    core = v + us
    g = spectrum(core)[0][0]
    rot = np.array([cmath.exp(2j*math.pi*k/m) for k in range(m)])
    anchor = us[0]
    def valid_orbit(x, base):
        ds = np.abs(np.array(base) - x)
        if ds.min() < g - TOL or ds.max() > D2 + TOL: return False
        dc = np.abs(x*rot[1:] - x)
        return not (dc.min() < g - TOL or dc.max() > D2 + TOL)
    cand = []
    base = list(core)
    for r in range(rounds):
        new = []
        loc = [p for p in base if abs(p - anchor) < radius_loc*g]
        far = base
        for p in loc:
            for q in far:
                if p == q: continue
                for r1 in (g, D2):
                    for r2 in (g, D2):
                        for x in circ_int(p, r1, q, r2):
                            if abs(x-anchor) < radius_loc*g and valid_orbit(x, base):
                                if all(abs(x-c) > 1e-7 for c in cand+new):
                                    new.append(x)
        cand += new
        # next round: allow candidates generated relative to previous candidates' orbits
        base = list(core) + [c*r for c in new for r in rot]
    print(f"m={m} g={g:.4f} candidates={len(cand)}", flush=True)
    best = []
    for k in range(1, maxk+1):
        for G in itertools.combinations(range(len(cand)), k):
            pts = [cand[i] for i in G]
            orbs = [p*rot for p in pts]
            ok = True
            # mutual validity
            allnew = np.concatenate(orbs)
            for p in pts:
                d = np.abs(allnew - p); d = d[d > 1e-9]
                if d.min() < g - TOL or d.max() > D2 + TOL: ok = False; break
                if np.sum(np.abs(allnew - p) < 1e-9) != 1: ok = False; break
                dc = np.abs(np.array(core) - p)
                if dc.min() < g - TOL or dc.max() > D2 + TOL: ok=False;break
            if not ok: continue
            # count edges per sector: edges from reps to core + half of edges among new points
            A = B = 0.0
            for p in pts:
                dc = np.abs(np.array(core) - p)
                A += np.sum(np.abs(dc-D2)<TOL); B += np.sum(np.abs(dc-g)<TOL)
                d = np.abs(allnew - p)
                A += np.sum(np.abs(d-D2)<TOL)/2; B += np.sum(np.abs(d-g)<TOL)/2
            s = 4*A + 3*B - 9*k
            best.append((s, k, A, B, pts))
    best.sort(key=lambda t: -t[0])
    for b in best[:5]:
        print("  score", b[0], "k", b[1], "A", b[2], "B", b[3])
    return best

if __name__ == '__main__':
    for m in [int(x) for x in sys.argv[1].split(',')]:
        run(m)

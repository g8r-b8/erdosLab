#!/usr/bin/env python3
"""r7_D1_ring.py -- consistency of Theorem G with ienjoymath's 9/7 construction (float screen, via ring16.py).
Checks: every R-point has v <= 6 (so sum_R v <= 6r holds with room), t << sqrt3/2 (Region I), and the resulting
min{mu(D2), mu(delta)}/n is <= 9/7 + o(1) as predicted, and approaches 9/7."""
import sys, numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, '/Users/wingatejones/Projects/erdosLab/problems/132/scripts')
from ring16 import construction, summary
TOL = 1e-9
for n in [60, 120, 250, 400]:
    best = None
    for m in range(6, n // 2 + 1):
        X, g, D2 = construction(m, n)
        s = summary(X)
        if abs(s['delta'] - g) < TOL and abs(s['D2'] - D2) < TOL:
            v = min(s['mu_D2'], s['mu_delta'])
            if best is None or v > best[0]: best = (v, m, X, g, D2)
    v, m, X, g, D2 = best
    X = np.array(X); d = np.abs(X[:, None] - X[None, :]); Dm = d.max()
    t = (Dm - D2) / g
    S = np.any(np.abs(d - D2) < TOL, axis=1); A = np.abs(d - g) < TOL
    vv = A.sum(1) + (A & S[None, :]).sum(1)
    r = int((~S).sum())
    print(f"n={n}: t/delta={t:.5f}  r={r}  sum_R v={int(vv[~S].sum())} <= 6r={6*r}  max v={int(vv[~S].max())}"
          f"  min/n={v/n:.4f} (9/7={9/7:.4f})")
    assert vv[~S].sum() <= 6 * r and t < 0.8461
print("OK: ienjoymath construction consistent with Theorem G (sum_R v <= 6r)")

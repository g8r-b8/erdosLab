"""REF_core referee: patched copy of the visible-path harness l97A_vp_common.py.

Two changes (loaded by source patching, so the author's file is untouched):
  1. the assertion 'vertex visited twice' is removed: a vertex CAN be a corner twice
     (the "dip": L_i = R_i = v with a nearer vertex B_i below v on the same ray);
  2. the per-vertex check sums over corner OCCURRENCES:
       claim(v) = (2pi/3)[v in A] + sum_{occurrences} (2pi/3 - kappa) - overlap,
     which is what Step 7 needs when m counts occurrences.
  3. checks the endpoint-overlap bound |W_a ∩ H+_a| <= pi/2 + |alpha_a| ('ovl_bound_fail').
Also exports 'occ_max' = max number of corner occurrences of a single vertex.
"""
import os
import types

_src = open(os.path.join(os.path.dirname(__file__), 'l97A_vp_common.py')).read()
_src = _src.replace("    assert len(set(vids)) == len(vids), 'vertex visited twice'\n",
                    "    results['occ_max'] = max([vids.count(x) for x in set(vids)] + [0])\n")
_src = _src.replace("    kap = {c[0]: c[2] - c[1] for c in vc}\n",
                    "    kap = {}\n    for c in vc:\n        kap[c[0]] = kap.get(c[0], 0) + (TWOPI / 3 - (c[2] - c[1]))\n")
_src = _src.replace("            claim += TWOPI / 3 - kap[v] - ovl.get(v, 0)\n",
                    "            claim += kap[v] - ovl.get(v, 0)\n")
_src = _src.replace("    results['ovl_sum'] = sum(ovl.values()) if ovl else mp.mpf(0)\n",
                    "    results['ovl_sum'] = sum(ovl.values()) if ovl else mp.mpf(0)\n"
                    "    ovf, alm = 0, mp.mpf(0)\n"
                    "    for (v, pin, pout, nu, virt) in vc:\n"
                    "        if virt and v in Aset:\n"
                    "            w = min(Kreg.W, key=lambda w: abs(D2 - abs(pts[v] - w)))\n"
                    "            al = abs(mod2pi(ang(pts[v] - w) - nu + PI) - PI)\n"
                    "            alm = max(alm, al)\n"
                    "            if ovl[v] > PI / 2 + al + TOL:\n"
                    "                ovf += 1\n"
                    "    results['ovl_bound_fail'] = ovf\n"
                    "    results['alpha_max'] = alm\n")
assert "ovl_bound_fail" in _src
assert "vertex visited twice" not in _src and "claim += kap[v]" in _src
H = types.ModuleType('l97R_harness_impl')
H.__file__ = __file__
exec(compile(_src, 'l97A_vp_common[patched]', 'exec'), H.__dict__)

"""Streaming DIMACS writer for the weakened instance F_y(X) (soundness: see smooth_sat.py).

Improvements over smooth_sat.build: exponents reduced mod k (f only sees e mod k), chain nodes are
multisets of prime indices (ascending), memoised; run-members that are never a chain prefix get a
single z var.  Optional cube: extra unit clauses f(p)=v.
  python smooth_cnf.py k l y runs.txt out.cnf [--cube 2=0,3=1] [--maxr R] [--nosym]
"""
import argparse


def primes_upto(y):
    return [p for p in range(2, y + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def key_of(n, ps, k):
    key = []
    for i, p in enumerate(ps):
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p; e += 1
            key += [i] * (e % k)
        if n == 1:
            break
    assert n == 1, "not smooth"
    return tuple(key)


def write(k, l, y, rs, path, cube=(), sym=True):
    ps = primes_upto(y)
    members = []
    for r in rs:
        members.append([key_of(n, ps, k) for n in range(r, r + l)])
    # nodes: prefixes key[:j] for j>=2 (j=1 is a prime, j=0 is 1)
    full, zonly = set(), set()
    for tri in members:
        for key in tri:
            for j in range(2, len(key)):
                full.add(key[:j])
    for tri in members:
        for key in tri:
            if len(key) >= 2 and key not in full:
                zonly.add(key)
    nv = 0
    pb = []
    for i in range(len(ps)):
        pb.append(nv + 1); nv += k + (1 if sym else 0)
    base = {}
    for key in sorted(full, key=len):
        base[key] = nv + 1; nv += k
    for key in zonly:
        base[key] = nv + 1; nv += 1

    def z(key):
        if len(key) == 0:
            return None                     # f = 0 constant true
        if len(key) == 1:
            return pb[key[0]]
        return base[key]

    def val(key):                           # base var of the one-hot block of a full node
        return pb[key[0]] if len(key) == 1 else base[key]

    lines = []
    allowed = {d for d in range(1, k) if k % d == 0}
    sprev = None
    for i in range(len(ps)):
        b = pb[i]
        lines.append([b + v for v in range(k)])
        lines += [[-(b + a), -(b + c)] for a in range(k) for c in range(a + 1, k)]
        if sym:
            s = b + k
            for v in range(1, k):
                if v not in allowed:
                    lines.append([-(b + v)] + ([sprev] if sprev else []))
            lines.append([-s, -b] + ([sprev] if sprev else []))
            if sprev:
                lines.append([-sprev, s])
            lines.append([b, s])
            sprev = s
    for key in sorted(full, key=len):
        b = base[key]; bm = val(key[:-1]); bp = pb[key[-1]]
        lines.append([b + v for v in range(k)])
        lines += [[-(b + a), -(b + c)] for a in range(k) for c in range(a + 1, k)]
        for a in range(k):
            for c in range(k):
                lines.append([-(bp + a), -(bm + c), b + (a + c) % k])
    for key in zonly:
        zb = base[key]; bm = val(key[:-1]); bp = pb[key[-1]]
        for a in range(k):
            lines.append([-(bp + a), -(bm + (-a) % k), zb])
    for tri in members:
        c = []
        for key in tri:
            zz = z(key)
            if zz is not None:
                c.append(-zz)
        lines.append(c)
    for p, v in cube:
        lines.append([pb[ps.index(p)] + v])
    with open(path, "w") as fh:
        fh.write(f"p cnf {nv} {len(lines)}\n")
        for c in lines:
            fh.write(" ".join(map(str, c)) + " 0\n")
    return nv, len(lines), len(full), len(zonly), pb, ps


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int); ap.add_argument("l", type=int); ap.add_argument("y", type=int)
    ap.add_argument("runs"); ap.add_argument("out")
    ap.add_argument("--cube", default=""); ap.add_argument("--maxr", type=int); ap.add_argument("--nosym", action="store_true")
    a = ap.parse_args()
    rs = [int(x) for x in open(a.runs)]
    if a.maxr:
        rs = [r for r in rs if r <= a.maxr]
    cube = [tuple(map(int, t.split("="))) for t in a.cube.split(",") if t]
    nv, nc, nf, nz, pb, ps = write(a.k, a.l, a.y, rs, a.out, cube, not a.nosym)
    print(f"k={a.k} l={a.l} y={a.y} runs={len(rs)} maxr={max(rs)} vars={nv} clauses={nc} full={nf} z={nz} cube={cube}")
    with open(a.out + ".map", "w") as fh:
        for p, b in zip(ps, pb):
            fh.write(f"{p} {b}\n")

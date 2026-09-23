"""Weakened SAT instance F_y(X) for Lambda_comb(k, l): variables = f(p) for primes p <= y only;
constraints = the l-runs r, ..., r+l-1 <= X+l-1 consisting of y-smooth numbers (from smoothruns).

Soundness: any completely additive f with no zero l-run starting at r <= X restricts to a model of
F_y(X) (we only dropped run-clauses).  Hence UNSAT(F_y(X)) => Lambda_comb(k,l) <= max r used <= X.

  python smooth_sat.py k l y runs.txt [--dimacs out.cnf] [--maxr R]
"""
import argparse, sys, time


def primes_upto(y):
    return [p for p in range(2, y + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def factor_lpf(n, ps):
    """largest prime factor of y-smooth n (ps ascending)."""
    for p in reversed(ps):
        if n % p == 0:
            return p
    raise ValueError(n)


def build(k, l, y, rs, sym=True):
    ps = primes_upto(y)
    nv = 0
    base = {}
    cl = []
    sprev = None
    allowed = {d for d in range(1, k) if k % d == 0}
    for p in ps:
        b = nv + 1; nv += k; base[p] = b
        cl.append([b + v for v in range(k)])
        cl += [[-(b + i), -(b + j)] for i in range(k) for j in range(i + 1, k)]
        if sym:
            nv += 1; s = nv
            for v in range(1, k):
                if v not in allowed:
                    cl.append([-(b + v)] + ([sprev] if sprev else []))
            cl.append([-s, -b] + ([sprev] if sprev else []))
            if sprev:
                cl.append([-sprev, s])
            cl.append([b, s])
            sprev = s
    # needed nodes: members and their chains
    members = sorted({r + i for r in rs for i in range(l)})
    need = set()
    for n in members:
        m = n
        while m > 1 and m not in need:
            need.add(m)
            m //= factor_lpf(m, ps)
    for n in sorted(need):
        if n in base:
            continue
        P = factor_lpf(n, ps); m = n // P
        b = nv + 1; nv += k; base[n] = b
        cl.append([b + v for v in range(k)])
        cl += [[-(b + i), -(b + j)] for i in range(k) for j in range(i + 1, k)]
        bp, bm = base[P], (base[m] if m > 1 else None)
        if bm is None:
            raise AssertionError
        for a in range(k):
            for c in range(k):
                cl.append([-(bp + a), -(bm + c), b + (a + c) % k])
    for r in rs:
        cl.append([-base[n] for n in range(r, r + l) if n != 1])
    return nv, cl, base, ps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int); ap.add_argument("l", type=int); ap.add_argument("y", type=int)
    ap.add_argument("runs"); ap.add_argument("--dimacs"); ap.add_argument("--maxr", type=int)
    a = ap.parse_args()
    rs = [int(x) for x in open(a.runs)]
    if a.maxr:
        rs = [r for r in rs if r <= a.maxr]
    t0 = time.time()
    nv, cl, base, ps = build(a.k, a.l, a.y, rs)
    print(f"k={a.k} l={a.l} y={a.y} runs={len(rs)} maxr={max(rs)} primes={len(ps)} vars={nv} clauses={len(cl)} build={time.time()-t0:.1f}s", flush=True)
    if a.dimacs:
        with open(a.dimacs, "w") as fh:
            fh.write(f"p cnf {nv} {len(cl)}\n")
            fh.write("".join(" ".join(map(str, c)) + " 0\n" for c in cl))
        return
    from pysat.solvers import Cadical153
    S = Cadical153(bootstrap_with=cl)
    ok = S.solve()
    print("SAT" if ok else "UNSAT", f"solve={time.time()-t0:.1f}s", flush=True)
    if ok:
        pos = set(x for x in S.get_model() if x > 0)
        f = {p: [v for v in range(a.k) if base[p] + v in pos][0] for p in ps}
        print("f on primes:", " ".join(f"{p}:{f[p]}" for p in ps))


if __name__ == "__main__":
    main()

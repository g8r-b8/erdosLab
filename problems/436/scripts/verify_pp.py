"""Independent segmented verifier of a lower-bound witness for Lambda_comb(k,3) (shares no code with lamenc/warmls/checkf/segcheck).

  python3 verify_pp.py K 3 LIM MAP MODEL [BLOCK]

MAP: "p base" lines; MODEL: solver "v" lines; f(p)=v iff literal base+v is true (exactly one, asserted); unmapped primes get f=1.
Checks the mapped numbers are prime, then for n in blocks divides out primes p <= sqrt(LIM+3) (adding e*f(p)); the cofactor left is 1
or one prime P (add f(P)). Prints the first r <= LIM with f(r)=f(r+1)=f(r+2)=0 (mod K). Memory ~1.3 GB at BLOCK=1e7.
Witness check: python3 verify_pp.py 5 3 1000007600 <(xz -dc ../witnesses/k5l3_first1000007372.map.xz) <(xz -dc ../witnesses/k5l3_first1000007372.model.xz) 10000000
"""
# Segmented independent check: for n in blocks, divide out primes p <= sqrt(M) (adding e*f(p)); leftover cofactor is 1 or one prime P.
# f(p) from MAP/MODEL (exactly one true value literal per mapped prime), unmapped primes -> 1. Prints first r with f(r)=f(r+1)=f(r+2)=0.
import sys, numpy as np
k, l, lim, mapf, modf = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
assert l == 3
M = lim + l; S = int(sys.argv[6]) if len(sys.argv) > 6 else 10**7
pos = set()
for line in open(modf):
    for t in line.split()[1:]:
        v = int(t)
        if v > 0: pos.add(v)
mp, mv = [], []
for line in open(mapf):
    p, b = map(int, line.split())
    hits = [v for v in range(k) if b + v in pos]
    assert len(hits) == 1, (p, hits)
    mp.append(p); mv.append(hits[0])
order = np.argsort(mp); mp = np.array(mp, np.int64)[order]; mv = np.array(mv, np.int64)[order]
def fval(P):  # vectorised f on primes
    i = np.searchsorted(mp, P); i = np.minimum(i, len(mp) - 1)
    return np.where(mp[i] == P, mv[i], 1)
sq = int(M**0.5) + 1
isp = np.ones(sq + 1, bool); isp[:2] = False
for i in range(2, int(sq**0.5) + 1):
    if isp[i]: isp[i*i::i] = False
small = np.nonzero(isp)[0]; fsmall = fval(small)
# mapped primes must be prime: check small ones by table, larger by trial division against small primes
for p in mp:
    if p <= sq: assert isp[p], p
    else: assert all(p % q for q in small if q*q <= p), p
prev = [False, False]  # zero flags of the two numbers before the block
a = 1
while a <= M:
    b = min(a + S, M + 1)
    n = np.arange(a, b, dtype=np.int64); rem = n.copy(); f = np.zeros(b - a, np.int64)
    for p, fp in zip(small, fsmall):
        p = int(p); start = (-a) % p
        idx = np.arange(start, b - a, p)
        while idx.size:
            rem[idx] //= p; f[idx] += fp
            idx = idx[rem[idx] % p == 0]
    big = rem > 1
    f[big] += fval(rem[big])
    z = np.concatenate([prev, (f % k) == 0])
    run = z[:-2] & z[1:-1] & z[2:]          # run[j] <=> n = a-2+j .. a+j zero
    hit = np.nonzero(run)[0]
    if hit.size:
        r = a - 2 + int(hit[0])
        if r >= 1: print("first_run", r); sys.exit(0)
    prev = list(z[-2:]); a = b
print(f"first_run NONE<={lim}")

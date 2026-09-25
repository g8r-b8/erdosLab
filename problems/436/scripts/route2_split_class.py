#!/usr/bin/env python3
"""route2: exact check of Theorem R2.3 (split-prime class) on explicit examples.

f = additive version of g (g = zeta^f), values in Z/5.
Class R: f(p) = c_chi(p) for all primes p = 1 mod 5 outside a finite set E,
arbitrary (here: pseudo-random) on all other primes.

For m = 0 mod Q (Q = 5 * q * prod(E)) the theorem says:
  f(m^5) = 0, f(Phi5(m)) = f(Phi10(m)) = 0,
so n = m^5 - 1 is a zero run iff f(m-1) = f(m+1) = 0.
We verify every step exactly with PARI/gp factorisations (gp must be on PATH):
  (1) every prime of Phi5(m), Phi10(m) is = 1 mod 5 and outside E, and Phi5, Phi10 = 1 mod q;
  (2) f(Phi5(m)) = f(Phi10(m)) = 0;
  (3) for good m, f(m^5-1) = f(m^5+1) = 0 from the full factorisation of m^5 +- 1;
  (4) the fraction of good m (expected 1/25 by Tao's two-point log-Elliott, heuristically also Cesaro).
Light: about 2000 factorisations of numbers < 10^21.  Run: python3 route2_split_class.py
"""
import hashlib, subprocess, sys, tempfile, os

def rnd(p, salt):
    return int(hashlib.sha256(f"{salt}:{p}".encode()).hexdigest(), 16) % 5

def gp_factor_batch(nums):
    """Return list of factorisations [(p,e),...] for nums, via one gp call (file input)."""
    with tempfile.NamedTemporaryFile("w", suffix=".gp", delete=False) as fh:
        fh.write("default(parisize,100000000);\n")
        for n in nums:
            fh.write(f"{{my(F=factor({n}));print(vector(#F~,i,[F[i,1],F[i,2]]))}}\n")
        fh.write("quit\n")
        path = fh.name
    out = subprocess.run(["gp", "-q", "-f", path], capture_output=True, text=True, check=True).stdout
    os.unlink(path)
    res = []
    for line in out.strip().splitlines():
        line = line.strip()
        if line == "[]":
            res.append([]); continue
        pairs = line[2:-2].split("], [")
        res.append([tuple(int(t) for t in pr.split(", ")) for pr in pairs])
    assert len(res) == len(nums), (len(res), len(nums))
    return res

def fval(fac, f):
    return sum(e * f(p) for p, e in fac) % 5

def run(name, f, Q, q, E, chi_ok, K):
    ms = [Q * k for k in range(1, K + 1)]
    phi5 = lambda m: m**4 + m**3 + m**2 + m + 1
    phi10 = lambda m: m**4 - m**3 + m**2 - m + 1
    nums = []
    for m in ms:
        nums += [m - 1, m + 1, phi5(m), phi10(m)]
    facs = gp_factor_batch(nums)
    good = []
    for i, m in enumerate(ms):
        fm1, fp1, f5, f10 = facs[4*i:4*i+4]
        for fac, val in ((f5, phi5(m)), (f10, phi10(m))):
            assert all(p % 5 == 1 and p not in E for p, _ in fac), (m, fac)
            assert val % q == 1 % q
            assert chi_ok(fac)
            assert fval(fac, f) == 0, (m, fac)
        if fval(fm1, f) == 0 and fval(fp1, f) == 0:
            good.append(m)
    # (3) independent confirmation on full factorisations of m^5 -+ 1 for the good m
    conf = gp_factor_batch([x for m in good for x in (m**5 - 1, m**5 + 1)])
    for j, m in enumerate(good):
        assert fval(conf[2*j], f) == 0 and fval(conf[2*j+1], f) == 0, m
    print(f"[{name}] Q={Q}: m = Q*k, k<={K}: all Phi5/Phi10 checks pass; "
          f"good m: {len(good)} / {K} = {len(good)/K:.4f} (1/25 = 0.04); "
          f"first good m = {good[:3]}; zero runs n = m^5-1 verified from full factorisations: {len(good)}")
    return good

def main():
    # Example 1: f = 0 on split primes, random elsewhere (g in case C: g(p) random on 3/4 of primes)
    f1 = lambda p: 0 if p % 5 == 1 else rnd(p, "ex1")
    run("ex1 chi=1, E={}", f1, 5, 1, set(), lambda fac: True, 2000)
    # Example 2: chi = order-5 character mod 11 on split primes, finite exception set E={11,31,41,61}
    # (11 is split itself; it lies in E via Q anyway), random values on E and on non-split primes.
    ind = {pow(2, j, 11): j for j in range(10)}
    chi = lambda p: 0 if p == 11 else ind[p % 11] % 5
    E = {31, 41, 61}
    def f2(p):
        if p % 5 == 1 and p not in E and p != 11:
            return chi(p)
        return rnd(p, "ex2")
    Q = 5 * 11 * 31 * 41 * 61
    run("ex2 chi mod 11, E={31,41,61}", f2, Q, 11, E | {11}, lambda fac: sum(e*chi(p) for p, e in fac) % 5 == 0, 1500)

if __name__ == "__main__":
    main()

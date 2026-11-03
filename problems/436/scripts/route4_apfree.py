#!/usr/bin/env python3
"""Route 4 side check: is there a completely additive f: N -> Z/5 with
        f(n) - 2 f(n+1) + f(n+2) != 0   for all n <= X ?
(equivalently g = zeta^f completely multiplicative with g(n) g(n+2) != g(n+1)^2).

Such an f is exactly a 'pointwise self-similar second-difference sequence' D = Delta^2 f with values
in (Z/5)^x (route4_selfsimilar.md, Remark R4.10).  Plain DFS over primes in increasing order,
checking each constraint n as soon as all primes of n(n+1)(n+2) are assigned; values are normalised
by scaling (first nonzero value = 1).  Prints the number of surviving assignments per prime level and
whether the instance is UNSAT (then no such f exists, with certificate bound X).

Usage: python3 route4_apfree.py [X]
"""
import sys


def main() -> None:
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    L = X + 3
    spf = list(range(L))
    for p in range(2, int(L ** 0.5) + 1):
        if spf[p] == p:
            for k in range(p * p, L, p):
                if spf[k] == k:
                    spf[k] = p
    primes = [p for p in range(2, L) if spf[p] == p]
    idx = {p: i for i, p in enumerate(primes)}

    def fac(n):
        out = []
        while n > 1:
            p = spf[n]
            out.append(p)
            n //= p
        return out

    # constraint n is checked at level = index of the largest prime among n, n+1, n+2
    cons = [[] for _ in primes]
    for n in range(1, X + 1):
        fs = [fac(n), fac(n + 1), fac(n + 2)]
        allp = [p for f in fs for p in f]
        if not allp:
            continue
        lvl = max(idx[p] for p in allp)
        cons[lvl].append(fs)

    val = [0] * len(primes)
    counts = [0] * (len(primes) + 1)

    def F(fl):
        return sum(val[idx[p]] for p in fl) % 5

    sys.setrecursionlimit(10000)

    def dfs(i, seen_nonzero):
        counts[i] += 1
        if i == len(primes):
            return True
        choices = range(5) if seen_nonzero else (0, 1)
        for v in choices:
            val[i] = v
            ok = True
            for fs in cons[i]:
                if (F(fs[0]) - 2 * F(fs[1]) + F(fs[2])) % 5 == 0:
                    ok = False
                    break
            if ok and dfs(i + 1, seen_nonzero or v != 0):
                return True
        val[i] = 0
        return False

    found = dfs(0, False)
    print(f"X = {X}, primes = {len(primes)}")
    print("nodes visited per level:", counts[:40])
    if found:
        print("SAT: example f on primes:", {p: val[idx[p]] for p in primes[:25]})
    else:
        print("UNSAT: every completely additive f: N -> Z/5 has n <= X with f(n)+f(n+2) = 2f(n+1)")


if __name__ == "__main__":
    main()

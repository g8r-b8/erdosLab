#!/usr/bin/env python3
"""route2: how many 'free' constraints does the fifth-power trick add to a smooth instance?

Lemma R2.4 (Thue): for a finite prime set S only finitely many n have n, n+1 both in
<S> * (N)^5 (S-unit times a fifth power).  So pigeonhole over families whose g-values
depend only on g|S is a finite CSP on the S-primes.  This scan lists, for S = primes <= 13,
every pair/triple of consecutive integers in <S>*N^5 in which at least one member has a
non-S part z^5 with z > 1, with that member <= 10^18.  (Pairs/triples of plain S-smooth
numbers are the usual F_y constraints and are not listed.)
Run: python3 route2_thue_scan.py     (about 1 min, < 50 MB)
"""
S = [2, 3, 5, 7, 11, 13]
LIM = 10**18

def iroot5(x):
    r = int(round(x ** 0.2))
    for c in (r - 1, r, r + 1):
        if c >= 0 and c**5 == x:
            return c
    return None

def sfree(x):
    for p in S:
        while x % p == 0:
            x //= p
    return x

def in_class(x):
    if x <= 0:
        return False
    return iroot5(sfree(x)) is not None

def smooth_upto(B):
    out = [1]
    for p in S:
        new = []
        for s in out:
            t = s
            while t <= B:
                new.append(t); t *= p
        out = new
    return sorted(out)

def main():
    smooth = smooth_upto(LIM // 2**5)
    zs = [z for z in range(2, int(LIM ** 0.2) + 2) if sfree(z) == z]
    pairs, triples = set(), set()
    for z in zs:
        z5 = z**5
        for s in smooth:
            M = s * z5
            if M > LIM:
                break
            for d in (-1, 1):
                if in_class(M + d):
                    pairs.add(min(M, M + d))
            for n in (M - 2, M - 1, M):
                if n >= 1 and all(in_class(n + i) for i in range(3)):
                    triples.add(n)
    print(f"S={S}, member <= 1e18 with fifth-power cofactor z^5, z>1 coprime to S:")
    print(f"  consecutive pairs found: {len(pairs)}  -> {sorted(pairs)[:20]}")
    print(f"  consecutive triples found: {len(triples)} -> {sorted(triples)}")
    for n in sorted(pairs)[:20]:
        print("   ", n, [(n + i, sfree(n + i)) for i in range(2)])

if __name__ == "__main__":
    main()

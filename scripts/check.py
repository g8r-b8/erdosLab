# For each K, count N<=X that are prefix sums (divisors >1, increasing) of some n with K*n <= N.
import sys
X=int(sys.argv[1])
divs=[[] for _ in range(X+1)]
for d in range(2,X+1):
    for m in range(d,X+1,d): divs[m].append(d)
for K in (1,2,3,4):
    hit=bytearray(X+1); pairs=0
    for n in range(1,X//K+1):
        s=0
        for d in divs[n]:
            s+=d
            if s>X: break
            if s>=K*n: hit[s]=1; pairs+=1
    c=sum(hit)
    print(f"K={K}: covered {c}/{X} = {c/X:.4f}; pairs/X={pairs/X:.4f}; bound C0/K^2 = {3.95/K**2:.4f}")

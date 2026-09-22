import sys
X=int(sys.argv[1]); M=int(sys.argv[2])*X
# smallest-prime-factor sieve up to M, then enumerate divisors <= X of each n <= M
import math
spf=list(range(M+1))
for i in range(2,int(M**0.5)+1):
    if spf[i]==i:
        for j in range(i*i,M+1,i):
            if spf[j]==j: spf[j]=i
rep=bytearray(X)
for n in range(2,M+1):
    # divisors of n up to X
    m=n; ds=[1]
    while m>1:
        p=spf[m]; e=0
        while m%p==0: m//=p; e+=1
        ds=[d*p**k for d in ds for k in range(e+1) if d*p**k<X]
    ds.sort(); s=0
    for d in ds[1:]:
        s+=d
        if s>=X: break
        rep[s]=1
    if n%1000000==0: print(n, sum(rep)/X, flush=True)
print("X",X,"n<=",M,"representable fraction",sum(rep)/X)

import math
X=10**7
import sys
# sieve
b=bytearray([1])*(X+1); b[0]=b[1]=0
for i in range(2,int(X**.5)+1):
    if b[i]: b[i*i::i]=bytearray(len(range(i*i,X+1,i)))
primes=[i for i in range(X+1) if b[i]]
R=bytearray(X+1)
for k in range(0,40):
    s=2**(k+1)-2; lo=2**k
    if lo+s>X: break
    for p in primes:
        if p<=lo: continue
        N=p+s
        if N>X: break
        R[N]=1
# also Romanov set p+2^j, j>=1
A=bytearray(X+1)
for j in range(1,40):
    if 2**j>X: break
    for p in primes:
        N=p+2**j
        if N>X: break
        A[N]=1
S=3.95
for x in [10**4,10**5,10**6,10**7]:
    r=sum(R[:x]); a=sum(A[:x])
    print(f"X={x:>9} dens R'={r/x:.4f}  dens(p+2^j)={a/x:.4f}")
d=sum(R[:X])/X
for K in [3,4,5,6,8]:
    print(f"K={K}: S/K^2={S/K**2:.4f}  vs delta={d:.4f}  delta - S/K^2={d-S/K**2:.4f}")

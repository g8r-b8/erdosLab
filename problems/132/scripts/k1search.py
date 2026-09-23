"""DFS search for strictly convex n-sets in cyclotomic pools with D <= target distinct distances.
Reports multiplicity profiles and #rare (mult <= n).  Usage: k1search.py N depth R n target
Pool: sums sum_k c_k zeta_N^k, |c_k|<=depth, k<phi-range, |z|<=R, canonical first point 0 (lowest (y,x))."""
import sys, itertools, cmath, math
from collections import Counter
N=int(sys.argv[1]); dep=int(sys.argv[2]); R=float(sys.argv[3]); n=int(sys.argv[4]); target=int(sys.argv[5])
maxout=int(sys.argv[6]) if len(sys.argv)>6 else 50
z=cmath.exp(2j*math.pi/N)
basis={3:2,4:2,6:2,12:4,5:4,10:4,8:4,7:6,9:6,18:6,14:6,15:8,16:8,20:8,24:8,30:8}[N]
pts={}
for c in itertools.product(range(-dep,dep+1),repeat=basis):
    p=sum(ci*z**k for k,ci in enumerate(c))
    if abs(p)<=R+1e-9:
        key=(round(p.real,7),round(p.imag,7))
        pts[key]=p
pool=[p for k,p in pts.items() if (k[1]>1e-9 or (abs(k[1])<1e-9 and k[0]>1e-9))]
pool.sort(key=lambda p:(round(p.imag,7),round(p.real,7)))
P=[0j]+pool; M=len(P)
did={}
def dkey(a,b):
    k=round(abs(a-b)**2,6)
    if k not in did: did[k]=len(did)
    return did[k]
DM=[[dkey(P[i],P[j]) if i!=j else -1 for j in range(M)] for i in range(M)]
def cross(o,a,b): return (a.real-o.real)*(b.imag-o.imag)-(a.imag-o.imag)*(b.real-o.real)
def strictly_convex(S):
    Q=[P[i] for i in S]
    if len(Q)<3: return True
    c=sum(Q)/len(Q)
    Q.sort(key=lambda p:cmath.phase(p-c))
    m=len(Q)
    for i in range(m):
        if cross(Q[i],Q[(i+1)%m],Q[(i+2)%m])<=1e-9: return False
    return True
found=0; seen=set()
def canon(S):
    # translation/rotation canonical form via sorted multiset of distance-structure? use rounded sorted coords after normalization: skip, use distance profile+sorted pairwise
    ds=sorted(round(abs(P[i]-P[j])**2,5) for i,j in itertools.combinations(S,2))
    return tuple(ds)
def dfs(S,ds,start):
    global found
    if len(S)==n:
        c=Counter(DM[i][j] for i,j in itertools.combinations(S,2))
        key=canon(S)
        if key in seen: return
        seen.add(key)
        prof=sorted(((round(math.sqrt([k for k,v in did.items() if v==d][0]),5),m) for d,m in c.items()),reverse=True)
        rare=sum(1 for _,m in prof if m<=n)
        cc=None
        print('D=%d rare=%d prof=%s pts=%s'%(len(c),rare,[m for _,m in prof],[ (round(P[i].real,4),round(P[i].imag,4)) for i in S]),flush=True)
        found+=1
        if found>=maxout: raise SystemExit
        return
    for j in range(start,M):
        nd=set(ds)
        for i in S: nd.add(DM[i][j])
        if len(nd)>target: continue
        S2=S+[j]
        if not strictly_convex(S2): continue
        dfs(S2,nd,j+1)
print('pool',M,flush=True)
dfs([0],set(),1)
print('done found',found)

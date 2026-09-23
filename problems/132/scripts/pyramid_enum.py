"""Ordinal pyramid enumeration.  Points 1..r on a convex chain cut off by a diameter; entries L(s,t), 1<=s<t<=r,
are length RANKS in {1..V} (larger = longer).  Altman Lemma 1 (ordinal): for s<u, t<v, s<t, u<v:
      L(s,v) > min(L(s,t), L(u,v)).
Row mins are strictly increasing => V >= r-1.  Question: when V = r-1 (tight), are rows forced constant?"""
import itertools, sys
r=int(sys.argv[1]); V=int(sys.argv[2]) if len(sys.argv)>2 else r-1
pairs=[(s,t) for t in range(1,r+1) for s in range(1,t)]
# order pairs by row (t-s) so constraints can be checked incrementally: L(s,v) depends on shorter pairs
pairs.sort(key=lambda p:(p[1]-p[0],p[0]))
cons={p:[] for p in pairs}
for (s,t) in pairs:
    for (u,v) in pairs:
        if s<u and t<v:
            cons[(s,v)].append(((s,t),(u,v)))
sols=[]
L={}
def rec(k):
    if k==len(pairs):
        sols.append(dict(L)); return
    p=pairs[k]
    lo=1
    for a,b in cons[p]:
        lo=max(lo,min(L[a],L[b])+1)
    for val in range(lo,V+1):
        L[p]=val; rec(k+1)
    L.pop(p,None)
rec(0)
def rows(S):
    return [[S[(i,i+j)] for i in range(1,r-j+1)] for j in range(1,r)]
nc=[S for S in sols if any(len(set(row))>1 for row in rows(S))]
print('r',r,'V',V,'solutions',len(sols),'non-row-constant',len(nc))
for S in nc[:15]: print(rows(S))

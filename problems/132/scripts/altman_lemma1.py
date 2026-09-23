"""Numerical test of Altman's Lemma 1 (1972): P convex, A=B_0, B=B_{r+1} a diameter of P, B_1..B_r the
vertices strictly on one side.  For s<u, t<v (s<t, u<v, (s,v)!=(0,r+1)):
     |B_s B_v| > min(|B_s B_t|, |B_u B_v|).
Test on random convex polygons (points on random convex curves), all chains on both sides of a diameter."""
import numpy as np, itertools, sys
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def rand_convex(n):
    # random convex polygon: sort random unit vectors, cumulative sum (Valtr-like)
    while True:
        v=rng.normal(size=(n,2)); v-=v.mean(0)
        ang=np.arctan2(v[:,1],v[:,0]); v=v[np.argsort(ang)]
        P=np.cumsum(v,0)
        # strictly convex check
        ok=True
        for i in range(n):
            a,b,c=P[i],P[(i+1)%n],P[(i+2)%n]
            if (b-a)[0]*(c-b)[1]-(b-a)[1]*(c-b)[0]<=1e-9: ok=False;break
        if ok: return P
bad=0; tests=0
for trial in range(3000):
    n=int(rng.integers(5,12)); P=rand_convex(n)
    D=np.linalg.norm(P[:,None]-P[None],axis=2)
    i0,j0=np.unravel_index(np.argmax(D),D.shape)
    for side in (0,1):
        if side==0: idx=[(i0+k)%n for k in range((j0-i0)%n+1)]
        else: idx=[(j0+k)%n for k in range((i0-j0)%n+1)]
        L=len(idx)-1  # B_0..B_L
        C=D[np.ix_(idx,idx)]
        for s,t,u,v in itertools.product(range(L+1),repeat=4):
            if not (s<u and t<v and s<t and u<v): continue
            if (s,v)==(0,L): continue
            tests+=1
            if not C[s,v]>min(C[s,t],C[u,v])-1e-12:
                bad+=1
                if bad<5: print('viol',n,L,(s,t,u,v),C[s,v],C[s,t],C[u,v])
print('tests',tests,'violations',bad)

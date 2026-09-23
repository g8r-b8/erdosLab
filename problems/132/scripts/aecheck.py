"""AE' check (extended Cap Lemma for gapped regular polygons).
V = vertices of R_N on the unit circle.  A = V minus the s-1 consecutive vertices x_1..x_{s-1} (a hole of
size s-1, s>=1; s=1 is the ordinary Cap Lemma).  A point u is admissible if A u {u} is strictly convex and u
lies beyond the hull edge x_0 x_s, i.e. in the open cap bounded by line x_0x_s and lines x_{-1}x_0, x_s x_{s+1}.
We enumerate ALL points u at chord distance from >= 2 vertices of A (pairwise circle intersections),
keep admissible u not on the circle, and report max #hits = #{x in A : |u-x| is a chord of R_N},
and the number of distinct chord classes hit.  Points with <=1 hit are irrelevant (hits<=1).
Usage: aecheck.py Nmin Nmax smax"""
import numpy as np, math, sys
Nmin,Nmax,smax=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
def side(a,b,p): return (b[0]-a[0])*(p[...,1]-a[1])-(b[1]-a[1])*(p[...,0]-a[0])
for N in range(Nmin,Nmax+1):
    V=np.array([(math.cos(2*math.pi*i/N),math.sin(2*math.pi*i/N)) for i in range(N)])
    ch=np.array(sorted(set(np.round([2*math.sin(math.pi*j/N) for j in range(1,N//2+1)],12))))
    out=[]
    for s in range(1,smax+1):
        hole=set(range(1,s)); Aidx=[i for i in range(N) if i not in hole]; A=V[Aidx]
        x0,xs,xm1,xs1=V[0],V[s],V[-1],V[(s+1)%N]
        pts=[]
        for ia in range(len(Aidx)):
            for ib in range(ia+1,len(Aidx)):
                c1,c2=A[ia],A[ib]; d=np.linalg.norm(c2-c1)
                r1=ch[:,None]; r2=ch[None,:]
                a=(r1*r1-r2*r2+d*d)/(2*d); h2=r1*r1-a*a
                ok=h2>=-1e-12; h=np.sqrt(np.maximum(h2,0))
                e=(c2-c1)/d; perp=np.array([-e[1],e[0]])
                for sg in (1,-1):
                    P=c1[None,None,:]+a[...,None]*e+sg*h[...,None]*perp
                    P=P[ok]
                    pts.append(P)
        P=np.concatenate(pts)
        nr=np.linalg.norm(P,axis=1)
        P=P[np.abs(nr-1)>1e-9]
        # admissible cap: strictly outside line x0 xs (away from centre), strictly inside lines x_{-1}x0 and xs x_{s+1}
        o=np.zeros(2)
        s0=side(x0,xs,P); so=side(x0,xs,o[None,:])[0]
        s1=side(xm1,x0,P); s1o=side(xm1,x0,o[None,:])[0]
        s2=side(xs,xs1,P); s2o=side(xs,xs1,o[None,:])[0]
        m=(s0*so< -1e-12)&(s1*s1o>1e-12)&(s2*s2o>1e-12)
        P=P[m]
        if len(P)==0: out.append((s,0,0));continue
        P=np.unique(np.round(P,9),axis=0)
        Dm=np.linalg.norm(P[:,None,:]-A[None,:,:],axis=2)
        err=np.min(np.abs(Dm[...,None]-ch[None,None,:]),axis=2)
        hit=err<1e-8
        hits=hit.sum(1)
        cls=np.argmin(np.abs(Dm[...,None]-ch[None,None,:]),axis=2)
        k=np.argmax(hits)
        ncls=len(set(cls[k][hit[k]]))
        out.append((s,int(hits.max()),ncls))
    print(N,' '.join('s=%d:max_hits=%d(classes %d)'%t for t in out),flush=True)

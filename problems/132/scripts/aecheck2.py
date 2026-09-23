"""AE' check, general local cap.  V = R_N.  The hull edge x_0 x_s (holes x_1..x_{s-1}) has neighbouring hull
edges x_{-t1} x_0 and x_s x_{s+t2} (holes x_{-t1+1}..x_{-1} and x_{s+1}..x_{s+t2-1}).  A = V minus all these holes.
Admissible u: strictly beyond line x_0x_s, strictly inside lines x_{-t1}x_0 and x_s x_{s+t2}, u not on the circle.
Report max #{x in A: |u-x| chord of R_N} over u at chord distance from >=2 points of A.
Usage: aecheck2.py Nmin Nmax gmax   (all s,t1,t2>=1 with total holes (s-1)+(t1-1)+(t2-1) <= gmax)"""
import numpy as np, math, sys
Nmin,Nmax,gmax=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
def side(a,b,p): return (b[0]-a[0])*(p[...,1]-a[1])-(b[1]-a[1])*(p[...,0]-a[0])
for N in range(Nmin,Nmax+1):
    V=np.array([(math.cos(2*math.pi*i/N),math.sin(2*math.pi*i/N)) for i in range(N)])
    ch=np.array(sorted(set(np.round([2*math.sin(math.pi*j/N) for j in range(1,N//2+1)],12))))
    # all pairwise intersection points of circles centred at V with chord radii (compute once)
    pts=[]; src=[]
    for ia in range(N):
        for ib in range(ia+1,N):
            c1,c2=V[ia],V[ib]; d=np.linalg.norm(c2-c1)
            r1=ch[:,None]; r2=ch[None,:]
            a=(r1*r1-r2*r2+d*d)/(2*d); h2=r1*r1-a*a
            ok=h2>=-1e-12; h=np.sqrt(np.maximum(h2,0))
            e=(c2-c1)/d; perp=np.array([-e[1],e[0]])
            for sg in (1,-1):
                P=c1[None,None,:]+a[...,None]*e+sg*h[...,None]*perp
                pts.append(P[ok]); src.append(np.tile([ia,ib],(ok.sum(),1)))
    P=np.concatenate(pts); S=np.concatenate(src)
    keep=np.abs(np.linalg.norm(P,axis=1)-1)>1e-9
    P=P[keep]; S=S[keep]
    Dm=np.linalg.norm(P[:,None,:]-V[None,:,:],axis=2)
    hitV=np.min(np.abs(Dm[...,None]-ch[None,None,:]),axis=2)<1e-8
    worst=(0,None)
    for s in range(1,gmax+2):
        for t1 in range(1,gmax+2):
            for t2 in range(1,gmax+2):
                g=(s-1)+(t1-1)+(t2-1)
                if g>gmax or s+t1+t2>=N-2: continue
                holes=set(range(1,s))|set(range(N-t1+1,N))|set(range(s+1,s+t2))
                Amask=np.array([i not in holes for i in range(N)])
                x0,xs,xl,xr=V[0],V[s],V[(-t1)%N],V[(s+t2)%N]; o=np.zeros((1,2))
                m=(side(x0,xs,P)*side(x0,xs,o)[0]< -1e-12)&(side(xl,x0,P)*side(xl,x0,o)[0]>1e-12)&(side(xs,xr,P)*side(xs,xr,o)[0]>1e-12)
                # the two generating centres must be in A (else the point need not have 2 hits in A) -- we just count hits in A
                if not m.any(): continue
                hits=(hitV[m][:,Amask]).sum(1)
                if hits.max()>worst[0]: worst=(int(hits.max()),(s,t1,t2))
    print(N,'max hits',worst,flush=True)

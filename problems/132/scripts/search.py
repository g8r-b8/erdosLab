import numpy as np, random, math, sys
from collections import Counter
def strictly_convex(P):
    # P array of points; check convex position (all on hull, no 3 collinear)
    n=len(P)
    c=P.mean(0); o=np.argsort(np.arctan2(P[:,1]-c[1],P[:,0]-c[0])); Q=P[o]
    for i in range(n):
        a,b,cc=Q[i],Q[(i+1)%n],Q[(i+2)%n]
        u=b-a; v=cc-b
        if u[0]*v[1]-u[1]*v[0]<=1e-9: return False
    return True
def profile(P,tol=1e-7):
    n=len(P); ds=[]
    for i in range(n):
        for j in range(i+1,n): ds.append(math.dist(P[i],P[j]))
    ds.sort(); groups=[]; 
    for x in ds:
        if groups and x-groups[-1][0]<tol: groups[-1][1]+=1
        else: groups.append([x,1])
    return groups
def rare(P):
    n=len(P); g=profile(P); return sum(1 for x,m in g if m<=n), len(g), sorted([m for x,m in g],reverse=True)
def local_search(pool,n,iters=4000,seed=None):
    rnd=random.Random(seed)
    # start: random convex subset by picking from hull-ish
    idx=None
    for t in range(20000):
        cand=rnd.sample(range(len(pool)),n)
        if strictly_convex(pool[cand]): idx=cand;break
    if idx is None: return None
    best=rare(pool[idx]); cur=idx; curv=(best[0],best[1])
    for it in range(iters):
        new=cur[:]; new[rnd.randrange(n)]=rnd.randrange(len(pool))
        if len(set(new))<n: continue
        P=pool[new]
        if not strictly_convex(P): continue
        r=rare(P); v=(r[0],r[1])
        if v<=curv or rnd.random()<0.02:
            cur=new; curv=v
            if v<(best[0],best[1]): best=r; bestidx=new[:]
    return best
if __name__=="__main__":
    kind=sys.argv[1]; n=int(sys.argv[2])
    if kind=="tri":
        R=int(sys.argv[3]); pool=[]
        for a in range(-R,R+1):
            for b in range(-R,R+1):
                x=a+b/2; y=b*math.sqrt(3)/2
                if x*x+y*y<=R*R: pool.append((x,y))
    elif kind=="sq":
        R=int(sys.argv[3]); pool=[(a,b) for a in range(-R,R+1) for b in range(-R,R+1) if a*a+b*b<=R*R]
    elif kind=="cyc":
        N=int(sys.argv[3]); radii=[1,2*math.cos(math.pi/N),1/(2*math.cos(math.pi/N)), math.cos(math.pi/N)]
        pool=[(r*math.cos(2*math.pi*j/N+s*math.pi/N), r*math.sin(2*math.pi*j/N+s*math.pi/N)) for r in radii for j in range(N) for s in (0,1)]
    pool=np.array(pool)
    res=[]
    for s in range(int(sys.argv[4]) if len(sys.argv)>4 else 10):
        r=local_search(pool,n,seed=s)
        if r: res.append(r)
    res.sort(key=lambda r:(r[0],r[1]))
    for r in res[:3]: print(n,"rare",r[0],"D",r[1],"mults",r[2][:12])

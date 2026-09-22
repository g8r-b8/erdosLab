# Triangle-free analogue of CDL Prop 1.5 / ienjoymath servers:
# even m-gon (L1), servers on bisectors at distance D2 from two adjacent vertices, near antipodal edge midpoints,
# square lattice patch with spacing g = server-to-edge-endpoint distance.
import numpy as np, itertools, sys
from collections import Counter
def build(m, c_side):
    R=1.0
    V=np.array([[R*np.cos(2*np.pi*i/m),R*np.sin(2*np.pi*i/m)] for i in range(m)])
    D2=np.linalg.norm(V[0]-V[m//2+1])
    S=[]
    for i in range(m):
        p,q=V[i],V[(i+1)%m]
        # point on perpendicular bisector of p,q (line through origin, direction of midpoint) at distance D2 from p, on far side
        u=(p+q)/np.linalg.norm(p+q); # bisector direction
        # x = -t u, |x-p|=D2 -> t^2 + 2t(u.p) + |p|^2 - D2^2=0
        b=2*u.dot(p); cc=p.dot(p)-D2**2
        t=(-b+np.sqrt(b*b-4*cc))/2
        S.append(-t*u)
    S=np.array(S)
    # g = distance server 0 to its nearby edge endpoints
    g=np.min(np.linalg.norm(V-S[0],axis=1))
    P=np.array([[g*i,g*j] for i in range(c_side) for j in range(c_side)])
    P=P-P.mean(axis=0)+np.array([1e-3*g*0.0,0])
    return V,S,P,g
def analyze(X,tol=1e-9):
    n=len(X)
    d=np.sqrt(((X[:,None,:]-X[None,:,:])**2).sum(-1))
    iu=np.triu_indices(n,1); dv=d[iu]
    order=np.sort(dv)
    # cluster distances
    vals=[];cnt=[]
    for x in order:
        if vals and abs(x-vals[-1])<tol*max(1,x): cnt[-1]+=1
        else: vals.append(x);cnt.append(1)
    return vals,cnt,d
m=int(sys.argv[1]); cs=int(sys.argv[2])
V,S,P,g=build(m,cs)
X=np.vstack([V,S,P]); n=len(X)
vals,cnt,d=analyze(X)
delta,muD=vals[0],cnt[0]; Delta2,mu2=vals[-2],cnt[-2]
print("n",n,"m",m,"servers",len(S),"patch",len(P))
print("delta",delta,"g",g,"mu(delta)",muD,"Delta2",Delta2,"mu(D2)",mu2,"Delta mult",cnt[-1])
# triangle check in delta graph
A=(np.abs(d-delta)<1e-9)&(~np.eye(n,dtype=bool))
tri=np.trace(np.linalg.matrix_power(A.astype(int),3))//6
print("delta-triangles",tri)
rare=[(v,c) for v,c in zip(vals,cnt) if c<=n]
print("#distances",len(vals),"#rare (<=n)",len(rare), "min rare mult",min(c for v,c in rare))

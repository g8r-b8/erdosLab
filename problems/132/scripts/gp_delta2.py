# Seek a set in GENERAL POSITION (no 3 collinear, no 4 concyclic) with mu(Delta2) = 4n/3 > n.
# L1: even m-gon deformed so that antipodal pairs all = Delta and offset-(m/2-1) pairs all = s (=Delta2);
# servers u_j for j even: Delta2 from v_j and v_{j+1}. Then each L1 vertex has Delta2-degree 3.
import numpy as np, itertools, sys
rng=np.random.default_rng(int(sys.argv[2]) if len(sys.argv)>2 else 1)
m=int(sys.argv[1]); h=m//2
def resid(z):
    v=z[:2*m].reshape(m,2); s=z[-1]
    r=[]
    for i in range(m):
        j=(i+h-1)%m; r.append(np.sum((v[i]-v[j])**2)-s*s)
    for i in range(h):
        r.append(np.sum((v[i]-v[i+h])**2)-4.0)
    return np.array(r)
def jac(z,eps=1e-7):
    f0=resid(z); J=np.zeros((len(f0),len(z)))
    for k in range(len(z)):
        dz=np.zeros_like(z); dz[k]=eps; J[:,k]=(resid(z+dz)-f0)/eps
    return J
V0=np.array([[np.cos(2*np.pi*i/m),np.sin(2*np.pi*i/m)] for i in range(m)])
s0=np.linalg.norm(V0[0]-V0[h-1])
z=np.concatenate([(V0+0.03*rng.standard_normal(V0.shape)).ravel(),[s0]])
for it in range(60):
    f=resid(z); 
    if np.max(abs(f))<1e-14: break
    J=jac(z); z=z-np.linalg.lstsq(J,f,rcond=None)[0]
print("resid",np.max(abs(resid(z))))
V=z[:2*m].reshape(m,2); s=z[-1]
# servers
S=[]
for j in range(0,m,2):
    a,b=V[j],V[j+1]
    mid=(a+b)/2; d=np.linalg.norm(b-a); hgt=np.sqrt(s*s-d*d/4)
    nrm=np.array([-(b-a)[1],(b-a)[0]])/d
    c=np.mean(V,axis=0)
    cand=[mid+hgt*nrm, mid-hgt*nrm]
    # choose the one inside (closer to centroid)
    S.append(min(cand,key=lambda x:np.linalg.norm(x-c)))
X=np.vstack([V,np.array(S)]); n=len(X)
D=np.sqrt(((X[:,None]-X[None])**2).sum(-1)); iu=np.triu_indices(n,1); dv=np.sort(D[iu])[::-1]
Delta=dv[0]; muDelta=np.sum(abs(dv-Delta)<1e-9)
Delta2=dv[muDelta]; mu2=np.sum(abs(dv-Delta2)<1e-9)
print("n",n,"Delta",Delta,"mult",muDelta,"Delta2",Delta2,"s",s,"mu(Delta2)",mu2,"4n/3",4*n/3)
# general position checks
def det3(a,b,c): return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
mincol=min(abs(det3(X[i],X[j],X[k])) for i,j,k in itertools.combinations(range(n),3))
def conc(a,b,c,d):
    M=np.array([[p[0],p[1],p[0]**2+p[1]**2,1] for p in (a,b,c,d)]); return abs(np.linalg.det(M))
mincc=min(conc(*[X[t] for t in q]) for q in itertools.combinations(range(n),4))
print("min |collinearity det|",mincol,"min |concyclic det|",mincc)
# convex layers
from scipy.spatial import ConvexHull
h1=set(ConvexHull(X).vertices); rest=[i for i in range(n) if i not in h1]
h2=set(np.array(rest)[ConvexHull(X[rest]).vertices]) if len(rest)>=3 else set(rest)
print("|L1|",len(h1),"|L2|",len(h2),"depth>=3",n-len(h1)-len(h2))
# rare distances
vals=[];cnt=[]
for x in np.sort(D[iu]):
    if vals and abs(x-vals[-1])<1e-9: cnt[-1]+=1
    else: vals.append(x);cnt.append(1)
print("distinct",len(vals),"rare non-diam",sum(1 for v,c in zip(vals,cnt) if c<=n and abs(v-Delta)>1e-9))
bad=[q for q in itertools.combinations(range(n),4) if conc(*[X[t] for t in q])<1e-9]
print("concyclic quadruples (L1 idx <m, servers >=m):",bad[:20], len(bad))

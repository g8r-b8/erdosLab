# Odd m-gon, Delta-cycle (offset k) kept, Delta2 edges = offset (k-1) pairs minus `drop` of them,
# plus CDL servers on adjacent pairs (v_i,v_{i+1}) chosen greedily so every Delta2-degree <= 3.
# Goal: general position (no 3 collinear, no 4 concyclic) with mu(Delta2) > n.
import numpy as np, itertools, sys
m=int(sys.argv[1]); drop=int(sys.argv[2]); seed=int(sys.argv[3]); k=m//2
rng=np.random.default_rng(seed)
D2pairs=[(i,(i+k-1)%m) for i in range(m)]
dropped=D2pairs[:drop*2:2][:drop]  # spread drops
keep=[p for p in D2pairs if p not in dropped]
Dpairs=[(i,(i+k)%m) for i in range(m)]
def resid(z):
    v=z[:2*m].reshape(m,2); s=z[-1]; r=[]
    for i,j in Dpairs: r.append(np.sum((v[i]-v[j])**2)-4.0)
    for i,j in keep: r.append(np.sum((v[i]-v[j])**2)-s*s)
    return np.array(r)
def jac(z,eps=1e-7):
    f0=resid(z); J=np.zeros((len(f0),len(z)))
    for t in range(len(z)):
        dz=np.zeros_like(z); dz[t]=eps; J[:,t]=(resid(z+dz)-f0)/eps
    return J
R=1/np.sin(np.pi*k/m)  # so that offset-k chord = 2
V0=np.array([[R*np.cos(2*np.pi*i/m),R*np.sin(2*np.pi*i/m)] for i in range(m)])
s0=np.linalg.norm(V0[0]-V0[k-1])
z=np.concatenate([(V0+float(sys.argv[4])*rng.standard_normal(V0.shape)).ravel(),[s0]])
for it in range(100):
    f=resid(z)
    if np.max(abs(f))<1e-14: break
    z=z-np.linalg.lstsq(jac(z),f,rcond=None)[0]
V=z[:2*m].reshape(m,2); s=z[-1]
deg=np.zeros(m,int)
for i,j in keep: deg[i]+=1; deg[j]+=1
S=[]; c=V.mean(0)
for i in range(m):
    j=(i+1)%m
    if deg[i]<3 and deg[j]<3:
        a,b=V[i],V[j]; mid=(a+b)/2; d=np.linalg.norm(b-a)
        if s*s-d*d/4<=0: continue
        hg=np.sqrt(s*s-d*d/4); nr=np.array([-(b-a)[1],(b-a)[0]])/d
        S.append(min([mid+hg*nr,mid-hg*nr],key=lambda x:np.linalg.norm(x-c))); deg[i]+=1; deg[j]+=1
X=np.vstack([V,np.array(S)]) if S else V; n=len(X)
Dm=np.sqrt(((X[:,None]-X[None])**2).sum(-1)); iu=np.triu_indices(n,1); dv=np.sort(Dm[iu])[::-1]
Delta=dv[0]; muD=int(np.sum(abs(dv-Delta)<1e-9)); Delta2=dv[muD]; mu2=int(np.sum(abs(dv-Delta2)<1e-9))
print(f"m={m} drop={drop} resid={np.max(abs(resid(z))):.1e} n={n} servers={len(S)} Delta={Delta:.6f}x{muD} Delta2={Delta2:.6f} (s={s:.6f}) mu2={mu2} n={n}  mu2>n? {mu2>n}")
def det3(a,b,c): return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def conc(*P):
    M=np.array([[p[0],p[1],p[0]**2+p[1]**2,1] for p in P]); return abs(np.linalg.det(M))
mincol=min(abs(det3(X[i],X[j],X[t])) for i,j,t in itertools.combinations(range(n),3))
cc=sorted((conc(*[X[t] for t in q]),q) for q in itertools.combinations(range(n),4))
print(" min collinear det",f"{mincol:.2e}"," smallest concyclic dets",[(f"{a:.1e}",q) for a,q in cc[:4]])
np.save(f"gp2_m{m}_d{drop}_s{seed}.npy",X)

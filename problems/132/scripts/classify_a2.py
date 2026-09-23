"""Classify good delta-edges on S as T (tangential) / R (rung) / bad, check A2 lemmas on constructions."""
import numpy as np, sys
sys.path.insert(0,'.')
from constr import ring_even, ring_odd, lattice_patch
def classify(X,name,beta=0.01,tol=1e-9):
    n=len(X); Dm=np.linalg.norm(X[:,None]-X[None],axis=2); iu=np.triu_indices(n,1); d=Dm[iu]
    delta=d.min(); X=X/delta; Dm=Dm/delta; d=d/delta
    Dl=d.max(); D2=max(x for x in d if x<Dl*(1-tol)); t=Dl-D2; tau=t-(1-t*t)/(2*D2)
    A2=np.abs(Dm-D2)<1e-7*Dl; A1=np.abs(Dm-Dl)<1e-7*Dl; Ad=np.abs(Dm-1)<1e-7
    for M in (A2,A1,Ad): np.fill_diagonal(M,False)
    S=np.where(A2.any(1))[0]; Dset=A1.any(1)
    u={}
    for p in S:
        if Dset[p]: x=np.where(A1[p])[0][0]; u[p]=(X[x]-X[p])/Dl
        else: w=np.where(A2[p])[0][0]; u[p]=(X[w]-X[p])/D2
    Sset=set(S); T=[];R=[];bad=[]
    for p in S:
        for q in np.where(Ad[p])[0]:
            if q<=p or q not in Sset: continue
            ang=np.arccos(np.clip(u[p]@u[q],-1,1))
            if ang>beta: bad.append((p,q)); continue
            a=(X[q]-X[p])@u[p]; b=(X[p]-X[q])@u[q]
            if a>0 and b>0: T.append((p,q))
            else:
                R.append((p,q)); ex=a if a<0 else b
                assert abs(-ex-tau)<1e-6, ("rung dot not exactly -tau",ex,tau)
    # per-vertex checks
    from collections import Counter
    rc=Counter([x for e in R for x in e]); maxr=max(rc.values()) if rc else 0
    side=Counter()
    for (p,q) in T:
        perp=np.array([-u[p][1],u[p][0]]); side[(p,np.sign((X[q]-X[p])@perp))]+=1
        perp=np.array([-u[q][1],u[q][0]]); side[(q,np.sign((X[p]-X[q])@perp))]+=1
    maxs=max(side.values()) if side else 0
    eS=len(T)+len(R)+len(bad)
    th=np.degrees(np.arccos(min(1,tau))) if tau<=1 else float('nan')
    reg='I' if tau<=np.sqrt(3)/2-2*beta else ('II' if tau>=np.sqrt(3)/2+3*beta else 'III')
    print(f"{name}: n={n} t={t:.4g} tau={tau:.6f} theta0={th:.3f}deg Region {reg} |S|={len(S)} T={len(T)} R={len(R)} bad={len(bad)} "
          f"e(S)/|S|={eS/len(S):.3f} maxT/side={maxs} maxRung/vertex={maxr}")
for m in [60,200]:
    V,U=ring_even(m); classify(np.vstack([V,U]),f"even ring m={m}")
for m in [61,201]:
    V,U=ring_odd(m); classify(np.vstack([V,U]),f"odd ring m={m}")

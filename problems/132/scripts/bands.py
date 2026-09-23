import numpy as np
from constr import *
def bands(X,name,beta=0.05):
    r=analyze(X,name); Dm=r['Dm']; S=r['S']; Dset=r['Dset']; Ad=r['Ad']; A2=r['A2']; A1=r['A1']
    n=len(X); U=np.zeros((n,2))
    for p in range(n):
        if not S[p]: continue
        q = np.where(A1[p])[0][0] if Dset[p] else np.where(A2[p])[0][0]
        U[p]=(X[q]-X[p])/np.linalg.norm(X[q]-X[p])
    t=(r['Delta']-r['D2'])/r['delta']
    worst=0; nb=0; good=0; bad=0; eus=[]
    for p in np.where(S)[0]:
        T=np.array([-U[p][1],U[p][0]])
        sides={+1:0,-1:0}
        for q in np.where(Ad[p]&S)[0]:
            e=(X[q]-X[p])/r['delta']
            ang=np.degrees(np.arccos(np.clip(U[p]@U[q],-1,1)))
            if ang<=np.degrees(beta)+1e-9:
                good+=1; sides[int(np.sign(e@T))]+=1; eus.append(e@U[p])
            else: bad+=1
        worst=max(worst,max(sides.values()))
    print(f"   t/delta={t:.4f} good edge-ends={good} bad edge-ends={bad} max good nbrs per side={worst} e.u range=[{min(eus) if eus else 0:.4f},{max(eus) if eus else 0:.4f}]")
for m in [20,40]:
    V,U_=ring_even(m); bands(np.vstack([V,U_]),f"even ring m={m}")
for m in [21,41]:
    V,U_=ring_odd(m); bands(np.vstack([V,U_]),f"odd ring m={m}")

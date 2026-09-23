import numpy as np, itertools, sys
def ring_even(m):
    a=2*np.pi/m; c=np.cos(np.pi/m)
    V=np.array([[np.cos(j*a),np.sin(j*a)] for j in range(m)])
    s=-c+np.sqrt(5*c*c-1)
    U=np.array([s*np.array([np.cos((i+.5)*a+np.pi),np.sin((i+.5)*a+np.pi)]) for i in range(m)])
    return V,U
def ring_odd(m):
    a=2*np.pi/m
    V=np.array([[np.cos(j*a),np.sin(j*a)] for j in range(m)])
    k=(m-3)//2; D2=2*np.sin(k*np.pi/m)
    # u_i on bisector of v_i v_{i+1}, inside, |u_i v_i|=D2
    U=[]
    for i in range(m):
        mid=(V[i]+V[(i+1)%m])/2; dirn=-mid/np.linalg.norm(mid); h=np.linalg.norm(V[i]-mid)
        d=np.sqrt(D2**2-h**2); U.append(mid+d*dirn)
    return V,np.array(U)
def lattice_patch(P,mesh):
    pts=[];R=int(np.sqrt(P))+3
    for i in range(-R,R+1):
        for j in range(-R,R+1):
            pts.append((i+j/2, j*np.sqrt(3)/2))
    pts=np.array(pts); pts=pts[np.argsort(np.linalg.norm(pts,axis=1))][:P]
    return pts*mesh
def analyze(X,name,tol=1e-9):
    n=len(X); Dm=np.linalg.norm(X[:,None]-X[None],axis=2)
    iu=np.triu_indices(n,1); d=Dm[iu]
    vals=np.sort(np.unique(np.round(d/ d.max(),11)))[::-1]*d.max()
    Delta=d.max(); 
    D2=max(x for x in d if x<Delta*(1-tol))
    delta=d.min()
    mu=lambda v: int(np.sum(np.abs(d-v)<tol*Delta))
    A2=np.abs(Dm-D2)<tol*Delta; A1=np.abs(Dm-Delta)<tol*Delta; Ad=np.abs(Dm-delta)<tol*Delta
    np.fill_diagonal(A2,False);np.fill_diagonal(A1,False);np.fill_diagonal(Ad,False)
    S=A2.any(1); Dset=A1.any(1)
    t=(Delta-D2)/delta
    eS=int(Ad[np.ix_(S,S)].sum()//2)
    # Jung-ish: check Delta <= sqrt3 (D2-2delta)
    print(f"{name}: n={n} mu(D2)={mu(D2)} mu(delta)={mu(delta)} ratio={min(mu(D2),mu(delta))/n:.4f} t/delta={t:.4g} |S|={S.sum()} |D|={Dset.sum()} |S&D|={(S&Dset).sum()} e(S)={eS} e(S)-|S|={eS-S.sum()} JungOK={Delta<=np.sqrt(3)*(D2-2*delta)}")
    return dict(Dm=Dm,S=S,Dset=Dset,Ad=Ad,A2=A2,A1=A1,D2=D2,Delta=Delta,delta=delta)
if __name__=="__main__":
    for m in [20,40,60]:
        V,U=ring_even(m); X=np.vstack([V,U]); r=analyze(X,f"even ring m={m}")
        g=np.linalg.norm(U[0]-V[m//2]); P=int(2*m/3*7/6); 
        X2=np.vstack([V,U,lattice_patch(m//3,g)]); analyze(X2,f"even ring+lattice m={m}")
    for m in [21,41,61]:
        V,U=ring_odd(m); X=np.vstack([V,U]); analyze(X,f"odd ring m={m}")

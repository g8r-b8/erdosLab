# Check Theorem A: mu(Delta2) <= |L1|+|L2| + 1/2 * sum_{p in L1'} (deg'(p)-2), and H3 corollary.
import numpy as np, sys, importlib
from scipy.spatial import ConvexHull
def layers(X):
    idx=list(range(len(X))); out=[]
    while len(idx)>=3:
        h=ConvexHull(X[idx]).vertices; L=[idx[i] for i in h]; out.append(set(L)); idx=[i for i in idx if i not in L]
    if idx: out.append(set(idx))
    return out
def check(X,name,tol=1e-9):
    n=len(X); D=np.sqrt(((X[:,None]-X[None])**2).sum(-1)); iu=np.triu_indices(n,1)
    dv=np.sort(D[iu])[::-1]; Delta=dv[0]; muD=int(np.sum(abs(dv-Delta)<tol)); D2=dv[muD]
    A=(abs(D-D2)<tol)&~np.eye(n,dtype=bool); mu2=int(A.sum()//2)
    Ls=layers(X); L1,L2=Ls[0],(Ls[1] if len(Ls)>1 else set())
    V=set(L1|L2); assert all((i in V and j in V) for i,j in zip(*np.nonzero(A)))
    # 2-core
    core=set(V); changed=True
    while changed:
        changed=False
        for v in list(core):
            if sum(1 for u in core if A[v,u])<2: core.remove(v); changed=True
    degc={v:sum(1 for u in core if A[v,u]) for v in core}
    assert all(degc[v]==2 for v in core if v in L2), "L2' degree !=2"
    bound=len(L1)+len(L2)+0.5*sum(degc[v]-2 for v in core if v in L1)
    h=[int(A[v].sum()) for v in range(n)]
    print(f"{name}: n={n} mu2={mu2} |L1|={len(L1)} |L2|={len(L2)} m3={n-len(L1)-len(L2)} ThmA bound={bound} maxdeg={max(h)} CDL={min(1.5*(len(L1)+len(L2)),4/3*len(L1)+2*len(L2),2*len(L1)+len(L2)):.1f} ok={mu2<=bound+1e-9}")
if __name__=="__main__":
    for f in sys.argv[1:]:
        check(np.load(f),f)

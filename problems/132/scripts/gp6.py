# n=6 general-position set with mu(Delta2)=7>n: 60-degree rhombus a,c,b,d (side 1, long diag sqrt3)
# plus e on circle(a,1) inside lens, f on circle(b,1) inside lens.
import numpy as np, itertools
s3=np.sqrt(3)
a=np.array([0,0.]); b=np.array([s3,0.]); c=np.array([s3/2,.5]); d=np.array([s3/2,-.5])
t1=np.radians(11.0); t2=np.radians(180+19.0)
e=np.array([np.cos(t1),np.sin(t1)]); f=b+np.array([np.cos(t2),np.sin(t2)])
X=np.array([a,b,c,d,e,f]); n=len(X)
D=np.sqrt(((X[:,None]-X[None])**2).sum(-1)); iu=np.triu_indices(n,1)
vals=sorted(set(np.round(D[iu],9)))[::-1]
from collections import Counter
C=Counter(np.round(D[iu],9)); print([(v,C[v]) for v in vals[:4]])
def det3(p,q,r): return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])
def conc(*P): return abs(np.linalg.det(np.array([[p[0],p[1],p[0]**2+p[1]**2,1] for p in P])))
print("min collinear",min(abs(det3(*X[list(q)])) for q in itertools.combinations(range(n),3)))
print("min concyclic",min(conc(*X[list(q)]) for q in itertools.combinations(range(n),4)))
print("all multiplicities",sorted(C.values(),reverse=True))

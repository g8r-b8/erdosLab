import itertools, sys, numpy as np
from lattice_sa import pool, dmat
kind=sys.argv[1]; R=int(sys.argv[2]); ns=[int(x) for x in sys.argv[3].split(',')]
pts=pool(kind,R) if kind=='tri' else [(a,b) for a in range(R) for b in range(R)]
D=dmat(kind,pts); N=len(pts)
for n in ns:
    iu=np.triu_indices(n,1)
    best=-1;bx=None
    # fix first point = lowest index to reduce translation duplicates? keep simple
    for S in itertools.combinations(range(N),n):
        v=D[np.ix_(S,S)][iu]
        c=np.bincount(v)
        nz=np.nonzero(c)[0]
        M=c[nz[:-1]].min()
        if M>best: best=M;bx=S;sp=[(int(k),int(c[k])) for k in nz]
    print(kind,R,'n',n,'M',best,'ratio %.3f'%(best/n),[pts[i] for i in bx],sp,flush=True)

# For regular N-gon V: among points q not in V, not center, near the circle (|q| in [r1,r2]) find max #{i: |q-v_i| in chord set}.
import numpy as np, math, itertools, sys
N=int(sys.argv[1]); rlo=float(sys.argv[2]) if len(sys.argv)>2 else 0.0; rhi=float(sys.argv[3]) if len(sys.argv)>3 else 10
V=np.array([(math.cos(2*math.pi*i/N),math.sin(2*math.pi*i/N)) for i in range(N)])
ch=np.array(sorted(set(2*math.sin(math.pi*j/N) for j in range(1,N//2+1))))
best=[];seen=set()
for i2 in range(1,N):  # by rotation symmetry take i=0
    for r1 in ch:
        for r2 in ch:
            c1=V[0];c2=V[i2];d=np.linalg.norm(c2-c1)
            if d>r1+r2+1e-12 or d<abs(r1-r2)-1e-12: continue
            a=(r1*r1-r2*r2+d*d)/(2*d); h=math.sqrt(max(r1*r1-a*a,0))
            m=c1+a*(c2-c1)/d; perp=np.array([-(c2-c1)[1],(c2-c1)[0]])/d
            for q in (m+h*perp,m-h*perp):
                nq=np.linalg.norm(q)
                if nq<1e-9 or abs(nq-1)<1e-9 or not(rlo<=nq<=rhi): continue
                key=(round(q[0],6),round(q[1],6))
                if key in seen: continue
                seen.add(key)
                ds=np.linalg.norm(V-q,axis=1)
                hits=sum(1 for x in ds if np.min(np.abs(ch-x))<1e-9)
                cls=len(set(int(np.argmin(np.abs(ch-x))) for x in ds if np.min(np.abs(ch-x))<1e-9))
                best.append((hits,cls,round(nq,5)))
best.sort(reverse=True)
print(N,"max hits/classes (all radii)",best[:4])

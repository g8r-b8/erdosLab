"""Subdivided regular Reuleaux polygons: regular (2k+1)-gon of diameter 1, each vertex v_i is the centre of the
arc joining the two opposite vertices; subdivide each arc into t equal steps.  n=(2k+1)t points, convex.
Report n, D, floor(n/2), multiplicity profile, #rare."""
import numpy as np, math, itertools, sys
from collections import Counter
def reuleaux(k,t):
    M=2*k+1
    R=0.5/math.sin(math.pi*k/M)*1.0  # circumradius so that diagonal v_i v_{i+k} has length 1
    V=[R*np.array([math.cos(2*math.pi*i/M+math.pi/2),math.sin(2*math.pi*i/M+math.pi/2)]) for i in range(M)]
    pts=[]
    for i in range(M):
        a=V[(i+k)%M]; b=V[(i+k+1)%M]; c=V[i]
        th0=math.atan2(a[1]-c[1],a[0]-c[0]); th1=math.atan2(b[1]-c[1],b[0]-c[0])
        dth=(th1-th0+math.pi)%(2*math.pi)-math.pi
        for j in range(t):
            th=th0+dth*j/t; pts.append(c+np.array([math.cos(th),math.sin(th)]))
    return np.array(pts)
for k in range(1,6):
    for t in range(1,8):
        P=reuleaux(k,t); n=len(P)
        d=[round(float(np.linalg.norm(P[i]-P[j])),7) for i,j in itertools.combinations(range(n),2)]
        c=Counter(d); prof=[c[x] for x in sorted(c)]
        print('k=%d t=%d n=%d D=%d floor(n/2)=%d K=%d rare=%d prof(asc)=%s'%(k,t,n,len(c),n//2,len(c)-n//2,sum(1 for x in prof if x<=n),prof[:12]))

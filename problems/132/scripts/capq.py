# Regular N-gon plus one extra point q in the cap beyond edge v0v1 (keeping convex position).
# For each candidate q (intersection of two circles C(v_i,c_j)), count how many vertices are at chord-length distance
# and how many chord classes get hit.
import numpy as np, math, itertools, sys
from collections import Counter
N=int(sys.argv[1])
V=np.array([(math.cos(2*math.pi*i/N),math.sin(2*math.pi*i/N)) for i in range(N)])
chords=[2*math.sin(math.pi*j/N) for j in range(1,N//2+1)]
def incap(q):
    # q outside line v0v1 and inside lines v_{-1}v0 and v1v2 extended (strict)
    def side(a,b,p): return (b[0]-a[0])*(p[1]-a[1])-(b[1]-a[1])*(p[0]-a[0])
    v0,v1,vm,v2=V[0],V[1],V[-1],V[2]
    return side(v0,v1,q)< -1e-9 and side(vm,v0,q)>1e-9 and side(v1,v2,q)>1e-9
def circ_int(c1,r1,c2,r2):
    d=math.dist(c1,c2)
    if d>r1+r2 or d<abs(r1-r2) or d==0: return []
    a=(r1*r1-r2*r2+d*d)/(2*d); h=math.sqrt(max(r1*r1-a*a,0))
    mx=c1[0]+a*(c2[0]-c1[0])/d; my=c1[1]+a*(c2[1]-c1[1])/d
    return [(mx+h*(c2[1]-c1[1])/d, my-h*(c2[0]-c1[0])/d),(mx-h*(c2[1]-c1[1])/d, my+h*(c2[0]-c1[0])/d)]
best=Counter(); seen=set(); results=[]
for i,i2 in itertools.combinations(range(N),2):
    for r1 in chords:
        for r2 in chords:
            for q in circ_int(V[i],r1,V[i2],r2):
                if not incap(q): continue
                key=(round(q[0],7),round(q[1],7))
                if key in seen: continue
                seen.add(key)
                ds=[math.dist(q,v) for v in V]
                hits=[min(range(len(chords)),key=lambda j:abs(chords[j]-d)) for d in ds if min(abs(c-d) for c in chords)<1e-9]
                results.append((len(hits),len(set(hits)),key))
results.sort(reverse=True)
print(N,"cands",len(results),"top",results[:5])

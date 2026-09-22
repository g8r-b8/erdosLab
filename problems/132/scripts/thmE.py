import numpy as np, math, random
from search import profile, strictly_convex
def capsample(a,e,rnd):
    th=math.pi/a; Rz=math.cos(th)/math.cos(2*th)
    x0=np.array([math.cos(2*math.pi*e/a),math.sin(2*math.pi*e/a)]); x1=np.array([math.cos(2*math.pi*(e+1)/a),math.sin(2*math.pi*(e+1)/a)])
    z=Rz*np.array([math.cos(2*math.pi*e/a+th),math.sin(2*math.pi*e/a+th)])
    u,v=rnd.random(),rnd.random()
    if u+v>1: u,v=1-u,1-v
    return x0+u*(x1-x0)+v*(z-x0)
rnd=random.Random(1); worst={}
for trial in range(3000):
    a=rnd.choice([5,6,7,8,9,11,12,13,15,16]); t=rnd.randint(1,4)
    A=[(math.cos(2*math.pi*i/a),math.sin(2*math.pi*i/a)) for i in range(a)]
    edges=rnd.sample(range(a),t)
    T=[]
    for e in edges:
        # sometimes snap onto circle C(antipode, cmax) to force diameter hits
        q=capsample(a,e,rnd); T.append(tuple(q))
    P=np.array(A+T)
    if not strictly_convex(P): continue
    n=len(P); g=profile(P); rare=sum(1 for x,m in g if m<=n)
    bound=a//2-1-(t//2)
    worst[(a,t)]=min(worst.get((a,t),99),rare-bound)
print("min(rare - bound) over trials:",min(worst.values()))
print(sorted(worst.items())[:12])

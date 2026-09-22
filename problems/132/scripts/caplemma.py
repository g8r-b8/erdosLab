# For regular a-gon on unit circle, cap triangle beyond edge x0x1 with apex z.
# For each vertex x, the set {|q-x| : q in open cap} is an open interval (lo,hi).
# Check which chord lengths lie in [lo,hi] (closed, conservative).
import math
def seg_dist(p,a,b):
    ax,ay=a;bx,by=b;px,py=p
    dx,dy=bx-ax,by-ay; t=((px-ax)*dx+(py-ay)*dy)/(dx*dx+dy*dy); t=max(0,min(1,t))
    return math.hypot(ax+t*dx-px,ay+t*dy-py)
def check(a):
    V=[(math.cos(2*math.pi*i/a),math.sin(2*math.pi*i/a)) for i in range(a)]
    ch=sorted(set(round(2*math.sin(math.pi*j/a),12) for j in range(1,a//2+1)))
    cmax=ch[-1]
    Rz=math.cos(math.pi/a)/math.cos(2*math.pi/a); z=(Rz*math.cos(math.pi/a),Rz*math.sin(math.pi/a))
    x0,x1=V[0],V[1]
    bad=[]
    for i in range(0,a):
        x=V[i]
        lo=min(seg_dist(x,x0,x1),seg_dist(x,x1,z),seg_dist(x,z,x0))
        hi=max(math.dist(x,x0),math.dist(x,x1),math.dist(x,z))
        # open cap interior values lie in (lo,hi); chord values equal to endpoints attained only on boundary
        inside=[c for c in ch if lo+1e-12<c<hi-1e-12]
        if any(abs(c-cmax)>1e-12 for c in inside): bad.append((i,inside))
    return bad
allok=True
for a in range(5,400):
    b=check(a)
    if b: allok=False; print(a,b[:3])
print("all ok" if allok else "failures")

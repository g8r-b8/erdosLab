import numpy as np
# v=0, u=(1,0). neighbors at angles a1<a2<a3 in (-90,90), gaps>=60.
# feasible u' for y2: (z-y2).u'>0 for z in {0,y1,y3}. find min angle between u and feasible u'.
def e(a): a=np.radians(a); return np.array([np.cos(a),np.sin(a)])
best=(1e9,None)
for a1 in np.arange(-90,90.01,0.5):
  for a2 in np.arange(a1+60,90.01,0.5):
    for a3 in np.arange(a2+60,90.01,0.5):
      y1,y2,y3=e(a1),e(a2),e(a3)
      dirs=[ -y2, y1-y2, y3-y2 ]
      angs=[np.degrees(np.arctan2(d[1],d[0])) for d in dirs]
      # feasible u' angles: within (ang-90, ang+90) of each -> intersect arcs
      # sample
      th=np.arange(0,360,0.25)
      U=np.stack([np.cos(np.radians(th)),np.sin(np.radians(th))],1)
      ok=np.all(np.stack([U@d>1e-12 for d in dirs]),0)
      if not ok.any(): continue
      diff=np.abs((th[ok]+180)%360-180)
      m=diff.min()
      if m<best[0]: best=(m,(a1,a2,a3))
print(best)

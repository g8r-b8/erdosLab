import numpy as np, itertools
def e(a): a=np.radians(a); return np.array([np.cos(a),np.sin(a)])
th=np.arange(0,360,0.25); U=np.stack([np.cos(np.radians(th)),np.sin(np.radians(th))],1)
def worst(t, allow_exc=True, step=1.0):
    best=(1e9,None)
    for a1 in np.arange(-90,90.01,step):
      for a2 in np.arange(a1+60,90.01,step):
        for a3 in np.arange(a2+60,90.01,step):
          y1,y2,y3=e(a1),e(a2),e(a3)
          opts=[]
          for s1 in ([0,1] if allow_exc else [0]):
            for s3 in ([0,1] if allow_exc else [0]):
              ok=(U@(-y2)>0)
              for s,y in ((s1,y1),(s3,y3)):
                d=y-y2; L=np.linalg.norm(d)
                if s==0: ok&=(U@d>0)
                else:
                  if L<t-1e-9: ok&=False
                  else: ok&=np.abs(U@d+t)<0.02  # component ~ -t
              if ok.any():
                diff=np.abs((th[ok]+180)%360-180); m=diff.min()
                if m<best[0]: best=(m,(a1,a2,a3,s1,s3))
    return best
for t in [0.5,1.0,1.2,1.5,1.8,2.0]:
    print(t, worst(t,step=2.0))

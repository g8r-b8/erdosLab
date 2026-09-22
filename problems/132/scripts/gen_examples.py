import numpy as np, subprocess
# CDL Prop1.5 style (odd m, all servers), and even-m alternate servers, plus tf construction
def poly(m,R=1.0): return np.array([[R*np.cos(2*np.pi*i/m),R*np.sin(2*np.pi*i/m)] for i in range(m)])
def servers(V,s,pairs):
    c=V.mean(0); S=[]
    for i,j in pairs:
        a,b=V[i],V[j]; mid=(a+b)/2; d=np.linalg.norm(b-a); hg=np.sqrt(s*s-d*d/4); nr=np.array([-(b-a)[1],(b-a)[0]])/d
        S.append(min([mid+hg*nr,mid-hg*nr],key=lambda x:np.linalg.norm(x-c)))
    return np.array(S)
for m in (9,11,15):
    V=poly(m); k=m//2; s=np.linalg.norm(V[0]-V[k-1])
    X=np.vstack([V,servers(V,s,[(i,(i+1)%m) for i in range(m)])]); np.save(f"cdl_odd{m}.npy",X)
    rng=np.random.default_rng(0); P=0.02*rng.standard_normal((m,2)); X2=np.vstack([X,P]); np.save(f"cdl_odd{m}_int.npy",X2)
for m in (8,12,16):
    V=poly(m); h=m//2; s=np.linalg.norm(V[0]-V[h-1])
    X=np.vstack([V,servers(V,s,[(i,i+1) for i in range(0,m,2)])]); np.save(f"even_alt{m}.npy",X)

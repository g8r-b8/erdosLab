"""route3 checks (light compute).
1. Every element of T = {(a,b,c) in (Z/5)^3 : abc != 0, a+b+c = 0} has a coordinate in {1,4}
   AND a coordinate in {2,3}; so local U^2-uniformity of g alone (or of g^2 alone) controls all of T.
2. Prop 9.6 model: the local Fourier sup  sup_alpha |E_{h<H} zeta^{X_h} e(-alpha h)|  is bounded
   below (≈ 0.418 = (5 sin(pi/5)/pi)/sqrt5) for almost every sample, i.e. the model is NOT locally
   Fourier uniform; hence local U^2 uniformity excludes it.
"""
import numpy as np
T=[(a,b,c) for a in range(1,5) for b in range(1,5) for c in range(1,5) if (a+b+c)%5==0]
assert len(T)==12
print("T:",T)
print("all T terms meet {1,4}:", all(any(x in (1,4) for x in t) for t in T))
print("all T terms meet {2,3}:", all(any(x in (2,3) for x in t) for t in T))
print("T terms inside {1,4}^3 or {2,3}^3:", [t for t in T if set(t)<= {1,4} or set(t)<={2,3}])

rng=np.random.default_rng(1)
zeta=np.exp(2j*np.pi/5)
H=4000; S=200
h=np.arange(H)
vals=[]
for _ in range(S):
    y,th=rng.random(2); s=rng.integers(5); kap=rng.choice([0.2,0.8])
    u=(y+h*th-kap*(s+h)**2)%1.0
    X=np.floor(5*u).astype(int)%5
    g=zeta**X
    # sup over alpha: FFT on a fine grid (zero-padded 8x) + local refinement unnecessary at this H
    F=np.abs(np.fft.fft(g,8*H))/H
    vals.append(F.max())
vals=np.array(vals)
pred=(5*np.sin(np.pi/5)/np.pi)/np.sqrt(5)
print(f"model local Fourier sup, H={H}: min {vals.min():.3f} median {np.median(vals):.3f} max {vals.max():.3f}; predicted {pred:.3f}")
# control: g uniformly random mu_5 sequence
F=np.abs(np.fft.fft(zeta**rng.integers(0,5,H),8*H))/H
print(f"iid control sup: {F.max():.3f}")

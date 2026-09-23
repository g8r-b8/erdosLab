"""lp5: LP for angle A2.  Variables (fractions of n): a=|L1'|, b=|L2'|, s=|P| (pruned, has D2-partner), r=|R|.
Constraints on T=min(muD2,mudelta)/n:
  (V1) T <= s + 4a/3 + 2b          (CDL/Vesztergombi Props, black box)
  (V2) T <= s + 2a + b
  (VS) T <= 1.5 (a+b+s)            (Vesztergombi 1987 applied to the subset S -- new)
  (E)  T <= k (a+b) + kp s + 6 r   (e_delta(S) <= k|S\\P| + kp|P|, each R point degree <= 6)
"""
from scipy.optimize import linprog
from fractions import Fraction
def solve(k=1.0,kp=None,use_V=True,use_VS=True):
    if kp is None: kp=k
    A=[];b=[]
    if use_V:
        A+= [[-4/3,-2,-1,0,1],[-2,-1,-1,0,1]]; b+=[0,0]
    if use_VS:
        A+= [[-1.5,-1.5,-1.5,0,1]]; b+=[0]
    A+= [[-k,-k,-kp,-6,1]]; b+=[0]
    r=linprog([0]*4+[-1],A_ub=A,b_ub=b,A_eq=[[1]*4+[0]],b_eq=[1],bounds=[(0,None)]*5)
    return -r.fun, r.x.round(4)
if __name__=="__main__":
    print("check old claims (no VS): k=1 ->",solve(1,use_VS=False)[0]," kp=3 ->",solve(1,3,use_VS=False)[0])
    for k in [1.0,1.2,1.4,1.45,1.49]:
        v,x=solve(k,use_V=False); print(f"VS only, uniform k={k}: T={v:.5f}  formula 9/(7.5-k)={9/(7.5-k):.5f}")
    for k,kp in [(1,2),(1,3),(1,4),(1.4,1.4),(1,3.5)]:
        v,x=solve(k,kp); print(f"V+VS k={k} kp={kp}: T={v:.5f} x={x}")

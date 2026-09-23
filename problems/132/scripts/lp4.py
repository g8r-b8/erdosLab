from scipy.optimize import linprog
def solve(ks=1.0,kp=3.0,kr=6.0):
    # x=[a1,b,pp (pruned w/ edge), r (no D2 partner), T]
    A=[[-4/3,-2,-1,0,1],[-2,-1,-1,0,1],[-ks,-ks,-kp,-kr,1]]
    r=linprog([0]*4+[-1],A_ub=A,b_ub=[0]*3,A_eq=[[1]*4+[0]],b_eq=[1],bounds=[(0,None)]*5)
    return r.x.round(4), round(-r.fun,5)
for ks in [1.0,1.1]:
  for kp in [1.5,2,2.5,3,4,6]:
    print(ks,kp,solve(ks,kp))

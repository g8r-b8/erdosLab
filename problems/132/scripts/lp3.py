from scipy.optimize import linprog
def solve(ks=1.0,kr0=3.5,kc=4.0):
    # x=[a1,p,b,r2p,r20,c,T]
    A=[[-4/3,-1,-2,-1,0,0,1],[-2,-1,-1,-1,0,0,1],[-1.5,-1.5,-1.5,-1.5,-1.5,0,1],[-ks,-ks,-ks,-ks,-kr0,-kc,1]]
    r=linprog([0]*6+[-1],A_ub=A,b_ub=[0]*4,A_eq=[[1]*6+[0]],b_eq=[1],bounds=[(0,None)]*7)
    return r.x.round(4), -r.fun
for ks in [1.0,1.2,1.3,1.4,1.45]:
    print(ks, solve(ks), solve(ks,4,4))

from scipy.optimize import linprog
def solve(ks=1.0,kr2=3.5,kc=4.0,extra=0.0):
    # x=[a1,p,b,r2,c,T]
    A=[[-4/3,-1,-2,-1,0,1],[-2,-1,-1,-1,0,1],[-1.5,-1.5,-1.5,-1.5,0,1],[-ks,-ks,-ks,-kr2,-kc,1]]
    B=[0,0,0,extra]
    r=linprog([0,0,0,0,0,-1],A_ub=A,b_ub=B,A_eq=[[1,1,1,1,1,0]],b_eq=[1],bounds=[(0,None)]*6)
    return r.x.round(4), -r.fun
print(solve())

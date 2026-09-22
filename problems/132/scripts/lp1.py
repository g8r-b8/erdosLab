from scipy.optimize import linprog
# vars: a1 (L1'), p (pruned hull), b (L2'), r2 (pruned L2), c, T ; maximize T
# normalized n=1
import numpy as np
def solve(kdelta_strip=1.0, kR=4.0):
    # x = [a1,p,b,r2,c,T]
    A=[];B=[]
    # T <= p + r2 + 4/3 a1 + 2 b
    A.append([-4/3,-1,-2,-1,0,1]);B.append(0)
    # T <= p + r2 + 2a1 + b
    A.append([-2,-1,-1,-1,0,1]);B.append(0)
    # T <= 3/2 (a1+p+b+r2)
    A.append([-1.5,-1.5,-1.5,-1.5,0,1]);B.append(0)
    # T <= mu_delta <= kstrip*(a1+p+b) + kR*(r2+c)
    A.append([-kdelta_strip,-kdelta_strip,-kdelta_strip,-kR,-kR,1]);B.append(0)
    Aeq=[[1,1,1,1,1,0]];Beq=[1]
    r=linprog([0,0,0,0,0,-1],A_ub=A,b_ub=B,A_eq=Aeq,b_eq=Beq,bounds=[(0,None)]*6)
    return r.x, -r.fun
for ks,kr in [(1,4),(1,3),(1.5,4),(1,3.5)]:
    print(ks,kr,solve(ks,kr))

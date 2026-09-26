# Rebuild A from the orbit and verify n/2^n == sum_{a in A} a/2^a exactly (integer arithmetic, scaled).
import sys
def rebuild(n, cap=10**7):
    a=n+1; s=2*n; A=[]; split=None; path=[]   # path: list of (a, include?)
    while a<=n+cap:
        d=s-(a+1)
        if d==-1:                 # include a, remainder 0
            A.append(a); return A
        if split is not None and d==1:
            # the mirror path is at d=-1 now: mirror decisions after split
            B=[x for x in A if x<split]+[x for (x,inc) in path if not inc]
            B.append(a); return B
        if d==0 and split is None:
            split=a; inc=False   # take exclude branch (d'=a); mirror = include branch
        elif d<-1: inc=False
        else: inc=True           # d>1, d==1, or d==0 after split (take include arbitrarily)
        if d==0 and split is not None and a!=split: inc=True
        if split is not None: path.append((a,inc))
        if inc: A.append(a); s=2*(s-a)
        else: s=2*s
        assert 0<=s<=2*(a+1)+2
        a+=1
    return None
def check(n):
    A=rebuild(n); M=max(A)
    lhs=n*2**(M-n); rhs=sum(a*2**(M-a) for a in A)
    return lhs==rhs, len(A), M-n
for n in [1,2,3,5,10,77,3817,9999,12345,54321,100003]:
    print(n, check(n))

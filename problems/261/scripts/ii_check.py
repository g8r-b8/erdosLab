# (1) brute force: does n/2^n = sum_{a in A} a/2^a for finite A subset (n, n+W], |A|>=2 ?
#     exact DP over s (integers): s_{n+1}=2n; include a: s->2(s-a) needs s>=a; exclude: s->2s needs s<=a+2.
# (2) orbit test: d=s-(a+1); d' = 2d - a*sgn(d) for |d|>1; success at d=-1; d=0 => mirror flag, then |d|==1 success.
def brute(n, W):
    st={2*n}
    for a in range(n+1, n+W+1):
        ns=set()
        for s in st:
            if s>=a:
                if s==a: return a   # include a -> remaining 0: finite rep found
                ns.add(2*(s-a))
            if s<=a+2: ns.add(2*s)
        st={s for s in ns if 0< s <= 2*(a+1)+2}
    return None
def orbit(n, W):
    d=n-2; a=n+1; mirror=False
    while a<=n+W:
        if d==-1 or (mirror and abs(d)==1): return a
        if d==0:
            mirror=True; d=a        # branches to -a and +a (mirror pair); track +a
        elif d==-1: pass
        elif d==1: d=2-a            # only live continuation (exclude -> cofinite)
        else: d=2*d-a*(1 if d>0 else -1)
        a+=1
    return None
bad=0
for n in range(1,400):
    b=brute(n,300); o=orbit(n,300)
    if b!=o: bad+=1; print('mismatch',n,b,o)
print('mismatches',bad)

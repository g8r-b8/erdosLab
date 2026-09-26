# Independent check: simulate the full set of live integer states s (no d/mirror bookkeeping) until some state equals a.
import sys
n=int(sys.argv[1]); a=n+1; st={2*n}
while True:
    if a in st: print(n,'finite rep ends at a =',a,'steps',a-n,'live states',len(st)); break
    ns=set()
    for s in st:
        if s>=a: ns.add(2*(s-a))
        if s<=a+2: ns.add(2*s)
    st={s for s in ns if 0<s<2*(a+1)+2}
    a+=1

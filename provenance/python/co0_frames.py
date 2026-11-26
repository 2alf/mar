"""Frame shapes of Co0 classes on the 24-dim Leech representation, from chi24 on powers.
chi24(g^k) = sum_{m | n, m | k} m * a_m, where the frame shape is prod_m m^{a_m} (a_m in Z)."""
import json
D=json.load(open('co0_data.json'))
pm={int(p):v for p,v in D['pmaps'].items()}; orders=D['orders']; chi=D['chi24']; names=D['names']; N=len(orders)
def factor(n):
    f=[]; d=2
    while d*d<=n:
        while n%d==0: f.append(d); n//=d
        d+=1
    if n>1: f.append(n)
    return f
def power(c,k):
    for p in factor(k): c=pm[p][c]
    return c
def frame(c):
    n=orders[c]; divs=[d for d in range(1,n+1) if n%d==0]
    t={k:chi[power(c,k)] for k in divs}       # chi(g^k)
    # chi(g^k) = sum_{m|n} a_m * m * [m | k]; solve for a_m by Mobius over divisors
    a={}
    for m in divs:
        # f(m) := sum_{d | m} d*a_d = chi(g^m)  =>  m*a_m = sum_{d|m} mu(m/d) chi(g^d)
        s=0
        for d in divs:
            if m%d==0:
                q=m//d; mu=1
                fq=factor(q)
                if len(set(fq))!=len(fq): mu=0
                else: mu=(-1)**len(fq)
                s+=mu*t[d]
        assert s%m==0,(names[c],m,s)
        if s: a[m]=s//m
    return a
FS=[frame(c) for c in range(N)]
ok=all(sum(m*e for m,e in f.items())==24 for f in FS)
print('degree check (sum m*a_m = 24) for all classes:',ok)
fmt=lambda f:'.'.join((f'{m}^{e}' if e!=1 else f'{m}') for m,e in sorted(f.items()))
json.dump({'frames':[{str(m):e for m,e in f.items()} for f in FS],'frame_str':[fmt(f) for f in FS]},open('co0_frames.json','w'))
from collections import Counter
cnt=Counter(fmt(f) for f in FS)
print('distinct frame shapes:',len(cnt),' sample:',[ (names[c],fmt(FS[c])) for c in range(8)])

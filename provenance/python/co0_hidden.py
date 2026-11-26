"""Power-map symmetries of Co0 = 2.Co1 (orders, centralizer orders, all prime power maps) and whether
they exchange classes with different Conway-moonshine series T^s_g (coefficients from Duncan–Mack-Crane,
validated against ctbllib characters)."""
import os as _os
def _find_root():
    d = _os.path.dirname(_os.path.abspath(__file__))
    while not _os.path.exists(_os.path.join(d, 'lakefile.toml')):
        nd = _os.path.dirname(d)
        if nd == d:
            raise RuntimeError('repository root (lakefile.toml) not found')
        d = nd
    return d
ROOT = _find_root()
import json, sys
sys.path.insert(0,(ROOT + '/data'))
import sporadic_survey as S
D=json.load(open('co0_data.json')); Lb=json.load(open('co0_labels.json'))
names=D['names']; pm={int(p):v for p,v in D['pmaps'].items()}; N=len(names)
key=[(o,c) for o,c in zip(D['orders'],D['cent'])]; coef=[tuple(c) for c in Lb['coef']]; lab=Lb['lab']
par=[[] for _ in range(N)]
for d in range(N):
    for p,m in pm.items():
        if m[d]!=d: par[m[d]].append((d,p))
def ac(D):
    D=[set(x) for x in D]; ch=True
    while ch:
        ch=False
        for c in range(N):
            new={d for d in D[c] if all(pm[p][d] in D[pm[p][c]] for p in pm) and all(any(pm[p][x]==d for x in D[e]) for e,p in par[c])}
            if new!=D[c]: D[c]=new; ch=True
            if not new: return None
        for c in range(N):
            if len(D[c])==1:
                (d,)=D[c]
                for c2 in range(N):
                    if c2!=c and d in D[c2]: D[c2]=D[c2]-{d}; ch=True
                    if not D[c2]: return None
        for d in range(N):
            hold=[c for c in range(N) if d in D[c]]
            if not hold: return None
            if len(hold)==1 and len(D[hold[0]])>1: D[hold[0]]={d}; ch=True
    return D
def solve(D):
    D=ac(D)
    if D is None: return None
    c=min((c for c in range(N) if len(D[c])>1),key=lambda c:len(D[c]),default=None)
    if c is None: return [next(iter(x)) for x in D]
    for d in sorted(D[c]):
        E=[set(x) for x in D]; E[c]={d}; r=solve(E)
        if r: return r
    return None
def verify(pi): return sorted(pi)==list(range(N)) and all(key[pi[c]]==key[c] and all(pi[pm[p][c]]==pm[p][pi[c]] for p in pm) for c in range(N))
D0=ac([{d for d in range(N) if key[d]==key[c]} for c in range(N)])
TA=S.table_auts('2.Co1',N) if False else None
moved=[]; W=[]
for c in range(N):
    for d in sorted(D0[c]):
        if d>c and coef[c]!=coef[d]:
            E=[set(x) for x in D0]; E[c]={d}; r=solve(E)
            if r and verify(r):
                k=next(m for m in range(len(coef[c])) if coef[c][m]!=coef[d][m])
                moved.append((names[c],lab[c],names[d],lab[d],k-1,coef[c][k],coef[d][k])); W.append({'c':c,'d':d,'perm':r})
print('classes with nontrivial AC domain:',sum(len(x)>1 for x in D0))
print('symmetric pairs with DIFFERENT Conway series:',len(moved))
for m in moved: print('   %s (%s) <-> %s (%s): first differing coeff q^%d: %d vs %d'%m)
json.dump(W,open('co0_witness.json','w'))

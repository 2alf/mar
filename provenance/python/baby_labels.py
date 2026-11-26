"""Do hidden power-map symmetries of 2.B move Hoehn's generalized-moonshine labels?
Maintained-arc-consistency search for permutations pi of the 247 classes of 2.B that commute
with all prime power maps and preserve (element order, centralizer order). Every witness is
re-verified from scratch against the raw definitions."""
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
import sys, csv
sys.path.insert(0,(ROOT + '/data'))
from ctparse import load
T=load('2.B',(ROOT + '/data/ctomonst.tbl'))
pm=T['pmaps']; key=[(o,c) for o,c in zip(T['orders'],T['cent'])]; N=len(key); names=T['names']
rows=list(csv.DictReader(open('baby_2B_table.tsv',encoding='utf8'),delimiter='\t'))
assert len(rows)==N
lab=[r['T_tg_label'] for r in rows]; Mgt=[r['M_class_gt'] for r in rows]; Bc=[r['B_class'] for r in rows]
mism=[(i,names[i],rows[i]['class_2B']) for i in range(N) if names[i].lower()!=rows[i]['class_2B'].lower()]
print('2.B classes',N,'| name mismatches GAP-derived vs TSV:',len(mism),mism[:6])
par=[[] for _ in range(N)]
for d in range(N):
    for p,m in pm.items():
        if m[d]!=d: par[m[d]].append((d,p))
def ac(D):
    D=[set(x) for x in D]
    ch=True
    while ch:
        ch=False
        for c in range(N):
            new={d for d in D[c] if all(pm[p][d] in D[pm[p][c]] for p in pm)
                 and all(any(pm[p][x]==d for x in D[e]) for e,p in par[c])}
            if new!=D[c]: D[c]=new; ch=True
            if not new: return None
        # injectivity / surjectivity
        for c in range(N):
            if len(D[c])==1:
                (d,)=D[c]
                for c2 in range(N):
                    if c2!=c and d in D[c2]: D[c2]=D[c2]-{d}; ch=True
                    if not D[c2]: return None
        for d in range(N):
            holders=[c for c in range(N) if d in D[c]]
            if not holders: return None
            if len(holders)==1 and len(D[holders[0]])>1: D[holders[0]]={d}; ch=True
    return D
D0=ac([{d for d in range(N) if key[d]==key[c]} for c in range(N)])
nontriv=[(names[c],sorted(names[x] for x in D0[c])) for c in range(N) if len(D0[c])>1]
print('classes with nontrivial domain after AC:',len(nontriv))
def solve(D):
    D=ac(D)
    if D is None: return None
    c=min((c for c in range(N) if len(D[c])>1),key=lambda c:len(D[c]),default=None)
    if c is None: return [next(iter(x)) for x in D]
    for d in sorted(D[c]):
        E=[set(x) for x in D]; E[c]={d}
        r=solve(E)
        if r: return r
    return None
def verify(pi):
    return sorted(pi)==list(range(N)) and all(key[pi[c]]==key[c] and all(pi[pm[p][c]]==pm[p][pi[c]] for p in pm) for c in range(N))
moved=[]; nopair=[]
for c in range(N):
    for d in sorted(D0[c]):
        if d>c and lab[c]!=lab[d]:
            E=[set(x) for x in D0]; E[c]={d}
            r=solve(E)
            if r and verify(r): moved.append((names[c],lab[c],Bc[c],Mgt[c],names[d],lab[d],Bc[d],Mgt[d]))
            elif r is None: nopair.append((names[c],names[d]))
print('pairs (c,d) in AC-domains with different labels and an actual symmetry c->d:',len(moved))
for m in moved: print('   %s [%s; B %s; M(gt) %s]  <->  %s [%s; B %s; M(gt) %s]'%m)
print('domain pairs with different labels but NO symmetry:',len(nopair),nopair[:10])

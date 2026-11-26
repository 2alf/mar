"""Co0 = 2.Co1 data from ctbllib: classes, orders, power maps, fusion to Co1, faithful characters
(from ARC("Co1","projectives",...)) and Co1 characters pulled back. Validated by norms."""
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
import re, sys, json
sys.path.insert(0,(ROOT + '/data'))
from ctparse import load
F=(ROOT + '/data/ctbllib_raw/ctoconja.tbl')
txt=open(F).read()
T=load('2.Co1',F); C=load('Co1',F); N=len(T['orders'])
a=txt.index('ALF("2.Co1","Co1",['); b=txt.index(']',a)
fus=[int(x)-1 for x in re.findall(r'\d+',txt[a+len('ALF("2.Co1","Co1",['):b])]
assert len(fus)==N
i=txt.index('ARC("Co1","projectives",["2.Co1",')+len('ARC("Co1","projectives",["2.Co1",')
j=i; d=0
while True:
    ch=txt[j]
    if ch=='[': d+=1
    elif ch==']':
        d-=1
        if d==0: break
    j+=1
body=txt[i:j+1]
rows=[[int(x) for x in r.split(',')] for r in re.findall(r'\[(-?\d+(?:,\s*-?\d+)*)\]',body)]
rows=[r for r in rows if len(r)==len(C['orders'])]
print('Co0 classes',N,'Co1 classes',len(C['orders']),'integer projective rows',len(rows),'degrees',[r[0] for r in rows[:6]])
seen={}; sign=[]
for c in range(N):
    k=fus[c]; sign.append(1 if k not in seen else -1); seen[k]=seen.get(k,0)+1
lifts=[seen[fus[c]] for c in range(N)]
def faithful(r): return [r[fus[c]]*sign[c] if lifts[c]==2 else 0 for c in range(N)]
def pull(r): return [r[fus[c]] for c in range(N)]
G=T['cent'][0]
def norm(x): return sum(G//T['cent'][c]*x[c]*x[c] for c in range(N))/G
chi24=faithful(rows[0])
print('norm chi24 =',norm(chi24),' single-lift nonzero:',[c for c in range(N) if lifts[c]==1 and rows[0][fus[c]]!=0][:5])
co1=[r for r in C['irr'] if r]
chi276=pull(co1[1]); print('chi276 degree',chi276[0],'norm',norm(chi276))
# Lambda^2 of chi24 should equal chi276 (on Co0): (chi(g)^2 - chi(g^2))/2
sq=T['pmaps'][2]
lam2=[(chi24[c]**2-chi24[sq[c]])//2 for c in range(N)]
print('Lambda^2(chi24) == chi276 :', lam2==chi276)
json.dump({'names':T['names'],'orders':T['orders'],'cent':T['cent'],'pmaps':{str(p):v for p,v in T['pmaps'].items()},
           'fus':fus,'co1names':C['names'],'chi24':chi24,'chi276':chi276,
           'co1irr':co1[:12],'projrows':rows[:6]},open('co0_data.json','w'))
print('names sample',T['names'][:20])

"""Faithful characters of 2.B from ctbllib's ARC("B","projectives",...) data; compute H2 = chi_185
on the 247 classes of 2.B and validate against Monster coefficients on monstrous-labelled classes."""
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
import re, sys, json, csv
sys.path.insert(0,(ROOT + '/data'))
from ctparse import load
txt=open('ctomonst.tbl').read()
i=txt.index('ARC("B","projectives",["2.B",[')+len('ARC("B","projectives",["2.B",')
# parse nested list
j=i; depth=0
while True:
    ch=txt[j]
    if ch=='[': depth+=1
    elif ch==']':
        depth-=1
        if depth==0: break
    j+=1
body=txt[i:j+1]
proj=json.loads(re.sub(r'\s+','',body)) if 'E(' not in body else None
if proj is None:
    # keep only integer-valued rows
    rows=re.findall(r'\[([-\d,\s]+)\]',body[1:-1]); proj=[[int(x) for x in r.split(',')] for r in rows]
print('projective rows parsed:',len(proj),' first degrees:',[r[0] for r in proj[:4]],' lengths:',set(len(r) for r in proj))
T2=load('2.B',(ROOT + '/data/ctomonst.tbl')); N=len(T2['orders'])
a=txt.index('ALF("2.B","B",['); b=txt.index(']',a)
fus=[int(x)-1 for x in re.findall(r'\d+',txt[a+len('ALF("2.B","B",['):b])]
# sign convention: first preimage +, second preimage -
seen={}
sign=[]
for c in range(N):
    k=fus[c]; sign.append(1 if k not in seen else -1); seen[k]=seen.get(k,0)+1
lifts=[seen[fus[c]] for c in range(N)]
chi185=[proj[0][fus[c]]*sign[c] if lifts[c]==2 else 0 for c in range(N)]
# check: classes with one lift must have value 0 in the projective character
print('single-lift classes with nonzero proj value:',[ (c,proj[0][fus[c]]) for c in range(N) if lifts[c]==1 and proj[0][fus[c]]!=0][:5])
# orthogonality: sum over 2.B classes |chi|^2 / |C(c)| == 1  (i.e. sum |G|/|C| |chi|^2 = |G|)
G=T2['cent'][0]
print('<chi185,chi185> =', sum(G//T2['cent'][c]*chi185[c]**2 for c in range(N))/G)
TM=load('M',(ROOT + '/data/ctomonst.tbl')); Mn={n:i for i,n in enumerate(TM['names'])}
rows=list(csv.DictReader(open('baby_2B_table.tsv',encoding='utf8'),delimiter='\t'))
ok=bad=0; badl=[]
for c,r in enumerate(rows):
    lab=r['T_tg_label']
    if lab in Mn:
        a2=1+TM['irr'][1][Mn[lab]]+TM['irr'][2][Mn[lab]]
        if a2==chi185[c]: ok+=1
        else: bad+=1; badl.append((r['class_2B'],lab,chi185[c],a2))
print('H2 vs Monster a2 on monstrous-labelled classes: agree',ok,'disagree',bad,badl[:6])
json.dump({'chi185':chi185,'fus':fus,'proj':proj[:3]},open('baby_proj.json','w'))

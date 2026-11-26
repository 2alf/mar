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
import csv, json, re, sys
from math import gcd
sys.path.insert(0,(ROOT + '/data')); sys.path.insert(0,(ROOT + '/ogg'))
from common import exact_divisors
D=json.load(open('co0_data.json'))
names=D['names']; orders=D['orders']; cent=D['cent']; pm={int(p):v for p,v in D['pmaps'].items()}; N=len(names)
rows={r['co0_class']:r for r in csv.DictReader(open('../conway/conway_table_expanded.tsv',encoding='utf8'),delimiter='\t')}
lab=[rows[c]['group_label_plain'].strip() for c in names]
coef=[[int(x) for x in rows[c]['coeffs_Ts2tau_qm1_to_q10'].split()] for c in names]
# (a) coefficients vs characters
chi24=D['chi24']; chi276=D['chi276']; proj=D['projrows']; fus=D['fus']
seen={};sign=[]
for c in range(N):
    k=fus[c]; sign.append(1 if k not in seen else -1); seen[k]=seen.get(k,0)+1
lifts=[seen[fus[c]] for c in range(N)]
chi2024=[proj[1][fus[c]]*sign[c] if lifts[c]==2 else 0 for c in range(N)]
print('(a) a1 == chi276 on all 167:', all(coef[i][2]==chi276[i] for i in range(N)))
print('    a2 == -(chi24+chi2024) on all 167:', all(coef[i][3]==-(chi24[i]+chi2024[i]) for i in range(N)))
# (b) CN power rule where both labels are plain n|h+W
plain=re.compile(r'^(\d+)(?:\|(\d+))?([-+](?:\d+(?:,\d+)*)?)?$')
def parse(s):
    m=plain.match(s)
    if not m: return None
    n=int(m.group(1)); h=int(m.group(2) or 1); r=m.group(3) or '-'; q=n//h
    W={1} if r=='-' else set(exact_divisors(q)) if r=='+' else {1}|{int(x) for x in r[1:].split(',')}
    return (n,h,frozenset(W))
P=[parse(s) for s in lab]
print('(b) plain-labelled classes:',sum(p is not None for p in P),'of',N,'; distinct labels:',len(set(lab)))
def rule(l,p):
    n,h,W=l; n2=n//gcd(n,p); h2=h//gcd(h,p); q=n2//h2
    return (n2,h2,frozenset(e for e in W if q%e==0))
tot=0; fails=[]
for i in range(N):
    for p,m in pm.items():
        if P[i] and P[m[i]] and m[i]!=i:
            tot+=1
            if P[m[i]]!=rule(P[i],p): fails.append((names[i],lab[i],p,names[m[i]],lab[m[i]]))
print('    CN power rule on plain->plain edges:',tot-len(fails),'ok,',len(fails),'fail; e.g.',fails[:4])
from collections import Counter
print('    level/order ratios (plain):',Counter(P[i][0]//orders[i] if P[i][0]%orders[i]==0 else ('nd',P[i][0],orders[i]) for i in range(N) if P[i]))
json.dump({'lab':lab,'coef':coef,'chi2024':chi2024},open('co0_labels.json','w'))

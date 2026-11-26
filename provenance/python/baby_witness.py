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
import sys, re, json
sys.path.insert(0,(ROOT + '/data'))
exec(open('baby_labels.py').read().split("moved=[]; nopair=[]")[0])
txt=open('ctomonst.tbl').read()
i=txt.index('ALF("2.B","B",['); j=txt.index(']',i)
fus=[int(x)-1 for x in re.findall(r'\d+',txt[i+len('ALF("2.B","B",['):j])]
assert len(fus)==N
TB=load('B',(ROOT + '/data/ctomonst.tbl')); chi2=TB['irr'][1]; assert chi2[0]==4371
print('fusion check vs TSV B_class:', all(TB['names'][fus[c]]==Bc[c] for c in range(N)))
W=[]
for c in range(N):
    for d in sorted(D0[c]):
        if d>c and lab[c]!=lab[d]:
            E=[set(x) for x in D0]; E[c]={d}
            r=solve(E)
            if r and verify(r):
                h1c,h1d=1+chi2[fus[c]],1+chi2[fus[d]]
                print(f'{names[c]:4s}<->{names[d]:4s} B-classes {TB["names"][fus[c]]}/{TB["names"][fus[d]]}  H1 = {h1c} vs {h1d}  {"DIFFERENT" if h1c!=h1d else "equal (same B-class or same chi2)"}')
                W.append({'c':c,'d':d,'perm':r,'h1':[h1c,h1d]})
json.dump({'witnesses':W,'fus':fus,'chi2B':chi2,'names':names},open('baby_witness.json','w'))

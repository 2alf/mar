"""Hidden power-map symmetries of all 26 sporadic groups (ctbllib 1.3.11 data).
For each group: |Aut(orders+power maps)|, |Aut(orders+power maps+centralizer orders)|,
|Aut(character table)| (ctbllib's stored table automorphisms), and the extra atoms."""
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
import sys, re
sys.path.insert(0, (ROOT + '/data'))
import autgen
from ctparse import load
FILES={'M11':'ctomathi','M12':'ctomathi','M22':'ctomathi','M23':'ctomathi','M24':'ctomathi',
 'J1':'ctoconja','J2':'ctoconja','J3':'ctoconja','Co3':'ctoconja','Co2':'ctoconja','Co1':'ctoconja','J4':'ctoconja',
 'HS':'ctospora','McL':'ctospora','He':'ctospora','Ru':'ctospora','Suz':'ctospora','ON':'ctospora',
 'HN':'ctospora','Ly':'ctospora','Th':'ctospora','Fi22':'ctofisc1','Fi23':'ctofisc2','F3+':'ctofisc2'}
def path(g): return (ROOT + '/data/')+('ctbllib_raw/'+FILES[g]+'.tbl' if g in FILES else 'ctomonst.tbl')
def mot_args(g):
    txt=open(path(g)).read(); s=txt[txt.index('MOT("%s",'%g)+4:]
    depth=0; cur=''; args=[]; instr=False
    for ch in s:
        if ch=='"': instr=not instr
        if not instr:
            if ch in '([': depth+=1
            if ch in ')]': depth-=1
            if depth==-1: args.append(cur); break
            if ch==',' and depth==0: args.append(cur); cur=''; continue
        cur+=ch
    return args
def table_auts(g, N):
    a=mot_args(g)[5].strip()
    assert a.startswith('[') and a.endswith(']'), a[:50]
    inner=a[1:-1]
    depth=0; cur=''; parts=[]
    for ch in inner:
        if ch=='(': depth+=1
        if ch==')': depth-=1
        if ch==',' and depth==0: parts.append(cur); cur=''
        else: cur+=ch
    if cur.strip(): parts.append(cur)
    def perm_of(t):
        p=list(range(N))
        for c in re.findall(r'\(([\d,\s]+)\)',t):
            xs=[int(x)-1 for x in c.split(',')]
            for x,y in zip(xs,xs[1:]+xs[:1]): p[x]=y
        return tuple(p)
    G=[perm_of(t) for t in parts if t.strip()]
    e=tuple(range(N)); S={e}; fr=[e]
    while fr:
        x=fr.pop()
        for h in G:
            y=tuple(h[i] for i in x)
            if y not in S: S.add(y); fr.append(y)
    return S
def atoms(A):
    sups=sorted({frozenset(i for i in range(len(g)) if g[i]!=i) for g in A if g!=tuple(range(len(g)))},key=len)
    at=[]
    for s_ in sups:
        if not any(a<=s_ for a in at): at.append(s_)
    return at
if __name__=='__main__':
    groups=sys.argv[1:] or ['M11','M12','J1','M22','J2','M23','HS','J3','M24','McL','He','Ru','Suz','ON','Co3','Co2','Fi22','HN','Ly','Th','Fi23','Co1','J4','F3+','B','M']
    for g in groups:
        T=load(g,path(g)); N=len(T['orders'])
        A1=set(autgen.pm_auts(T))
        T2=dict(T); T2['orders']=[(o,c) for o,c in zip(T['orders'],T['cent'])]
        A2=set(autgen.pm_auts(T2))
        TA=table_auts(g,N)
        ok=TA<=A2
        extra=[sorted(T['names'][i] for i in a) for a in atoms(A2) if not any(frozenset(i for i in range(N) if h[i]!=i)==a for h in TA)]
        print(f"{g:5s} classes {N:3d}  |Aut(pm,ord)|={len(A1):6d}  |Aut(pm,ord,cent)|={len(A2):6d}  |Aut(table)|={len(TA):6d}  TA<=A:{ok}  hidden index={len(A2)//len(TA)}  extra atoms:{extra}", flush=True)

"""Generic parser for a MOT(...) table in ctomonst.tbl: centralizers, power maps, and the
irreducible rows that are plain integer lists (others reported as None)."""
import re, sys, json
def load(name, path='ctomonst.tbl'):
    txt=open(path).read()
    s=txt[txt.index('MOT("%s",'%name)+len('MOT('):]
    toks=re.findall(r'"[^"]*"|-?[0-9]+|[][(),]|[A-Za-z_]+|[^\s]',s)
    pos=[0]
    def parse():
        t=toks[pos[0]]
        if t=='[':
            pos[0]+=1; lst=[]; cur=None; have=False
            while True:
                t=toks[pos[0]]
                if t==']':
                    pos[0]+=1
                    if have: lst.append(cur)
                    return lst
                if t==',':
                    pos[0]+=1; lst.append(cur if have else None); cur=None; have=False; continue
                cur=parse(); have=True
        if t=='(':
            depth=0; out=[]
            while True:
                tt=toks[pos[0]]; out.append(tt)
                if tt=='(': depth+=1
                if tt==')': depth-=1
                pos[0]+=1
                if depth==0: return ('expr',' '.join(out))
        pos[0]+=1
        if t.startswith('"'): return t
        if re.match(r'-?\d+$',t): return int(t)
        # identifier possibly followed by (...) e.g. E(7) or GALOIS
        if pos[0]<len(toks) and toks[pos[0]]=='(':
            sub=parse(); return ('call',t,sub)
        return t
    ident=parse(); pos[0]+=1; text=parse(); pos[0]+=1; cent=parse(); pos[0]+=1; pm=parse(); pos[0]+=1
    irr=parse()
    primes=[p+1 for p,m in enumerate(pm) if m is not None]
    pmaps={p:[x-1 for x in pm[p-1]] for p in primes}
    n=len(cent)
    def ppart(i,p):
        seen={i:0}; seq=[i]
        while True:
            j=pmaps[p][seq[-1]]
            if j in seen: return seen[j]
            seen[j]=len(seq); seq.append(j)
    orders=[]
    for i in range(n):
        o=1
        for p in primes: o*=p**ppart(i,p)
        orders.append(o)
    cnt={}; names=[]
    for o in orders:
        k=cnt.get(o,0); cnt[o]=k+1
        names.append(f"{o}{chr(65+k) if k<26 else chr(65+k//26-1)+chr(65+k%26)}")
    rows=[r if isinstance(r,list) and all(isinstance(x,int) for x in r) else None for r in irr] if isinstance(irr,list) else []
    return dict(name=name,cent=cent,pmaps=pmaps,orders=orders,names=names,irr=rows,primes=primes)
if __name__=='__main__':
    for nm in ['B','2.B']:
        T=load(nm)
        degs=[r[0] if r else None for r in T['irr'][:8]]
        print(nm,'classes',len(T['cent']),'primes',T['primes'],'first degrees',degs)
        print('  |G| =',T['cent'][0])
        print('  class eq:', sum(T['cent'][0]//c for c in T['cent'])==T['cent'][0])

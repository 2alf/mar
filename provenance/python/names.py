import re,sys
txt=open(sys.argv[1]).read()
start=txt.index('MOT("M",')
s=txt[start+len('MOT('):]
# tokenizer for GAP literal subset
toks=re.findall(r"\"[^\"]*\"|-?[0-9]+|[][(),]|[A-Za-z_]+",s)
pos=0
def parse():
    global pos
    t=toks[pos]
    if t=='[':
        pos+=1; lst=[]; cur=None; have=False
        while True:
            t=toks[pos]
            if t==']':
                pos+=1
                if have: lst.append(cur)
                return lst
            if t==',':
                pos+=1; lst.append(cur if have else None); cur=None; have=False; continue
            cur=parse(); have=True
    elif t=='(':
        # permutation cycles - skip to matching
        depth=0
        while True:
            if toks[pos]=='(': depth+=1
            if toks[pos]==')': depth-=1
            pos+=1
            if depth==0: return 'cyc'
    else:
        pos+=1
        if t.startswith('"'): return t
        if re.match(r'-?\d+$',t): return int(t)
        return t
args=[]
args.append(parse()); assert toks[pos]==','; pos+=1
args.append(parse()); pos+=1
cent=parse(); pos+=1
pm=parse()
print('id',args[0],'nclasses',len(cent))
primes=[p+1 for p,m in enumerate(pm) if m is not None]
print('powermap primes',primes)
n=len(cent)
def ppart(i,p):
    seq=[i]; seen={i:0}
    while True:
        j=pm[p-1][seq[-1]-1]
        if j in seen: return seen[j]
        seen[j]=len(seq); seq.append(j)
orders=[]
for i in range(1,n+1):
    o=1
    for p in primes:
        o*=p**ppart(i,p)
    orders.append(o)
names=[];cnt={}
for o in orders:
    k=cnt.get(o,0); cnt[o]=k+1
    names.append(f"{o}{chr(65+k)}")
open(sys.argv[2],'w').write('\n'.join(f"{a}\t{o}\t{c}" for a,o,c in zip(names,orders,cent))+'\n')
print(' '.join(names))
import json
json.dump({str(p):pm[p-1] for p in primes},open('pmaps.json','w'))

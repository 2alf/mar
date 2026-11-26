"""Regenerate MonsterCN/Data/Catalogue.lean (distinct labels of CNTable.lean, first-occurrence order)."""
rows=[l for l in open('../MonsterCN/Data/CNTable.lean',encoding='utf8').read().split('\n') if l.strip().startswith('⟨')]
seen=[]
for r in rows:
    t=r.strip().split(' /-')[0].rstrip(',')
    if t not in seen: seen.append(t)
hdr=open('../MonsterCN/Data/Catalogue.lean',encoding='utf8').read().split('def catalogue')[0]
open('../MonsterCN/Data/Catalogue.lean','w',encoding='utf8').write(hdr+'def catalogue : List CNLabel := [\n'+',\n'.join('  '+x for x in seen)+'\n]\n\nend MonsterCN\n')
print(len(seen))

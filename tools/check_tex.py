"""Mechanical sanity checks for mar.tex (no LaTeX installation available)."""
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
import re
from collections import Counter

s = open((ROOT + '/paper/mar.tex'), encoding='utf8').read()
b = Counter(re.findall(r'\\begin\{([A-Za-z*]+)\}', s))
e = Counter(re.findall(r'\\end\{([A-Za-z*]+)\}', s))
print('environment mismatches:', {k: (b[k], e[k]) for k in set(b) | set(e) if b[k] != e[k]})
print('brace balance ({ minus }):', s.count('{') - s.count('}'))
cites = {x.strip() for c in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]*)\}', s) for x in c.split(',')}
bib = set(re.findall(r'\\bibitem\{([^}]*)\}', s))
print('undefined cites:', cites - bib, '| unused bibitems:', bib - cites)
refs = set(re.findall(r'\\ref\{([^}]*)\}', s))
labs = set(re.findall(r'\\label\{([^}]*)\}', s))
print('undefined refs:', refs - labs)
print('begin{document} count:', s.count('\\begin{document}'), '| end{document} count:', s.count('\\end{document}'))
odd = [i + 1 for i, l in enumerate(s.split('\n')) if (l.count('$') - l.count('\\$')) % 2 == 1]
print('lines with odd $ count:', odd)
print('non-ASCII characters:', sorted({ch for ch in s if ord(ch) > 127}))

# usage: python3 extract.py FILE NAME  -> prints docstring + def block verbatim
import sys,re
f,name=sys.argv[1],sys.argv[2]
L=open(f).read().split('\n')
i=[k for k,l in enumerate(L) if re.match(r'^(noncomputable )?(def|abbrev) '+re.escape(name)+r'(\s|$)',l)][0]
s=i
if L[i-1].rstrip().endswith('-/'):
    s=i-1
    while not L[s].lstrip().startswith('/--'): s-=1
e=i+1
while e<len(L) and L[e].strip()!='' and not re.match(r'^(def|theorem|lemma|/--|instance|structure|abbrev|end |namespace|open|variable|section)',L[e]): e+=1
print('\n'.join(L[s:e]))

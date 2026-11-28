"""Parse every printed new row, authenticate inputs and run exact independent checks."""
from pathlib import Path
import re,json,hashlib,subprocess,sys,os
from collections import defaultdict,Counter
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[2]
manifest=json.loads((HERE/'INPUTS.json').read_text())
for item in manifest['files']:
 p=REPO/item['path'];assert p.stat().st_size==item['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],str(p)
text=(REPO/'manuscripts/quartic_v22.tex').read_text()
blocks=re.findall(r'% V22_ROW (\d+) ([^\n]+)\n(.*?)% V22_END_ROW',text,re.S)
rows=json.loads((HERE/'inputs/quadrics.json').read_text())['residuals'];assert len(blocks)==len(rows)==147
for index,((num,name,block),row) in enumerate(zip(blocks,rows),1):
 assert int(num)==index and name==row['name']
 expression=block.split('={}&',1)[1].split(r'\end{aligned}',1)[0]
 expression=re.sub(r'\s+|\\\\|&','',expression)
 parsed=defaultdict(int)
 for token in re.findall(r'[+-]?[^+-]+',expression):
  sign=-1 if token.startswith('-') else 1;t=token.lstrip('+-');co=re.match(r'\d+',t);a=int(co[0]) if co else 1
  if co:t=t[len(co[0]):]
  power=0
  if t.startswith('C'):
   m=re.match(r'C(?:\^\{(\d+)\})?',t);power=int(m[1] or 1);t=t[len(m[0]):]
  mono=[]
  while t:
   m=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',t);assert m,(index,t)
   mono.extend([int(m[1])]*int(m[2] or 1));t=t[len(m[0]):]
  parsed[power,tuple(sorted(mono))]+=sign*a
 expected=defaultdict(int)
 for t in row['terms']:expected[t['parameterPower'],tuple(sorted(t['monomial']))]+=int(t['coefficient'])
 assert dict(parsed)==dict(expected),(index,name)
# Re-render the canonical literal, including order and terminal-newline convention.
C=331**21;poly=defaultdict(int)
for row in rows:
 terms=[(tuple(t['monomial']),int(t['coefficient'])*C**t['parameterPower']) for t in row['terms']]
 for m,a in terms:
  for n,b in terms:poly[tuple(sorted(m+n))]+=a*b
parts=[]
for m,a in sorted(poly.items()):
 if not a:continue
 factors=['x'+str(i)+('^'+str(n) if n>1 else '') for i,n in sorted(Counter(m).items())]
 coefficient='' if abs(a)==1 and factors else str(abs(a))
 body='*'.join(([coefficient] if coefficient else [])+factors)
 parts.append(('-' if a<0 else '+' if parts else '')+body)
assert ''.join(parts).encode('ascii')==(HERE/'inputs/expanded175.txt').read_bytes()
env={k:v for k,v in os.environ.items() if not any(word in k.upper() for word in ['TOKEN','SECRET','PASSWORD','API_KEY']) and not k.startswith(('GH_','GITHUB_','OPENAI_','ANTHROPIC_'))}
for script in ['verify175.py','verify_interpretation.py']:
 subprocess.run([sys.executable,'-X','utf8','-B',str(HERE/script)],cwd=REPO,env=env,check=True,stdout=subprocess.PIPE)
subprocess.run([sys.executable,'-X','utf8','-B',str(REPO/'research/version21/construction/check.py')],cwd=REPO,env=env,check=True,stdout=subprocess.PIPE)
print('All 147 printed rows match. All 147 direct interpretation checks pass. Expansion and canonical 73,080-byte literal agree.')

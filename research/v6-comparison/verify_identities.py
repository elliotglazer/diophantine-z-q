"""Independently expand the emitted G2/G9 circuits over Q[f0,f1]."""
from fractions import Fraction as Q
import json,sys
from pathlib import Path

def add(a,b):
 c=a.copy()
 for k,v in b.items():
  c[k]=c.get(k,Q(0))+v
  if not c[k]:del c[k]
 return c

def scale(a,q):return {k:v*q for k,v in a.items() if v*q}
def mul(a,b):
 c={}
 for (i,j),u in a.items():
  for (k,l),v in b.items():c=add(c,{(i+k,j+l):u*v})
 return c

def fm(a,b):return (add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0])))
def fa(a,b):return (add(a[0],b[0]),add(a[1],b[1]))
def fs(a,q):return tuple(scale(x,q) for x in a)
ONE={(0,0):Q(1)}

def verify(raw):
 gates={g['coordinateId']:g for g in raw['gates']};values=raw['values'];checks=[]
 for prefix,degree in [(side+str(i),2 if i==1 else 9) for side in ['U','V'] for i in range(5)]:
  cache={}
  for j in range(2):
   t=values[prefix+'.f.'+str(j)]['terms'];assert len(t)==1 and len(t[0]['monomial'])==1 and Q(t[0]['coefficient'])==1
   cache[t[0]['monomial'][0]]={(1-j,j):Q(1)}
  def coord(i):
   if i not in cache:
    g=gates[i];assert g['operation']=='quadratic_assignment';cache[i]=expr(g['expression'])
   return cache[i]
  def expr(ts):
   out={}
   for t in ts:
    assert t['sPower']==0;p={(0,0):Q(t['coefficient'])}
    for i in t['monomial']:p=mul(p,coord(i))
    out=add(out,p)
   return out
  w=fm(({(0,0):Q(11)},{(0,0):Q(-6)}),fm(({(1,0):Q(1)},{(0,1):Q(1)}),({(1,0):Q(1)},{(0,1):Q(1)})))
  power=(ONE,{});expected=(ONE,{});a=Q(1)
  for j in range(1,degree+1):
   a=Q(-2,5) if j==1 else a*Q(4*j-5,4*j+1);power=fm(power,w);expected=fa(expected,fs(power,a))
  actual=tuple(expr(values['log'+prefix+'.polynomial.'+str(j)]['terms']) for j in range(2))
  assert actual==expected,prefix
  checks.append({'point':prefix,'degree':degree,'status':'exact_polynomial_identity'})
 # These are the exact exponents in the emitted quotient chain.
 e2=2;e4=2*e2;e8=2*e4;e16=2*e8;e24=e16+e8;e40=e24+e16;e80=2*e40
 assert e24-e2==22 and e80-e2==78
 return {'logarithmCircuits':checks,'weightExponentIdentities':[22,78],'scope':'Exact symbolic emitted logarithm identities and exponent identities; denominator nonvanishing is proved in README.md'}
if __name__=='__main__':print(json.dumps(verify(json.loads(Path(sys.argv[1]).read_text())),indent=2))

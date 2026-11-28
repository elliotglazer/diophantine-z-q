"""Independent exact checks of the new 175 arithmetic constants and final table.
Reads contributor data only; does not import or execute contributor programs.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict, Counter
from math import gcd, prod, isqrt
import json, hashlib, re

BASE=Path(__file__).resolve().parents[1]
REPO=BASE.parents[1]
SRC=BASE/'construction/inputs'
OUTPUT=REPO/'build/version22'
OUTPUT.mkdir(parents=True,exist_ok=True)
data=json.loads((SRC/'quadrics.json').read_text())
C=331**21
rows=[]
for row in data['residuals']:
    p=defaultdict(int)
    for t in row['terms']:
        assert len(t['monomial'])<=2 and all(1<=v<=175 for v in t['monomial'])
        assert t['parameterPower']>=0
        p[tuple(sorted(t['monomial']))]+=int(t['coefficient'])*C**t['parameterPower']
    rows.append({m:c for m,c in p.items() if c})
poly=defaultdict(int)
for p in rows:
    for m,a in p.items():
        for n,b in p.items(): poly[tuple(sorted(m+n))]+=a*b
poly={m:c for m,c in poly.items() if c}
assert len(rows)==147 and len(poly)==3196 and max(map(len,poly))==4
assert set(v for m in poly for v in m)==set(range(1,176))
assert poly[(1,1,1,1)]==1 and gcd(*poly.values())==1
# Parse the actual decimal expression, independently of its term order.
literal=(SRC/'expanded175.txt').read_bytes()
assert len(literal)==73080 and literal.isascii() and not literal.endswith(b'\n')
parsed={}
for chunk in re.findall(r'[+-]?[^+-]+',literal.decode()):
    sign=-1 if chunk.startswith('-') else 1
    factors=chunk.lstrip('+-').split('*'); coeff=sign; mon=[]
    for f in factors:
        if f.startswith('x'):
            hit=re.fullmatch(r'x([1-9][0-9]*)(?:\^([1-4]))?',f); assert hit
            mon.extend([int(hit[1])]*int(hit[2] or 1))
        else: assert f.isdigit(); coeff*=int(f)
    mon=tuple(sorted(mon)); assert mon not in parsed
    parsed[mon]=coeff
assert parsed==poly

def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return out
def add(a,b):
    out=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):out[i]+=x
    for i,x in enumerate(b):out[i]+=x
    return out
radii=[77,23,21,75,51]
P=[F(1)]
for a in radii:P=mul(P,[-a*a,1])
assert P==list(map(F,[-20236648618580625,98933750608581,-151547683050,77366218,-15125,1]))
assert 1127*32-(-1568)*77==156800==2**7*5**2*7**2
for t,u in [(F(23,32),0),(F(21,32),1),(F(-75,32),2401),(F(51,32),F(-343,32))]:
    assert (1127-1568*t)/(32*t+77)==u
assert 32*F(-77,32)+77==0
def support(n):
    n=abs(n); out=set(); d=2
    while d*d<=n:
        if n%d==0:
            out.add(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.add(n)
    return out
S={2,3,5,7,11,13,17,37,41,2399}
contacts=sorted(set(radii+[-a for a in radii]))
extra=set()
for a in contacts:
    extra|=support(a)
    for b in contacts:
        if a!=b:extra|=support(a-b)
Gamma=S|extra
assert Gamma==S|{19,23}
J=prod(Gamma); assert J==811898089212210
cal=F(74712001,10**6)*2**68*3**16*5**16*7**4*J**2*prod(F(p+1,p) for p in Gamma)
assert 2**68<cal<2**249
primes=[p for p in range(2,1001) if all(p%d for d in range(2,isqrt(p)+1))]
euler=prod(F(p+1,p) for p in primes if p not in Gamma)
assert euler<F(21,10)
# The source's exponential endpoint is reduced to this rational inequality.
assert 2**21*(1-F(2835,36036))>526500
assert 331**97>2**810
assert 360*331**97+2500<F(331**194,2)
# Exact depressed scalar identity.
r=mul(mul([2401,2400],[343,375]),[1,1])
e=F(-1081567619,25920000)
w=[F(34981,36000),1]
dep=add(add([e],[900000*x for x in mul(mul(w,w),w)]),[-F(1053721,480)*x for x in w])
assert r==dep
W=[34981,36000]
recip=add(add(mul(mul(W,W),W),[-3161163*x for x in W]),[-2163135238])
assert recip==[2*25920000*x for x in r]
assert 1081567619==11*47*1019*2053
assert 25920000==2**9*3**4*5**4
assert 47*1019*2053<2**27
k=2**20
for x in range(331):
    s=k*x*x%331
    rx=sum(int(a)*pow(s,i,331) for i,a in enumerate(r))%331
    emod=e.numerator*pow(e.denominator,-1,331)%331
    assert rx and (rx-emod)%331
assert r[3]%331 and k%331
assert (2**9*e).denominator%2 and (-(2**9*e).numerator*pow((2**9*e).denominator,-1,8))%8==3
assert 7*pow(331,43,8)%8==5
record={'scope':'Finite identities and bounds only, not an independent arithmetic acceptance.',
 'base':'dda0439aa44a63a05d4ef7c58230caed6df8e628','variables':175,'quadrics':147,'monomials':3196,
 'coefficient_bits':max(abs(c) for c in poly.values()).bit_length(),
 'largest_absolute_coefficient':str(max(abs(c) for c in poly.values())),
 'plain_bytes':len(literal),'plain_sha256':hashlib.sha256(literal).hexdigest(),
 'quadrics_sha256':hashlib.sha256((SRC/'quadrics.json').read_bytes()).hexdigest(),
 'contact_constant':str(cal),'contact_bound_margin_fraction':str(1-cal/F(2**249)),
 'small_prime_euler_product':str(euler),'anchor_residues_checked':331}
assert record['coefficient_bits']==802
(OUTPUT/'finite-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))

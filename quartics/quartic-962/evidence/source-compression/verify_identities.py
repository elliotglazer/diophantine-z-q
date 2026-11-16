"""Independent exact checks of the two local algebraic transformations.

No baseline builder or compiler is imported. Polynomial keys are exponent
tuples in the variables C,e,p,s,q,U. Integer arithmetic is exact.
"""
from itertools import product
import json
from pathlib import Path

N=6
def add(*ps):
    out={}
    for p in ps:
        for m,c in p.items():
            out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def scale(p,c): return {m:v*c for m,v in p.items() if v*c}
def neg(p): return scale(p,-1)
def sub(p,q): return add(p,neg(q))
def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            k=tuple(a+b for a,b in zip(m,n))
            out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def sq(p): return mul(p,p)
one={(0,)*N:1}
variables=[]
for i in range(N):
    key=[0]*N
    key[i]=1
    variables.append({tuple(key):1})
C,e,p,s,q,U=variables
z=mul(C,e)
old_first=sub(sq(p),mul(C,mul(sub(one,e),add(one,scale(e,3)))))
new_first=sub(mul(C,sq(p)),mul(sub(C,z),add(C,scale(z,3))))
assert new_first==mul(C,old_first)
old_H=mul(C,mul(e,sub(C,sq(U))))
new_H=mul(z,sub(C,sq(U)))
assert old_H==new_H
old_second=sub(mul(C,sq(q)),mul(sub(sq(s),old_H),add(sq(s),scale(old_H,3))))
new_second=sub(mul(C,sq(q)),mul(sub(sq(s),new_H),add(sq(s),scale(new_H,3))))
assert old_second==new_second

primes=(2,3,5,7,11,13,17)
old_values=set()
new_chains=set()
for bits in product((0,1),repeat=8):
    v=1-2*bits[7]
    chain=[v]
    for prime,bit in zip(primes,bits[:7]):
        v*=1+(prime-1)*bit
        chain.append(v)
    assert chain[0]**2==1
    for prime,left,right in zip(primes,chain,chain[1:]):
        assert right**2-(prime+1)*right*left+prime*left**2==0
        assert left!=0 and right!=0
        assert right//left in (1,prime)
    old_values.add(v)
    new_chains.add(tuple(chain))
assert len(old_values)==len(new_chains)==256
report={
    'pole_first_residual':'new(Ce)=C*old',
    'pole_second_residual':'new(Ce)=old',
    'required_domain':'C != 0, retained from baseline',
    'correction_chains_checked':len(new_chains),
    'correction_values':len(old_values),
    'status':'exact polynomial identities and all forward correction choices checked; converse proved in PROOF.md'
}
here=Path(__file__).resolve().parent
(here/'identity-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

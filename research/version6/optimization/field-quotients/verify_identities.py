"""Independent exact checks of the local quotient transformations.

Uses formal polynomials over Q, not sampled arithmetic. Ordering arguments and
the inherited nonzero ordinate lemma are stated separately in EQUIVALENCE.md.
"""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

class P(dict):
    def __add__(self, other):
        if not isinstance(other, P): other=P({():Q(other)})
        out=defaultdict(Q,self)
        for m,c in other.items(): out[m]+=c
        return P({m:c for m,c in out.items() if c})
    __radd__=__add__
    def __neg__(self): return P({m:-c for m,c in self.items()})
    def __sub__(self, other): return self+-as_p(other)
    def __rsub__(self, other): return as_p(other)+-self
    def __mul__(self, other):
        other=as_p(other); out=defaultdict(Q)
        for m,c in self.items():
            for n,d in other.items(): out[tuple(sorted(m+n))]+=c*d
        return P({m:c for m,c in out.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        out=as_p(1)
        for _ in range(n): out=out*self
        return out
def as_p(x): return x if isinstance(x,P) else P({():Q(x)})
def v(x): return P({(x,):Q(1)})
def fm(a,b): return (a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def fa(a,b): return tuple(x+y for x,y in zip(a,b))
def fn(a): return tuple(-x for x in a)
checks=[]
def check(name,a,b):
    assert a==b,name
    checks.append(name)

x,y,m,D=map(v,['x','y','m','D'])
check('doubling positivity numerator identity',
      4*y*y*(m*m-2*x)-(x*x+D)**2,
      (2*y*m-(3*x*x-D))*(2*y*m+(3*x*x-D))-8*x*(y*y-x*x*x+D*x))
a,b=map(v,['a','b'])
check('field quotient determinant', a*a-2*b*b, fm((a,b),(a,-b))[0])
check('field conjugate product imaginary component',fm((a,b),(a,-b))[1],P())
B=(v('b0'),v('b1')); Z=(v('z0'),v('z1')); X=(v('x0'),v('x1'))
H=(v('h0'),v('h1')); L=(v('l0'),v('l1')); R=(v('r0'),v('r1'))
# b*l+x*h = b*(l-z*h)+(b*z+x)*h.
check('paired log quotient fusion identity',fa(fm(B,L),fm(X,H)),
      fa(fm(B,fa(L,fn(fm(Z,H)))),fm(fa(fm(B,Z),X),H)))
# x*r+y*zS = (x+y*z)*r-y*(z*r-zS).
check('scalar local parameter ratio fusion identity',fa(fm(X,R),fm(B,H)),
      fa(fm(fa(X,fm(B,Z)),R),fn(fm(B,fa(fm(Z,R),fn(H))))))
d,i,e,r,q=map(v,['delta','di','ep','R','q'])
check('R inverse reconstruction',e*(r*d)-1,d*(e*r-i)+(d*i-1))
check('q1 reconstruction residual',d*(q-e*i**3), (d*q-e*i*i)-e*i*i*(d*i-1))
w,u,n,j=map(v,['w0','w1','nw','wi'])
check('trace quotient reconstruction',w*(n-(w*w-2*u*u)*j*Q(1,2)),
      w*n-(w*w-2*u*u)*Q(1,2)-(w*w-2*u*u)*Q(1,2)*(w*j-1))

here=Path(__file__).resolve().parent
base=here.parents[1]/'quartic-version5-release/repository/quartics/quartic-1272'
assert hashlib.sha256((base/'MANIFEST.json').read_bytes()).hexdigest()=='aa7f04c54e8b778a419a1be8d24e0b3a9a8540c50202d41815864a156d6985c6'
raw=json.loads((here/'raw-ir.json').read_text()); compiled=json.loads((here/'compiled/compiler-report.json').read_text())
assert raw['counts']['coordinates']==1255
assert compiled['final']['coordinates']==1223
assert all(len(t['monomial'])<=2 for row in raw['residuals'] for t in row['terms'])
names={x['name'] for x in raw['coordinates']}
for k in range(9):
    assert f'detector{k}.FInverse' not in names
    assert f'detector{k}.eWeightInverse' not in names
    assert f'detector{k}.w0Inverse' in names
    assert f'detector{k}.deltaInverse' in names
assert 'U0.z.0' not in names and 'V0.z.0' not in names
assert raw['coordinates'][0]['name']=='input'
out={'status':'passed','formalPolynomialIdentities':checks,'rawCoordinates':1255,
     'compiledCoordinates':1223,'compiledSavings':49,'inheritedDomainLemma':'Finite doubles/differences have nonzero ordinate; baseline Brox4311-4348',
     'newOrderedFieldArgument':'All scales strictly positive by the checked doubling identity; see EQUIVALENCE.md'}
(here/'identity-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

# Quaternion algebra B=(2,-3): i^2=2, j^2=-3, k=ij. Exact arithmetic with Fractions.
from fractions import Fraction as F
T={('1','1'):(1,'1'),('1','i'):(1,'i'),('1','j'):(1,'j'),('1','k'):(1,'k'),
   ('i','1'):(1,'i'),('j','1'):(1,'j'),('k','1'):(1,'k'),
   ('i','i'):(2,'1'),('j','j'):(-3,'1'),('k','k'):(6,'1'),
   ('i','j'):(1,'k'),('j','i'):(-1,'k'),('i','k'):(2,'j'),('k','i'):(-2,'j'),
   ('j','k'):(3,'i'),('k','j'):(-3,'i')}
B='1ijk'
def mul(x,y):
    r={b:F(0) for b in B}
    for a,xa in zip(B,x):
        for b,yb in zip(B,y):
            c,e=T[(a,b)]; r[e]+=c*xa*yb
    return tuple(r[b] for b in B)
def ocoords(v):
    n3=2*v[3]; n2=2*v[2]; n1=v[1]-n3/2; n0=v[0]-n2/2
    return (n0,n1,n2,n3)
basis=[(F(1),F(0),F(0),F(0)),(F(0),F(1),F(0),F(0)),(F(1,2),F(0),F(1,2),F(0)),(F(0),F(1,2),F(0),F(1,2))]
mu=(F(0),F(0),F(2),F(1)); muInv=(F(0),F(0),F(-1,3),F(-1,6))
print("mu*muInv",mul(mu,muInv),"muInv*mu",mul(muInv,mu))
for name,(x,y) in {"mu z muInv":(mu,muInv),"muInv z mu":(muInv,mu)}.items():
    cols=[ocoords(mul(mul(x,b),y)) for b in basis]
    print(name)
    for r in range(4):
        print("  n%d' ="%r, " + ".join("%s*n%d"%(cols[c][r],c) for c in range(4)))
# stabilizer elements and cone maps
import itertools
stab=[]
for A0,A2 in itertools.product(range(-4,5),repeat=2):
    if (A0-A2)%2: continue
    n=F(A0*A0+3*A2*A2,4)
    if n in (1,2,3,6): stab.append((F(A0,2),F(A2,2),n))
print("stab",stab)
cones={'A':[(1,0),(0,1)],}
def act(a0,a2,X,U):
    al=a0*a0-3*a2*a2; be=a0*a2
    return (al*X+6*be*U, -2*be*X+al*U)
import math
for th in range(0,360,15):
    X=math.cos(math.radians(th)); U=math.sin(math.radians(th))
    ok=[(float(a0),float(a2)) for a0,a2,n in stab if (lambda XU: XU[1]>=abs(XU[0])-1e-12)(act(float(a0),float(a2),X,U))]
    print(th, ok)

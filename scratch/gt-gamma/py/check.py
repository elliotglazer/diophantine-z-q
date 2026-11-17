# Numerical checks for gt-gamma (Gamma* fundamental triangle T, Dirichlet property, area).
import itertools, math, cmath
s=math.sqrt(2); k=9+6*s; p=1j*math.sqrt(3)
def iota(a0,a1,a2,a3):
    return (a0+a1*s, -3*a2-3*s*a3, a2-s*a3, a0-a1*s)
def act(M,z):
    a,b,c,d=M; return (a*z+b)/(c*z+d)
def nrd(a0,a1,a2,a3): return a0*a0-2*a1*a1+3*a2*a2-6*a3*a3
def cdist(z,w): return 1+abs(z-w)**2/(2*z.imag*w.imag)
# 1. cosh d(p, M p) = Q/n
import random
for _ in range(5):
    y=[random.randint(-6,6)/2 for _ in range(4)]
    n=nrd(*y)
    if n<=0: continue
    M=iota(*y); Q=y[0]**2+2*y[1]**2+3*y[2]**2+6*y[3]**2
    print("cosh check", cdist(p,act(M,p)), Q/n)
# 2. Phi formula
for _ in range(5):
    y=[random.randint(-6,6)/2 for _ in range(4)]; n=nrd(*y)
    if n<=0: continue
    a0,a1,a2,a3=y; w=complex(random.uniform(-2,2),random.uniform(0.5,4))
    M=iota(*y)
    lhs=n*(cdist(act(M,w),p)-cdist(w,p))*2*math.sqrt(3)*w.imag  # = |..|^2 - n|w-p|^2
    P=4*a1*a1+12*a3*a3; R=a0*a1-3*a2*a3; S=a0*a3+a1*a2
    U=abs(w)**2-3; X=6*w.real
    print("Phi check", lhs, P*(U+6)+2*s*(R*U-S*X))
# 3. enumeration: for y in O (A_i=2a_i, A0=A2, A1=A3 mod 2), nrd in {1,2,3,6}, P<4n: check 2(R-+S)+P>=0
bad=0;cnt=0
for n in (1,2,3,6):
  for A0,A1,A2,A3 in itertools.product(range(-12,13),repeat=4):
    if (A0-A2)%2 or (A1-A3)%2: continue
    if A0*A0-2*A1*A1+3*A2*A2-6*A3*A3!=4*n: continue
    if A1*A1+3*A3*A3>=4*n: continue
    cnt+=1
    for sg in (1,-1):
        val=(A0*A1-3*A2*A3)-sg*(A0*A3+A1*A2)+2*(A1*A1+3*A3*A3)
        if val<0: bad+=1; print("BAD",n,A0,A1,A2,A3,sg,val)
print("small cases",cnt,"bad",bad)
# 3b. all cases up to box: check vertex condition holds generally
bad=0
for n in (1,2,3,6):
  for A0,A1,A2,A3 in itertools.product(range(-20,21),repeat=4):
    if (A0-A2)%2 or (A1-A3)%2: continue
    if A0*A0-2*A1*A1+3*A2*A2-6*A3*A3!=4*n: continue
    for sg in (1,-1):
        val=(A0*A1-3*A2*A3)-sg*(A0*A3+A1*A2)+2*(A1*A1+3*A3*A3)
        if val<0: bad+=1
print("all box bad",bad)
# 4. mu normalizes O? check conj of basis
from fractions import Fraction as F
def qmul(x,y):
    a1,b1,c1,d1=x;a2,b2,c2,d2=y  # i^2=2, j^2=-3, k=ij, k^2=6
    return (a1*a2+2*b1*b2-3*c1*c2+6*d1*d2,
            a1*b2+b1*a2+3*(-c1*d2+d1*c2)*1,  # placeholder
            0,0)

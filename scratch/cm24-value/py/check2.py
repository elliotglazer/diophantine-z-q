# Numerical checks of the three exact steps:
# (1) inversion: theta_{(a,b)}(W)^2 = det(-i Om) theta_{(b,a)}(Om)^2, W = -Om^{-1}
# (2) duplication + translation: theta_{(a,b)}(W)^2 in terms of x = a0^2 b1^2, y = -a2^2 b0^2, z = i a1^2 b2^2
#     (a_j = theta_{0j}-type genus-1 constants at i sqrt6, b_j at i sqrt6/2)
from split import *
D = (-I)**2*(Om[0][0]*Om[1][1]-Om[0][1]**2)
for m in even:
    (a, b) = m
    print(m, nstr(th2[m]**2 - D*th1[(b, a)]**2, 5))
d1, d2 = I*s6, I*s6/2
a0, a1, a2 = t1(0,0,d1), t1(0,1,d1), t1(1,0,d1)
b0, b1, b2 = t1(0,0,d2), t1(0,1,d2), t1(1,0,d2)
x, y, z = a0**2*b1**2, -a2**2*b0**2, I*a1**2*b2**2
T00, T10, T01 = a0*b1, I*a2*b0, exp(pi*I/4)*a1*b2
pred = {((0,0),(0,0)): x+y+z, ((0,0),(1,0)): x-y+z, ((0,0),(0,1)): x+y-z, ((0,0),(1,1)): x-y-z,
        ((1,0),(0,0)): 2*T00*T10, ((1,0),(0,1)): 2*T00*T10, ((0,1),(0,0)): 2*T00*T01, ((0,1),(1,0)): 2*T00*T01,
        ((1,1),(0,0)): 2*T01*T10, ((1,1),(1,1)): -2*T01*T10}
for m in even: print("dup", m, nstr(th2[m]**2 - pred[m], 5))

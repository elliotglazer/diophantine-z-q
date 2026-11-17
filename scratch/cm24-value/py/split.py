# Numerics: theta constants at Om24 and at W = -Om24^{-1}; genus-1 decomposition.
from mpmath import mp, mpf, mpc, exp, pi, sqrt, matrix, inverse, nstr
import itertools
mp.dps = 50
I = mpc(0,1)
s6 = sqrt(6)
Om = [[(-4+3*I*s6)/14, (-1-I*s6)/7],[(-1-I*s6)/7, (-4+3*I*s6)/7]]
def theta2(m, O, N=30):
    a, b = m
    tot = mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            v = (n1 + mpf(a[0])/2, n2 + mpf(a[1])/2)
            q = O[0][0]*v[0]**2 + 2*O[0][1]*v[0]*v[1] + O[1][1]*v[1]**2
            tot += exp(pi*I*q + pi*I*(v[0]*b[0] + v[1]*b[1]))
    return tot
chars = [((a0,a1),(b0,b1)) for a0 in (0,1) for a1 in (0,1) for b0 in (0,1) for b1 in (0,1)]
even = [m for m in chars if (m[0][0]*m[1][0] + m[0][1]*m[1][1]) % 2 == 0]
def F(O):
    th = {m: theta2(m, O) for m in even}
    S8 = sum(th[m]**8 for m in even)
    P2 = 1
    for m in even: P2 *= th[m]**2
    return 3779136*P2**2/S8**5, th
f1, th1 = F(Om)
M = matrix(Om); Wm = -inverse(M)
W = [[Wm[0,0], Wm[0,1]],[Wm[1,0], Wm[1,1]]]
print("W =", [[nstr(x, 15) for x in r] for r in W])
f2, th2 = F(W)
print("F(Om) =", nstr(f1, 40)); print("F(W)  =", nstr(f2, 40))
for m in even: print(m, nstr(th1[m], 12), nstr(th2[m], 12))
# genus-1 thetas
def t1(a, b, tau, N=60):
    return sum(exp(pi*I*tau*(n + mpf(a)/2)**2 + pi*I*(n + mpf(a)/2)*b) for n in range(-N, N+1))
for tau, name in ((I*s6, "i sqrt6"), (I*s6/2, "i sqrt6/2")):
    t00, t01, t10 = t1(0,0,tau), t1(0,1,tau), t1(1,0,tau)
    k = (t10/t00)**2; kp = (t01/t00)**2
    print(name, "k =", nstr(k, 30), "k' =", nstr(kp, 30), "k^2+k'^2=", nstr(k**2+kp**2, 20))
k6 = (2-sqrt(3))*(sqrt(3)-sqrt(2)); print("(2-sqrt3)(sqrt3-sqrt2) =", nstr(k6, 30), " (1-k6)/(1+k6) =", nstr((1-k6)/(1+k6), 30))

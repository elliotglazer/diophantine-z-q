# Check the Lean-side conventions: Th2, th1, partial inversion PI0, duplication, translation phases.
from mpmath import mp, mpf, mpc, exp, pi, sqrt, nstr
mp.dps = 30
I = mpc(0, 1); s6 = sqrt(6)
def Th2(al, be, ga, c0, c1, d0, d1, N=25):
    t = mpc(0)
    for n0 in range(-N, N+1):
        for n1 in range(-N, N+1):
            v0, v1 = n0 + c0, n1 + c1
            t += exp(pi*I*(al*v0**2 + 2*be*v0*v1 + ga*v1**2) + 2*pi*I*(v0*d0 + v1*d1))
    return t
def th1(c, d, tau, N=40):
    return sum(exp(pi*I*tau*(n + c)**2 + 2*pi*I*(n + c)*d) for n in range(-N, N+1))
al, be, ga = (-4+3*I*s6)/14, (-1-I*s6)/7, (-4+3*I*s6)/7
c0, c1, d0, d1 = mpf(1)/2, 0, mpf(1)/2, mpf(1)/2
lhs = Th2(al, be, ga, c0, c1, d0, d1)
rhs = 1/sqrt(-I*al)*exp(2*pi*I*c0*d0)*Th2(-1/al, be/al, ga - be**2/al, -d0, c1, c0, d1)
print("PI0:", nstr(lhs - rhs, 5))
print("J1 Om:", nstr(-1/al, 10), nstr(be/al, 10), nstr(ga - be**2/al, 10))
# translation phases at 2W = diag(i s6, i s6/2) + [[2,1],[1,1]]
A, Bb, G = 2 + I*s6, 1, 1 + I*s6/2
h = mpf(1)/2
for (c0, c1, e0, e1, k) in ((0, 0, 0, h, 1), (h, 0, 0, 0, I), (0, h, h, 0, exp(pi*I/4)), (h, h, h, h, exp(pi*I/4))):
    l = Th2(A, Bb, G, c0, c1, 0, 0); r = k*th1(c0, e0, I*s6)*th1(c1, e1, I*s6/2)
    print("transl", c0, c1, nstr(l - r, 5), nstr(l, 8))
# duplication 2D at W
Wa, Wb, Wg = 1 + I*s6/2, h, h + I*s6/4
for (a0, a1, b0, b1) in ((0,0,0,0), (1,0,0,1), (1,1,1,1)):
    l = Th2(Wa, Wb, Wg, a0*h, a1*h, b0*h, b1*h)**2
    r = sum(Th2(2*Wa, 2*Wb, 2*Wg, (s0+a0)*h, (s1+a1)*h, b0, b1)*Th2(2*Wa, 2*Wb, 2*Wg, s0*h, s1*h, 0, 0) for s0 in (0,1) for s1 in (0,1))
    print("dup", (a0,a1,b0,b1), nstr(l - r, 5))

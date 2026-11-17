# (a) numerical check of the cubic modular equation th3(t)th3(3t) = th2(t)th2(3t) + th4(t)th4(3t);
# (d) positive real solutions of the genus-1 system pinning k6.
from mpmath import mp, mpf, mpc, exp, pi, sqrt, nstr
import sympy as sp
mp.dps = 30
I = mpc(0, 1)
def t1(a, b, tau, N=60):
    return sum(exp(pi*I*tau*(n + mpf(a)/2)**2 + pi*I*(n + mpf(a)/2)*b) for n in range(-N, N+1))
for tau in (I*sqrt(6)/3, mpc(0.3, 0.7), mpc(-0.2, 1.3)):
    th3 = lambda x: t1(0, 0, x); th4 = lambda x: t1(0, 1, x); th2 = lambda x: t1(1, 0, x)
    print("cubic", nstr(th3(tau)*th3(3*tau) - th2(tau)*th2(3*tau) - th4(tau)*th4(3*tau), 5))
# at tau' = i sqrt6/3: S-transform to tau3 = i sqrt6/2
tp, t3 = I*sqrt(6)/3, I*sqrt(6)/2
print("S:", nstr(t1(0,0,tp)/t1(0,0,t3), 12), nstr(t1(1,0,tp)/t1(0,1,t3), 12), nstr(t1(0,1,tp)/t1(1,0,t3), 12), nstr(sqrt(-I*t3), 12))
A0, A1, A2 = t1(0,0,I*sqrt(6)), t1(0,1,I*sqrt(6)), t1(1,0,I*sqrt(6))
B0, B1, B2 = t1(0,0,t3), t1(0,1,t3), t1(1,0,t3)
print("A0B0 - A2B1 - A1B2 =", nstr(A0*B0 - A2*B1 - A1*B2, 5))
# elimination with A0 = 1: t = A2, s = A1, b0, b1, b2
t, s, b0, b1, b2 = sp.symbols('t s b0 b1 b2')
eqs = [b0**2 - 1 - t**2, b1**2 - 1 + t**2, b2**2 - 2*t, s**4 - 1 + t**4, b0 - t*b1 - s*b2]
G = sp.groebner(eqs, b0, b1, b2, s, t, order='lex')
pt = G.exprs[-1]
print("eliminant in t:", sp.factor(pt))
for fac, mult in sp.factor_list(pt)[1]:
    rts = sp.Poly(fac, t).nroots(n=20)
    print(" factor", fac, " real roots in (0,1):", [r for r in rts if r.is_real and 0 < r < 1])
print("sqrt(k6) =", sp.N(sp.sqrt((2-sp.sqrt(3))*(sp.sqrt(3)-sp.sqrt(2))), 20))

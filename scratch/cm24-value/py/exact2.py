# Exact check in Q(sqrt2, sqrt3):
# F = 3779136*4*Y^2 Z^2 ((Y+Z-1)^2-4YZ)^2 / (Y^2+14YZ+14Y+Z^2+14Z+1)^5 = -16/27
# with Y = lambda(i sqrt6)/lambda'(i sqrt6/2), Z = -lambda'(i sqrt6) lambda(i sqrt6/2)/lambda'(i sqrt6/2).
import sympy as sp
a, b = sp.symbols('a b')  # a = sqrt2, b = sqrt3
G = sp.groebner([a**2 - 2, b**2 - 3], a, b, order='lex')
def red(e): return G.reduce(sp.expand(e))[1]
k6 = (2 - b)*(b - a)
l1 = red(k6**2); l1p = red(1 - l1)
# lambda'(i sqrt6/2) = ((1-k6)/(1+k6))^2, lambda(i sqrt6/2) = 4k6/(1+k6)^2
dd = red((1 - k6)**2)
Yn = red(l1*(1 + k6)**2); Zn = red(-l1p*4*k6)   # Y = Yn/dd, Z = Zn/dd
num = red(3779136*4*Yn**2*Zn**2*red((Yn + Zn - dd)**2 - 4*Yn*Zn)**2*dd**2)
den = red((Yn**2 + 14*Yn*Zn + 14*Yn*dd + Zn**2 + 14*Zn*dd + dd**2)**5)
print("num + 16/27 den =", red(num + sp.Rational(16, 27)*den))
print("den =", den, "~", sp.N(den.subs({a: sp.sqrt(2), b: sp.sqrt(3)})))
print("Y = (", Yn, ") / (", dd, ")")
print("Z = (", Zn, ") / (", dd, ")")
print("Y ~", sp.N((Yn/dd).subs({a: sp.sqrt(2), b: sp.sqrt(3)})), " Z ~", sp.N((Zn/dd).subs({a: sp.sqrt(2), b: sp.sqrt(3)})))
print("lambda1 =", l1, "  lambda2 =", sp.factor(red(4*k6)), "/ (1+k6)^2")

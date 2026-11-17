# Reduce the final identity to one variable k = k_6 with its minimal polynomial.
import sympy as sp
k, x, y, z, Z2 = sp.symbols('k x y z Z2')
lin = (x+y+z)*(x+y-z)*(x-y+z)*(x-y-z)
S = (x+y+z)**4 + (x+y-z)**4 + (x-y+z)**4 + (x-y-z)**4 + 32*(x**2*y**2 + x**2*z**2 + y**2*z**2)
P = -64*x**2*y**2*z**2*lin
def evz(e):  # polynomial even in z -> in Z2
    e = sp.Poly(sp.expand(e), z); out = 0
    for (i,), c in e.terms():
        assert i % 2 == 0; out += c*Z2**(i//2)
    return sp.expand(out)
S2 = evz(S); P2 = evz(P**2); lin2 = evz(lin)
print("S(x,y,Z2) =", sp.factor(S2))
print("lin(x,y,Z2) =", sp.factor(lin2))
sub = {x: 1-k, y: -k*(1+k), Z2: -4*k*(1-k**2)}
s = sp.expand(S2.subs(sub)); p = sp.expand(P2.subs(sub)); l = sp.expand(lin2.subs(sub))
print("s(k) =", sp.factor(s)); print("lin(k) =", sp.factor(l))
r2, r3 = sp.sqrt(2), sp.sqrt(3)
k6 = (2 - r3)*(r3 - r2)
m = sp.minimal_polynomial(k6, k)
print("minpoly k6:", m)
E = sp.expand(3779136*p + sp.Rational(16, 27)*s**5)
q, r = sp.div(sp.Poly(E, k), sp.Poly(m, k))
print("remainder:", r)
print("deg q:", q.degree())
sr = sp.div(sp.Poly(s, k), sp.Poly(m, k))[1]
print("s mod m:", sr, "  value ~", sp.N(sr.as_expr().subs(k, k6)), sp.N(s.subs(k, k6)))
open('kpoly_out.txt', 'w').write(f"m = {m}\ns = {s}\nq = {q.as_expr()}\nsr = {sr.as_expr()}\n")

# Exact: F(Om24) from the genus-1 lambda values (sympy).
import sympy as sp
x, U, V = sp.symbols('x U V')  # U = (y/x)^2, V = (z/x)^2
y, z = sp.symbols('y z')
P = (x+y+z)*(x-y+z)*(x+y-z)*(x-y-z)*(4*x*y)*(4*x*z)*(-4*y*z)
S = (x+y+z)**4+(x-y+z)**4+(x+y-z)**4+(x-y-z)**4 + 32*(x**2*y**2 + x**2*z**2 + y**2*z**2)
F = sp.expand(3779136*P**2), sp.expand(S**5)
Fy = sp.cancel((F[0]/F[1]).subs({x: 1}))
print("F(1,y,z) even in y,z:", sp.simplify(Fy - Fy.subs(y, -y)) == 0, sp.simplify(Fy - Fy.subs(z, -z)) == 0)
FUV = sp.factor(sp.expand(S.subs(x, 1)))
print("S(1,y,z) =", FUV)
print("P(1,y,z)^2 =", sp.factor(P.subs(x, 1)**2))
r2, r3, r6 = sp.sqrt(2), sp.sqrt(3), sp.sqrt(6)
k6 = (2 - r3)*(r3 - r2)
l1 = sp.expand(k6**2); l1p = 1 - l1
k2p = (1 - k6)/(1 + k6)
l2p = k2p**2; l2 = 1 - l2p
# u^2 = (y/x)^2 = lambda1 / lambda2' ; w^2 = (z/x)^2 = -(1-lambda1) * lambda2 / lambda2'
u2 = l1/l2p; w2 = -l1p*l2/l2p
yy, zz = sp.symbols('yy zz')  # yy = y^2, zz = z^2
Snum = sp.expand(S.subs(x, 1)); Pnum = sp.expand(P.subs(x, 1)**2)
def sq(e):
    e = sp.Poly(sp.expand(e), y, z)
    out = 0
    for (i, j), c in e.terms():
        assert i % 2 == 0 and j % 2 == 0
        out += c*yy**(i//2)*zz**(j//2)
    return out
Sv = sq(Snum).subs({yy: u2, zz: w2}); Pv = sq(Pnum).subs({yy: u2, zz: w2})
val = sp.nsimplify(sp.N(3779136*Pv/Sv**5, 60), tolerance=1e-40, rational=True)
print("numeric value ->", val, sp.N(3779136*Pv/Sv**5, 30))
ex = sp.radsimp(sp.simplify(3779136*Pv - sp.Rational(-16, 27)*Sv**5))
print("exact residual simplifies to:", sp.simplify(sp.expand(ex)))

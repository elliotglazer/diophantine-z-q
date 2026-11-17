import sympy as sp
k = sp.symbols('k')
E4 = sp.expand(16*k*(1-k**2)*(1+2*k-k**2)**2 - ((1+k**2)**2 + 4*k*(1-k**2))**2)
print("E4 =", sp.factor(E4))
for fac, mu in sp.factor_list(E4)[1]:
    print(fac, [r for r in sp.Poly(fac, k).nroots(n=15)])
m = k**4 + 12*k**3 + 2*k**2 - 12*k + 1
x, y, Z2 = 1 - k, -k*(1 + k), -4*k*(1 - k**2)
S = sp.expand(4*(Z2**2 + 14*Z2*x**2 + 14*Z2*y**2 + x**4 + 14*x**2*y**2 + y**4))
P = sp.expand(4096*x**4*y**4*Z2**2*((x**2 - 2*x*y + y**2 - Z2)*(x**2 + 2*x*y + y**2 - Z2))**2)
for fac, mu in sp.factor_list(E4)[1]:
    print("F identity mod", fac, ":", sp.rem(sp.expand(3779136*P + sp.Rational(16,27)*S**5), fac, k))

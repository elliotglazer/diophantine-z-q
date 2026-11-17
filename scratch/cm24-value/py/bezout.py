import sympy as sp
k = sp.symbols('k')
m = k**4 + 12*k**3 + 2*k**2 - 12*k + 1
x, y, Z2 = 1 - k, -k*(1 + k), -4*k*(1 - k**2)
s = sp.expand(4*(Z2**2 + 14*Z2*x**2 + 14*Z2*y**2 + x**4 + 14*x**2*y**2 + y**4))
u, v, g = sp.gcdex(s, m, k)
print("g =", g)
print("u =", u); print("v =", v)
assert sp.expand(u*s + v*m - 1) == 0
open('bezout_out.txt','w').write(f"u = {u}\nv = {v}\n")

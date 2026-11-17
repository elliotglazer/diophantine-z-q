import sympy as sp
k, a, b = sp.symbols('k a b')
m = k**4 + 12*k**3 + 2*k**2 - 12*k + 1
f = (k - (2-b)*(b-a))*(k + (2+b)*(b-a))*(k - (2-b)*(b+a))*(k + (2+b)*(b+a))
qs, r = sp.reduced(sp.expand(f - m), [a**2 - 2, b**2 - 3], a, b, order='lex')
print("rem", r); print("ca =", qs[0]); print("cb =", qs[1])
open('factor_out.txt','w').write(f"ca = {qs[0]}\ncb = {qs[1]}\n")

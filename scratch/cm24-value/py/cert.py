# Certificates for Lean: (1) m(k6) = 0 from a^2=2, b^2=3; (2) quotient q; (3) s mod m value in a,b.
import sympy as sp
k, a, b = sp.symbols('k a b')
m = k**4 + 12*k**3 + 2*k**2 - 12*k + 1
k6 = (2 - b)*(b - a)
e = sp.expand(m.subs(k, k6))
G = sp.groebner([a**2 - 2, b**2 - 3], a, b, order='lex')
qs, r = sp.reduced(e, [a**2 - 2, b**2 - 3], a, b, order='lex')
print("m(k6) remainder:", r)
print("cert m: coeff(a^2-2) =", sp.factor(qs[0]), "\n coeff(b^2-3) =", sp.factor(qs[1]))
txt = open('kpoly_out.txt').read()
s = sp.sympify(txt.split('\n')[1].split('=')[1]); q = sp.sympify(txt.split('\n')[2].split('=')[1]); sr = sp.sympify(txt.split('\n')[3].split('=')[1])
srab = sp.expand(sr.subs(k, k6)); qs2, r2 = sp.reduced(srab, [a**2 - 2, b**2 - 3], a, b, order='lex')
print("sr(k6) =", r2, "~", sp.N(r2.subs({a: sp.sqrt(2), b: sp.sqrt(3)})))
print("s - sr = m * ", sp.factor(sp.div(sp.Poly(s - sr, k), sp.Poly(m, k))[0].as_expr()))
open('cert_out.txt', 'w').write(f"cm_a = {qs[0]}\ncm_b = {qs[1]}\nq = {q}\nsq = {sp.div(sp.Poly(s - sr, k), sp.Poly(m, k))[0].as_expr()}\nsr = {sr}\nsrab = {r2}\nsr_a = {qs2[0]}\nsr_b = {qs2[1]}\n")
print("q =", q)

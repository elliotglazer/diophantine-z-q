# Exact check: with theta[a;b]^2 = sum_c (-1)^{(c+a).b} U_c U_{c+a} (duplication formula),
# sum_m theta_m^16 - (sum_m theta_m^8)^2/4 == 0 in Q[U0..U3].
import itertools
from poly import P
U = [P.var(i, 4) for i in range(4)]
cs = list(itertools.product(range(2), repeat=2))
idx = {c: i for i, c in enumerate(cs)}
def add(c, a): return ((c[0]+a[0]) % 2, (c[1]+a[1]) % 2)
chars = [(a, b) for a in cs for b in cs if (a[0]*b[0]+a[1]*b[1]) % 2 == 0]
def sq(a, b):
    r = P.const(0, 4)
    for c in cs:
        e = add(c, a); r = r + (-1)**(e[0]*b[0]+e[1]*b[1]) * U[idx[c]] * U[idx[e]]
    return r
S = {m: sq(*m) for m in chars}
if __name__ == '__main__':
    for m in chars: print(m, S[m].d)
    S4 = {m: S[m]**4 for m in chars}
    s4 = sum((S4[m] for m in chars), P.const(0, 4)); s8 = sum((S4[m]**2 for m in chars), P.const(0, 4))
    print('ThetaEightSquare identity in Q[U]:', (4*s8 - s4*s4).iszero())

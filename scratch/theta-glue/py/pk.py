# Global identities e_k(theta_m^8) = P_k(psi4, psi6, chi10, chi12) on H_2 (k = 3..9), found by exact
# linear algebra at random rational points U (all forms are polynomials in U), then checked at fresh
# points.  Also: substituting Lin-Yang's relations chi10 = psi4 psi6/(2^12 3^5),
# chi12 = (psi4^3+psi6^2)/(2^12 3^6), j = psi6^2/psi4^3, E1 = 4 psi4 gives E_k/E1^k = qmR_k(j).
import pickle, random, itertools
from fractions import Fraction as F
from poly import P
from dup_sym import S, chars
from igusa import syz, goep
from linalg import solve
random.seed(99)
eps = pickle.load(open('psi6_signs.pkl', 'rb')); key = lambda t: tuple(sorted(t))
def vals(x):
    s = {m: S[m].ev(x) for m in chars}; t4 = {m: s[m]**2 for m in chars}
    psi4 = sum(t4[m]**2 for m in chars) / 4
    psi6 = sum(t4[a]*t4[b]*t4[c]*eps[key((a, b, c))] for a, b, c in syz) / 4
    p = F(1)
    for m in chars: p *= s[m]
    chi10 = -p / 2**14
    chi12 = F(0)
    for q in goep:
        r = F(1)
        for m in chars:
            if m not in q: r *= t4[m]
        chi12 += r
    chi12 /= 2**17 * 3
    t8 = [t4[m]**2 for m in chars]
    e = [F(1)] + [F(0)] * 10
    for y in t8:
        for k in range(10, 0, -1): e[k] += e[k - 1] * y
    return (psi4, psi6, chi10, chi12), e
def wmonos(w):
    return [(a, b, c, d) for a in range(w // 4 + 1) for b in range(w // 6 + 1) for c in range(w // 10 + 1)
            for d in range(w // 12 + 1) if 4*a + 6*b + 10*c + 12*d == w]
qmR = {3: [F(283, 3888), F(1, 972)], 4: [F(1529, 186624), F(-1, 1458)], 5: [F(13, 23328), F(17, 314928)],
       6: [F(521, 22674816), F(95, 5668704), F(1, 2834352)], 7: [F(19, 34012224), F(313, 272097792), F(-1, 2834352)],
       8: [F(1, 136048896), F(107, 3673320192), F(49, 1836660096)],
       9: [F(1, 24794911296), F(9, 8 * 24794911296), F(1, 4 * 24794911296), F(1, 24794911296)]}
PK = {}
for k in range(3, 10):
    W = wmonos(4 * k); n = len(W)
    pts = [[F(random.randint(-30, 30), random.randint(1, 7)) for _ in range(4)] for _ in range(n + 12)]
    rows, rhs = [], []
    for x in pts:
        (a4, a6, a10, a12), e = vals(x)
        rows.append([a4**a * a6**b * a10**c * a12**d for a, b, c, d in W]); rhs.append(e[k])
    co = solve(rows[:n + 2], rhs[:n + 2], n)
    ok = all(sum(c * r for c, r in zip(co, row)) == b for row, b in zip(rows[n + 2:], rhs[n + 2:]))
    PK[k] = {w: c for w, c in zip(W, co) if c != 0}
    # curve substitution: psi4 = 1 (scale), psi6^2 = j: monomial a,b,c,d -> psi6^b chi10^c chi12^d
    # with chi10 = psi6/(2^12 3^5), chi12 = (1+psi6^2)/(2^12 3^6): expect a polynomial in psi6^2 = j
    # E_k/E1^k = P_k/4^k.
    j = P.var(0, 2); s6 = P.var(1, 2)  # use s6 with s6^2 = j
    tot = P.const(0, 2)
    for (a, b, c, d), cf in PK[k].items():
        tot = tot + s6**b * (s6 * F(1, 2**12 * 3**5))**c * ((s6 * s6 + 1) * F(1, 2**12 * 3**6))**d * cf
    # replace s6^2 -> j
    red = {}
    for (ej, es), cf in tot.d.items():
        assert es % 2 == 0, 'odd psi6 power on the curve'
        kk = ej + es // 2; red[kk] = red.get(kk, 0) + cf / 4**k
    poly = [red.get(i, F(0)) for i in range(max(red) + 1)]
    while poly and poly[-1] == 0: poly.pop()
    print('k=%d: %d monomials, check %s; P_k = %s' % (k, len(PK[k]), ok,
          ' + '.join('%s*psi4^%d psi6^%d chi10^%d chi12^%d' % (c, *w) for w, c in PK[k].items())))
    print('     curve: E_k/E1^k =', [str(c) for c in poly], ' matches qmR:', poly == qmR[k])
pickle.dump(PK, open('pk.pkl', 'wb'))

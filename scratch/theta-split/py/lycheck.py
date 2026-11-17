# Cross-check of R_3 (fit_hp.py) against Lin-Yang's Igusa vector on the QM curve
# ([psi4, psi6, 2^12 3^5 chi10, 2^12 3^6 chi12] = [j, j^2, j^3, j^3 (j+1)] weighted-projectively,
# as restated in scratch/h-v14/igusa_check.py).  Step 1: write e_3(theta_m^8) (weight 12) as
# a psi4^3 + b psi6^2 + c chi12 by evaluating on diagonal period matrices diag(t1, t2), where
# theta[a;b](diag) = theta[a0;b0](t1) theta[a1;b1](t2), psi4 = E4 E4, psi6 = E6 E6, chi12 = Delta Delta
# (restrictions of Igusa's forms; chi10 = 0 there and does not occur in weight 12).
# Step 2: predict E_3/E_1^3 = (a + b j + c (j+1)/(2^12 3^6))/64 along the curve (E_1 = 4 psi4).
import hp, random, itertools
from hp import C, D
from fractions import Fraction
random.seed(3)
def th1(t, N=40):
    # genus-1 thetas theta[a;b](t) = sum exp(pi i (n+a/2)^2 t + pi i (n+a/2) b)
    q = hp.cexp(C(0, hp.PI) * t / 4)  # exp(pi i t/4); exponent (2n+a)^2
    out = {}
    for a in range(2):
        s = {0: C(0), 1: C(0)}
        for n in range(-N, N + 1):
            u = 2 * n + a
            tt = q ** (u * u)
            s[0] = s[0] + tt
            s[1] = s[1] + tt * hp.IPOW[u % 4]
        out[(a, 0)] = s[0]; out[(a, 1)] = s[1]
    return out
def mf(t):
    T = th1(t); t3, t4, t2 = T[(0, 0)], T[(0, 1)], T[(1, 0)]
    E4 = (t2 ** 8 + t3 ** 8 + t4 ** 8) / 2
    E6 = (t2 ** 4 + t3 ** 4) * (t3 ** 4 + t4 ** 4) * (t4 ** 4 - t2 ** 4) / 2
    Dl = (t2 * t3 * t4) ** 8 / 256
    return T, E4, E6, Dl
def solve(A, b):
    n = len(A); M = [row[:] + [bb] for row, bb in zip(A, b)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c])); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]
rows = []; rhs = []
for _ in range(8):
    t1 = C(D(random.uniform(-.5, .5)), D(random.uniform(.8, 1.5)))
    t2 = C(D(random.uniform(-.5, .5)), D(random.uniform(.8, 1.5)))
    T1, a4, a6, ad = mf(t1); T2, b4, b6, bd = mf(t2)
    th = [T1[(a0, b0)] * T2[(a1, b1)] for (a0, a1), (b0, b1) in hp.chars]
    e = hp.esym([x ** 8 for x in th])
    assert abs(e[1] - 4 * a4 * b4) < D(10) ** -60  # psi4 = Sigma/4 on the diagonal
    rows.append([(a4 * b4) ** 3, (a6 * b6) ** 2, ad * bd]); rhs.append(e[3])
x = solve(rows[:3], rhs[:3])
res = max(abs(sum((r * c for r, c in zip(rows[i], x)), C(0)) - rhs[i]) / abs(rhs[i]) for i in range(3, 8))
fr = [Fraction(str(c.r)).limit_denominator(10 ** 20) for c in x]
print('e_3 = a psi4^3 + b psi6^2 + c chi12:', [str(f) for f in fr], 'check relres %.1e' % float(res))
a, b, c = fr
const = a / 64 + c / (64 * 2 ** 12 * 3 ** 6); lin = b / 64 + c / (64 * 2 ** 12 * 3 ** 6)
print('predicted E_3/E_1^3 =', const, '+', lin, 'j ;  fit_hp.py: 283/3888 + 1/972 j')
print('MATCH' if (const, lin) == (Fraction(283, 3888), Fraction(1, 972)) else 'MISMATCH')

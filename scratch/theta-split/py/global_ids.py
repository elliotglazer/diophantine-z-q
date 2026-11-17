# Global (all of the Siegel space) identities among e_k(theta_m^8): test whether e_k (k = 2, 6..9) is a
# linear combination of weight-4k monomials in e_1, e_3, e_4, e_5 (e_2 = 3/8 e_1^2 is tested first),
# at random Omega in H_2 (80 digits).
import hp, random, itertools
from hp import C, D
from fractions import Fraction
random.seed(11)
def rand_omega():
    # Omega = X + iY, Y positive definite
    a, b, c = [D(random.uniform(-.5, .5)) for _ in range(3)]
    y11 = D(random.uniform(.8, 1.4)); y22 = D(random.uniform(.8, 1.4)); y12 = D(random.uniform(-.3, .3))
    return [[C(a, y11), C(b, y12)], [C(b, y12), C(c, y22)]]
def esyms(Om):
    T = hp.thetas_all(Om, 22)
    th = [T[a][b] for a, b in hp.chars]
    return hp.esym([t ** 8 for t in th])
pts = [esyms(rand_omega()) for _ in range(16)]
print('k=2: max |e2 - 3/8 e1^2|/|e2| =', '%.1e' % float(max(abs(E[2] - C(D(3) / 8) * E[1] ** 2) / abs(E[2]) for E in pts)))
def solve(A, b):
    n = len(A); M = [row[:] + [bb] for row, bb in zip(A, b)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c])); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]
gens = {1: 1, 3: 3, 4: 4, 5: 5}  # e_i has weight 4i
def monomials(k):
    out = []
    for a in range(k + 1):
        for b in range(k // 3 + 1):
            for c in range(k // 4 + 1):
                for d in range(k // 5 + 1):
                    if a + 3 * b + 4 * c + 5 * d == k: out.append((a, b, c, d))
    return out
for k in range(6, 10):
    mons = monomials(k); n = len(mons)
    A = [[E[1] ** a * E[3] ** b * E[4] ** c * E[5] ** d for a, b, c, d in mons] for E in pts]
    rhs = [E[k] for E in pts]
    x = solve(A[:n], rhs[:n])
    res = max(abs(sum((u * v for u, v in zip(A[i], x)), C(0)) - rhs[i]) / abs(rhs[i]) for i in range(n, len(pts)))
    print('k=%d: %d monomials, check relres %.1e' % (k, n, float(res)), [str(Fraction(str(c.r)).limit_denominator(10**12)) for c in x] if res < 1e-30 else '')

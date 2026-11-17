# Fit E_k/E_1^k = sum_{i<=d} c_{k,i} j^i along tau -> Omega(tau), at high precision; recognize rationals.
import hp, random, sys
from fractions import Fraction
from decimal import Decimal as D
random.seed(7)
def solve(A, b):
    n = len(A); M = [row[:] + [bb] for row, bb in zip(A, b)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c])); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]
def rat(x, maxden=10**30):
    return Fraction(str(x)).limit_denominator(maxden)
pts = []
for _ in range(14):
    tau = hp.C(D(random.uniform(-1, 1)).quantize(D('0.001')), D(random.uniform(0.7, 1.6)).quantize(D('0.001')))
    th = hp.even_thetas(tau, N=22)
    E, N, j = hp.invariants(th)
    pts.append((tau, j, E))
res = {}
for k in range(1, 11):
    d = k // 3
    n = d + 1
    A = [[j ** i for i in range(n)] for _, j, E in pts]
    b = [E[k] / E[1] ** k for _, j, E in pts]
    x = solve(A[:n], b[:n])
    r = max(abs(sum((a * c for a, c in zip(A[i], x)), hp.C(0)) - b[i]) / abs(b[i]) for i in range(n, len(pts)))
    fr = [rat(c.r) for c in x]
    errs = [abs(c - hp.C(D(f.numerator) / D(f.denominator))) for c, f in zip(x, fr)]
    print(k, 'd=%d' % d, 'check relres %.2e' % float(r), [str(f) for f in fr], 'max|c-rat| %.1e' % float(max(errs)))
    res[k] = fr

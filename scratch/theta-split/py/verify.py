# Independent check of QMThetaSymmetricCore (ThetaUse.lean) at 30 fresh points tau (one after another):
# e_k(theta_m(Omega(tau))^8) - qmR_k(j) * (sum theta_m^8)^k, 2 <= k <= 9, exact rational qmR, 80 digits.
# Also a truncation check (N = 22 vs N = 30) at the point with the smallest Im tau.
import hp, random
from hp import C, D
from fractions import Fraction as F
R = {2: [F(3, 8)], 3: [F(283, 3888), F(1, 972)], 4: [F(1529, 186624), F(-1, 1458)],
     5: [F(13, 23328), F(17, 314928)], 6: [F(521, 22674816), F(95, 5668704), F(1, 2834352)],
     7: [F(19, 34012224), F(313, 272097792), F(-1, 2834352)],
     8: [F(1, 136048896), F(107, 3673320192), F(49, 1836660096)],
     9: [F(1, 24794911296), F(9, 8 * 24794911296), F(1, 4 * 24794911296), F(1, 24794911296)],
     10: [F(0), F(0), F(1, 14281868906496)]}
def fr(x): return D(x.numerator) / D(x.denominator)
random.seed(2026)
worst = 0; low = None
for i in range(30):
    tau = C(D(random.uniform(-3, 3)).quantize(D('0.0001')), D(random.uniform(0.35, 3.0)).quantize(D('0.0001')))
    th = hp.even_thetas(tau, N=26)
    E, N, j = hp.invariants(th)
    rel = []
    for k in range(2, 11):
        pred = sum((C(fr(c)) * j ** i for i, c in enumerate(R[k])), C(0)) * E[1] ** k
        rel.append(abs(E[k] - pred) / max(abs(E[k]), abs(pred)))
    m = max(rel); worst = max(worst, m)
    if low is None or tau.i < low.i: low = tau
    print('%2d tau=%s  |j|=%.3g  max rel. residual k=2..10: %.1e' % (i, tau, float(abs(j)), float(m)))
print('worst over 30 points: %.1e' % float(worst))
a = hp.even_thetas(low, N=22); b = hp.even_thetas(low, N=30)
print('truncation check at tau=%s: max|theta(N=22)-theta(N=30)| = %.1e' % (low, float(max(abs(x - y) for x, y in zip(a, b)))))

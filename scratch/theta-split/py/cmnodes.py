# CM points on the QM curve: fixed points tau of iota(mu), mu in O (N5 basis 1, i, (1+j)/2, (i+ij)/2,
# i^2 = 2, j^2 = -3; iota(i) = [[r2,0],[0,-r2]], iota(j) = [[0,-3],[1,0]]), and j_theta(Omega(tau)).
import dnum as Dn, math, cmath, itertools
from fractions import Fraction
r2 = math.sqrt(2)
def mat(a, b, c, d):
    # a*1 + b*i + c*(1+j)/2 + d*(i+ij)/2
    I = [[1, 0], [0, 1]]; Mi = [[r2, 0], [0, -r2]]; Mj = [[0, -3], [1, 0]]
    MiMj = [[sum(Mi[r][k] * Mj[k][s] for k in range(2)) for s in range(2)] for r in range(2)]
    return [[a * I[r][s] + b * Mi[r][s] + c * (I[r][s] + Mj[r][s]) / 2 + d * (Mi[r][s] + MiMj[r][s]) / 2
             for s in range(2)] for r in range(2)]
seen = {}
import sys
R = range(-int(sys.argv[1]), int(sys.argv[1]) + 1)
for a, b, c, d in itertools.product(R, R, R, R):
    M = mat(a, b, c, d)
    tr = M[0][0] + M[1][1]; det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    disc = tr * tr - 4 * det
    if disc > -1e-9 or abs(M[1][0]) < 1e-12: continue
    # reduced trace 2a + c and norm are integers
    A, B, Cc, Dd = M[0][0], M[0][1], M[1][0], M[1][1]
    s = cmath.sqrt((Dd - A) ** 2 + 4 * Cc * B)
    tau = ((A - Dd) + s) / (2 * Cc)
    if tau.imag < 0: tau = ((A - Dd) - s) / (2 * Cc)
    D = round(disc)
    # primitive-ish: record by discriminant
    if D in seen: continue
    th, E, N, j = Dn.data(tau)
    S = E[1]
    seen[D] = (tau, j, abs(S), (a, b, c, d))
for D in sorted(seen, reverse=True):
    tau, j, S, mu = seen[D]
    fr = Fraction(j.real).limit_denominator(10 ** 6)
    print('D=%5d mu=%s tau=%.6f%+.6fi  j=%.10f%+.1ei  ~%s  |S|=%.2e' % (D, mu, tau.real, tau.imag, j.real, j.imag, fr, S))

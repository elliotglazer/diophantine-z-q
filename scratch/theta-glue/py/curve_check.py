# 80-digit check of the Lin-Yang relations along the explicit curve tau -> Omega(tau) (hp.py = copy of
# theta-split's py/hp.py, which mirrors the Lean PkgI1.Omega and thetaConst):
#   psi4 psi6 = 2^12 3^5 chi10   and   psi4^3 + psi6^2 = 2^12 3^6 chi12,
# with Igusa's theta expressions psi4 = Sum theta^8/4, psi6 = Sum_syz eps (theta theta theta)^4/4,
# chi10 = -Prod theta^2/2^14, chi12 = Sum_Goepel Prod_{complement} theta^4/(2^17 3).
import pickle, random, itertools
import hp
from hp import C, D
from igusa import syz, goep
from dup_sym import chars as dchars
eps = pickle.load(open('psi6_signs.pkl', 'rb'))
key = lambda t: tuple(sorted(t))
random.seed(2024)
assert [((a0, a1), (b0, b1)) for (a0, a1), (b0, b1) in hp.chars] == dchars
def forms(th):
    T = dict(zip(dchars, th)); t4 = {m: T[m]**4 for m in dchars}
    psi4 = sum((t4[m]**2 for m in dchars), C(0)) / 4
    psi6 = sum((t4[a]*t4[b]*t4[c]*eps[key((a, b, c))] for a, b, c in syz), C(0)) / 4
    p = C(1)
    for m in dchars: p = p * T[m]**2
    chi10 = -p / 2**14
    chi12 = C(0)
    for q in goep:
        r = C(1)
        for m in dchars:
            if m not in q: r = r * t4[m]
        chi12 = chi12 + r
    chi12 = chi12 / (2**17 * 3)
    return psi4, psi6, chi10, chi12
worst1 = worst2 = D(0)
for i in range(12):
    tau = C(D(random.uniform(-2, 2)), D(random.uniform(0.5, 2.5)))
    th = hp.even_thetas(tau, N=22)
    psi4, psi6, chi10, chi12 = forms(th)
    r1 = abs(psi4 * psi6 - 2**12 * 3**5 * chi10) / abs(psi4 * psi6)
    r2 = abs(psi4**3 + psi6**2 - 2**12 * 3**6 * chi12) / abs(psi4**3)
    worst1 = max(worst1, r1); worst2 = max(worst2, r2)
    E, Nn, j = hp.invariants(th)
    jj = psi6**2 / psi4**3
    print('tau=%s  rel.res %.1e %.1e   |j_theta - psi6^2/psi4^3| = %.1e' % (tau, float(r1), float(r2), float(abs(j - jj))))
print('worst', float(worst1), float(worst2))

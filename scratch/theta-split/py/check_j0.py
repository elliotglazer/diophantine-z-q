# Constant terms R_k(0): e_k/e_1^k at the product point diag(i, i) (E_i x E_i, product polarization),
# compared with qmR k at j = 0 (verify_table.R). Independent of the fit along Omega(tau): it tests that the
# j = 0 point of the curve (tau = sqrt2 + i) is Sp4(Z)-equivalent to diag(i, i).
import hp, verify_table as T
from hp import C, D
from fractions import Fraction as F
Om = [[C(0, 1), C(0)], [C(0), C(0, 1)]]
Tt = hp.thetas_all(Om, 22)
th = [Tt[a][b] for a, b in hp.chars]
E = hp.esym([t ** 8 for t in th])
worst = 0
for k in range(2, 11):
    pred = T.R[k][0]
    val = E[k] / E[1] ** k
    err = abs(val - C(D(pred.numerator) / D(pred.denominator)))
    worst = max(worst, float(err / max(abs(val), D(10) ** -70)))
    print('k=%d  e_k/e_1^k(diag(i,i)) = %s   R_k(0) = %s   diff %.1e' % (k, val, pred, float(err)))
print('worst relative diff %.1e' % worst)

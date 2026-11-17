# QMCMNodesNumeric at the four Lean nodes cmTau i = (y sqrt2 + i sqrt(3z^2-2y^2))/z (ThetaUse.lean):
# |sum theta^8| and j_theta(Omega(tau)) at 80 digits; distance of j to Elkies' rational CM value.
import hp
from hp import C, D
from fractions import Fraction as F
nodes = [(-4, F(1), F(1), F(0)), (-19, F(1), F(3, 2), F(81, 64)), (-40, F(1), F(2), F(1296, 125)),
         (-43, F(2), F(5, 2), F(194481, 1000000))]
def fr(x): return D(x.numerator) / D(x.denominator)
for Dd, y, z, jv in nodes:
    s2 = 3 * z * z - 2 * y * y
    tau = C(fr(y) * hp.sqrt2() / fr(z), fr(s2).sqrt() / fr(z))
    th = hp.even_thetas(tau, N=26)
    E, N, j = hp.invariants(th)
    print('D=%d tau=%s |S|=%.6g  j=%s  |j - %s| = %.1e' % (Dd, tau, float(abs(E[1])), j, jv, float(abs(j - C(fr(jv))))))

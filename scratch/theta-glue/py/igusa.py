# Exact reconstruction of Igusa's genus-2 forms in second-order theta constants U = (U00,U01,U10,U11),
# theta_m^2 = S_m(U) (duplication formula, Dup.lean).  Pure python (poly.py).
# * modularity criterion (Runge-style): a polynomial f in U of degree 2k is a Siegel modular form of
#   even weight k for Sp4(Z) iff it is invariant under T1: U2,U3 -> iU2,iU3; T2: U1,U3 -> iU1,iU3;
#   T12: U3 -> -U3; permutations of U1,U2,U3 (GL2(F2)); H/2: U_c -> (1/2) sum_d (-1)^{c.d} U_d
#   (jtrans.py checks U(-W^-1) = s (H/2) U(W), s^2 = det(-iW)).
# * diagonal restriction U -> (u0 v0, u0 v1, u1 v0, u1 v1), genus-1 theta3^2 = u0^2+u1^2,
#   theta4^2 = u0^2-u1^2, theta2^2 = 2u0u1.
import itertools, random
from fractions import Fraction as F
from poly import P
from dup_sym import S, chars, U
cs = list(itertools.product(range(2), repeat=2))
def addc(m, n): return tuple(tuple((x + y) % 2 for x, y in zip(p, q)) for p, q in zip(m, n))
def even(m): return (m[0][0]*m[1][0] + m[0][1]*m[1][1]) % 2 == 0
zero = ((0, 0), (0, 0))
T4 = {m: S[m]**2 for m in chars}           # theta_m^4
# syzygous triples: distinct even m1,m2,m3 with m1+m2+m3 even
syz = [t for t in itertools.combinations(chars, 3) if even(addc(addc(t[0], t[1]), t[2]))]
azy = [t for t in itertools.combinations(chars, 3) if not even(addc(addc(t[0], t[1]), t[2]))]
# Goepel quadruples: 4 distinct even chars, sum zero, all four triples syzygous
goep = [q for q in itertools.combinations(chars, 4)
        if addc(addc(q[0], q[1]), addc(q[2], q[3])) == zero
        and all(even(addc(addc(*t[:2]), t[2])) for t in itertools.combinations(q, 3))]
if __name__ == '__main__':
    print('#syzygous', len(syz), '#azygetic', len(azy), '#Goepel quadruples', len(goep))

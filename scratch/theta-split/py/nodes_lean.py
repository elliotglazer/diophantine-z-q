# Integer matrices n with oBasis k * mu = sum_l n[k][l] oBasis l in B = (2, 0, -3 | Q) (i^2 = 2, j^2 = -3,
# ij = k = -ji), for the four CM nodes mu = x + y i + z j (u = 0), and the CM data tau, w.
from fractions import Fraction as F
def qmul(p, q):
    a1, b1, c1, d1 = p; a2, b2, c2, d2 = q
    # basis 1, i, j, k=ij; i^2=2, j^2=-3, k^2=6, ij=k, ji=-k, ik = i(ij) = 2j, ki = (ij)i = -i(ij)... compute via rules
    # general QuaternionAlgebra R a b c with a=2,b=0,c=-3: (Mathlib) i*i = a, j*j = c, i*j = k, j*i = -k, k*k = -a*c,
    # i*k = a*j, k*i = -a*j, j*k = -c*i, k*j = c*i
    a, c = F(2), F(-3)
    re = a1*a2 + a*b1*b2 + c*c1*c2 - a*c*d1*d2
    im_i = a1*b2 + b1*a2 - c*c1*d2 + c*d1*c2
    im_j = a1*c2 + c1*a2 + a*b1*d2 - a*d1*b2
    im_k = a1*d2 + d1*a2 + b1*c2 - c1*b2
    return (re, im_i, im_j, im_k)
oB = [(F(1),F(0),F(0),F(0)), (F(0),F(1),F(0),F(0)), (F(1,2),F(0),F(1,2),F(0)), (F(0),F(1,2),F(0),F(1,2))]
def coords(x):
    # x = n0 b0 + n1 b1 + n2 b2 + n3 b3: re = n0 + n2/2, i = n1 + n3/2, j = n2/2, k = n3/2
    re, i, j, k = x
    n2 = 2*j; n3 = 2*k; n0 = re - n2/2; n1 = i - n3/2
    return [n0, n1, n2, n3]
nodes = {-4: (0, 1, 1), -19: (F(1,2), 1, F(3,2)), -40: (0, 1, 2), -43: (F(1,2), 2, F(5,2))}
for D, (x, y, z) in nodes.items():
    mu = (F(x), F(y), F(z), F(0))
    assert all(c.denominator == 1 for c in coords(mu)), D
    t = 2*F(x); nrd = F(x)**2 - 2*F(y)**2 + 3*F(z)**2
    assert t*t - 4*nrd == D
    n = [coords(qmul(b, mu)) for b in oB]
    assert all(c.denominator == 1 for row in n for c in row)
    s2 = 3*F(z)**2 - 2*F(y)**2
    print('D=%d mu=<%s,%s,%s,0> tau=(%s*sqrt2 + I*sqrt(%s))/%s  w=%s + I*sqrt(%s)' % (D, x, y, z, y, s2, z, x, s2))
    print('   n =', [[int(c) for c in row] for row in n])

# Numerical check of the J-transformation of second-order theta constants U_c(W) = theta[c;0](2W):
# U_c(-W^{-1}) = s(W) * (1/2) sum_d (-1)^{c.d} U_d(W), with s(W)^2 = det(-i W).
import cmath, itertools, random
from dup_num import theta
random.seed(5)
cs = list(itertools.product(range(2), repeat=2))
def inv(W):
    d = W[0][0]*W[1][1] - W[0][1]*W[1][0]
    return [[W[1][1]/d, -W[0][1]/d], [-W[1][0]/d, W[0][0]/d]]
for t in range(3):
    x = [random.uniform(-.5, .5) for _ in range(3)]
    W = [[x[0] + 1.1j, x[1] + 0.2j], [x[1] + 0.2j, x[2] + 0.9j]]
    Wi = inv(W); JW = [[-Wi[0][0], -Wi[0][1]], [-Wi[1][0], -Wi[1][1]]]
    U = {c: theta(W, c, (0, 0), scale=2.0) for c in cs}
    UJ = {c: theta(JW, c, (0, 0), scale=2.0) for c in cs}
    rat = [UJ[c] / (sum((-1)**(c[0]*d[0]+c[1]*d[1]) * U[d] for d in cs) / 2) for c in cs]
    detmi = -(W[0][0]*W[1][1] - W[0][1]*W[1][0])
    print([f'{r:.6f}' for r in rat], 'r^2/det(-iW) =', rat[0]**2 / detmi)

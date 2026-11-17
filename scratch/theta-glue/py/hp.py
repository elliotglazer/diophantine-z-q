# High-precision theta constants at the Lean Omega(tau) (pure Python, decimal module).
# Lean definitions mirrored: HDec.PkgI1.Omega (= BPAnalytic.QM.Omega), PkgI1.thetaConst
# (sum over n in Z^2 of exp(pi i v^T Omega v + pi i v.b), v = n + a/2), evenChars (a.b even),
# thetaSum8, thetaProd2, jNum = 3779136 thetaProd2^2, jDen = thetaSum8^5.
from decimal import Decimal as D, getcontext
import itertools
def setprec(p): getcontext().prec = p
setprec(80)
class C:
    __slots__ = ('r', 'i')
    def __init__(s, r, i=D(0)): s.r = D(r); s.i = D(i)
    def __add__(s, o): o = cc(o); return C(s.r + o.r, s.i + o.i)
    __radd__ = __add__
    def __sub__(s, o): o = cc(o); return C(s.r - o.r, s.i - o.i)
    def __rsub__(s, o): return cc(o) - s
    def __neg__(s): return C(-s.r, -s.i)
    def __mul__(s, o): o = cc(o); return C(s.r * o.r - s.i * o.i, s.r * o.i + s.i * o.r)
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = cc(o); d = o.r * o.r + o.i * o.i
        return C((s.r * o.r + s.i * o.i) / d, (s.i * o.r - s.r * o.i) / d)
    def __rtruediv__(s, o): return cc(o) / s
    def __pow__(s, n):
        r = C(1); b = s
        if n < 0: b = C(1) / b; n = -n
        while n:
            if n & 1: r = r * b
            b = b * b; n >>= 1
        return r
    def __abs__(s): return (s.r * s.r + s.i * s.i).sqrt()
    def __repr__(s): return '(%s %+si)' % (format(s.r, '.20g'), format(s.i, '.20g'))
def cc(x): return x if isinstance(x, C) else C(x)
def pi():
    getcontext().prec += 5
    # Chudnovsky-free: Machin
    def arctan_inv(x):
        x = D(x); t = 1 / x; s = t; x2 = x * x; k = 1; sign = -1
        while True:
            t = t / x2; term = t / (2 * k + 1)
            if term < D(10) ** (-getcontext().prec): break
            s += sign * term; sign = -sign; k += 1
        return s
    p = 4 * (4 * arctan_inv(5) - arctan_inv(239))
    getcontext().prec -= 5
    return +p
PI = None
def cos_sin(x):
    # x real Decimal; reduce mod 2 pi
    global PI
    twopi = 2 * PI
    x = x - twopi * (x / twopi).to_integral_value()
    getcontext().prec += 5
    x2 = x * x; c = D(1); s = x; tc = D(1); ts = x; k = 1
    eps = D(10) ** (-getcontext().prec)
    while True:
        tc = -tc * x2 / ((2 * k - 1) * (2 * k)); ts = -ts * x2 / ((2 * k) * (2 * k + 1))
        c += tc; s += ts; k += 1
        if abs(tc) < eps and abs(ts) < eps: break
    getcontext().prec -= 5
    return +c, +s
def cexp(z):
    z = cc(z); m = z.r.exp(); c, s = cos_sin(z.i); return C(m * c, m * s)
def init():
    global PI; PI = pi()
init()
def sqrt2(): return D(2).sqrt()
def Omega(tau):
    tau = cc(tau); s2 = sqrt2()
    E = [[tau, s2 * tau], [C(1), C(-s2)]]
    F0 = [[(tau - 3) / 2, s2 * (tau - 3) / 2], [(tau + 1) / 2, -(s2 * (tau + 1)) / 2]]
    P = [[-2, -1], [-1, -1]]
    F = [[F0[r][0] * P[0][c] + F0[r][1] * P[1][c] for c in range(2)] for r in range(2)]
    d = F[0][0] * F[1][1] - F[0][1] * F[1][0]
    Fi = [[F[1][1] / d, -F[0][1] / d], [-F[1][0] / d, F[0][0] / d]]
    return [[Fi[r][0] * E[0][c] + Fi[r][1] * E[1][c] for c in range(2)] for r in range(2)]
chars = [((a0, a1), (b0, b1)) for a0, a1, b0, b1 in itertools.product(range(2), repeat=4)
         if (a0 * b0 + a1 * b1) % 2 == 0]
IPOW = [C(1), C(0, 1), C(-1), C(0, -1)]
def thetas_all(Om, N):
    """dict a -> dict b -> theta[a;b](Omega), all 16 characteristics."""
    a_, b_, c_ = Om[0][0], (Om[0][1] + Om[1][0]) / 2, Om[1][1]
    ipi = C(0, PI)
    A = cexp(ipi * a_ / 4); B = cexp(ipi * b_ / 2); Cc = cexp(ipi * c_ / 4)
    out = {}
    for a0, a1 in itertools.product(range(2), repeat=2):
        sums = {bb: C(0) for bb in itertools.product(range(2), repeat=2)}
        for n0 in range(-N, N + 1):
            u0 = 2 * n0 + a0
            base0 = A ** (u0 * u0); Bu = B ** u0
            for n1 in range(-N, N + 1):
                u1 = 2 * n1 + a1
                t = base0 * (Bu ** u1) * (Cc ** (u1 * u1))
                for bb in sums:
                    sums[bb] = sums[bb] + t * IPOW[(u0 * bb[0] + u1 * bb[1]) % 4]
        out[(a0, a1)] = sums
    return out
def even_thetas(tau, N=None):
    Om = Omega(tau)
    if N is None: N = 14
    T = thetas_all(Om, N)
    return [T[a][b] for a, b in chars]
def esym(xs):
    e = [C(1)] + [C(0)] * len(xs)
    for x in xs:
        for k in range(len(xs), 0, -1): e[k] = e[k] + e[k - 1] * x
    return e
def invariants(th):
    t8 = [t ** 8 for t in th]; E = esym(t8)
    p = C(1)
    for t in th: p = p * t
    Nn = 3779136 * p ** 4
    return E, Nn, Nn / E[1] ** 5

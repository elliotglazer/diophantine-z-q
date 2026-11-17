# Minimal exact multivariate polynomials over Q (dict: exponent tuple -> Fraction). Pure python.
from fractions import Fraction
class P:
    __slots__ = ('d', 'n')
    def __init__(s, d, n): s.d = {k: v for k, v in d.items() if v != 0}; s.n = n
    @staticmethod
    def var(i, n): e = [0]*n; e[i] = 1; return P({tuple(e): Fraction(1)}, n)
    @staticmethod
    def const(c, n): return P({(0,)*n: Fraction(c)}, n)
    def _c(s, o): return o if isinstance(o, P) else P.const(o, s.n)
    def __add__(s, o):
        o = s._c(o); d = dict(s.d)
        for k, v in o.d.items(): d[k] = d.get(k, 0) + v
        return P(d, s.n)
    __radd__ = __add__
    def __neg__(s): return P({k: -v for k, v in s.d.items()}, s.n)
    def __sub__(s, o): return s + (-s._c(o))
    def __rsub__(s, o): return s._c(o) - s
    def __mul__(s, o):
        o = s._c(o); d = {}
        for k1, v1 in s.d.items():
            for k2, v2 in o.d.items():
                k = tuple(a + b for a, b in zip(k1, k2)); d[k] = d.get(k, 0) + v1 * v2
        return P(d, s.n)
    __rmul__ = __mul__
    def __pow__(s, e):
        r = P.const(1, s.n); b = s
        while e:
            if e & 1: r = r * b
            b = b * b; e >>= 1
        return r
    def iszero(s): return not s.d
    def __eq__(s, o): return (s - o).iszero()
    def deg(s): return max((sum(k) for k in s.d), default=-1)
    def __len__(s): return len(s.d)
    def ev(s, xs):
        tot = 0
        for k, v in s.d.items():
            t = v
            for x, e in zip(xs, k): t = t * x**e
            tot = tot + t
        return tot
def _subst(s, L):
    """f(L_0, ..., L_{n-1}) for polynomials L_i (all in the same number of variables)."""
    m = L[0].n; cache = {}
    def pw(i, e):
        if (i, e) not in cache: cache[(i, e)] = L[i] ** e
        return cache[(i, e)]
    out = P.const(0, m)
    for k, v in s.d.items():
        t = P.const(v, m)
        for i, e in enumerate(k):
            if e: t = t * pw(i, e)
        out = out + t
    return out
P.subst = _subst

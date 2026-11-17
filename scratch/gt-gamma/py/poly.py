# Tiny multivariate polynomial arithmetic (Fraction coefficients) to compute linear_combination
# certificates modulo s^2 = 2, t^2 = 3 (s = sqrt 2, t = sqrt 3).
from fractions import Fraction as F
class P:
    def __init__(s, d=None): s.d = {k: v for k, v in (d or {}).items() if v != 0}
    @staticmethod
    def const(c, n): return P({(0,)*n: F(c)})
    def __add__(a, b):
        b = b if isinstance(b, P) else P.const(b, NV)
        d = dict(a.d)
        for k, v in b.d.items(): d[k] = d.get(k, 0) + v
        return P(d)
    __radd__ = __add__
    def __neg__(a): return P({k: -v for k, v in a.d.items()})
    def __sub__(a, b): return a + (-(b if isinstance(b, P) else P.const(b, NV)))
    def __rsub__(a, b): return (-a) + b
    def __mul__(a, b):
        b = b if isinstance(b, P) else P.const(b, NV)
        d = {}
        for k1, v1 in a.d.items():
            for k2, v2 in b.d.items():
                k = tuple(x + y for x, y in zip(k1, k2)); d[k] = d.get(k, 0) + v1 * v2
        return P(d)
    __rmul__ = __mul__
    def __pow__(a, n):
        r = P.const(1, NV)
        for _ in range(n): r = r * a
        return r
NAMES = []
NV = 0
def setvars(names):
    global NAMES, NV
    NAMES = names; NV = len(names)
    return [P({tuple(1 if j == i else 0 for j in range(NV)): F(1)}) for i in range(NV)]
def reduce(E, var, val):
    """E = q*(var^2 - val) + r with r of degree <= 1 in var. Returns q, r."""
    i = NAMES.index(var)
    q = P(); r = P(E.d)
    while True:
        hi = {k: v for k, v in r.d.items() if k[i] >= 2}
        if not hi: return q, r
        for k, v in hi.items():
            k2 = list(k); k2[i] -= 2; k2 = tuple(k2)
            q = q + P({k2: v})
            r = r - P({k: v}) + P({k2: v * val})
def fmt(p, names=None):
    names = names or NAMES
    if not p.d: return "0"
    terms = []
    for k, v in sorted(p.d.items()):
        mon = "*".join(f"{n}^{e}" if e > 1 else n for n, e in zip(names, k) if e > 0)
        c = f"({v})" if v.denominator != 1 or v < 0 else f"{v}"
        terms.append(c if not mon else (mon if v == 1 else f"{c}*{mon}"))
    return " + ".join(terms)

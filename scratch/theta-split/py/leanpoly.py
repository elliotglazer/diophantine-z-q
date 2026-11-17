# Parse qmR from ThetaUse.lean (sympy-free) and compare with verify.py's table R.
import re, sys
from fractions import Fraction as F
src = open(sys.argv[1]).read()
body = src[src.index('def qmR'):src.index('| _ => 0')]
X = 'X'
def ev(expr):
    # evaluate as polynomial: represent as dict deg->Fraction using a tiny class
    class P:
        def __init__(s, d): s.d = {k: v for k, v in d.items() if v != 0}
        def __add__(s, o): o = cv(o); d = dict(s.d); [d.__setitem__(k, d.get(k, 0) + v) for k, v in o.d.items()]; return P(d)
        __radd__ = __add__
        def __sub__(s, o): return s + cv(o) * P({0: F(-1)})
        def __mul__(s, o):
            o = cv(o); d = {}
            for a, x in s.d.items():
                for b, y in o.d.items(): d[a + b] = d.get(a + b, 0) + x * y
            return P(d)
        __rmul__ = __mul__
        def __pow__(s, n):
            r = P({0: F(1)})
            for _ in range(n): r = r * s
            return r
    def cv(o): return o if isinstance(o, P) else P({0: F(o)})
    e = expr.replace('^', '**')
    e = re.sub(r'C \(([0-9]+) / ([0-9]+)\)', r'C(F(\1,\2))', e)
    r = eval(e, {'C': lambda c: P({0: F(c)}), 'X': P({1: F(1)}), 'F': F})
    return cv(r).d
import verify_table as T
ok = True
for m in re.finditer(r'\| (\d+) => (.*)', body):
    k = int(m.group(1)); d = ev(m.group(2))
    if k in T.R:
        want = {i: c for i, c in enumerate(T.R[k]) if c != 0}
        print(k, d == want); ok &= d == want
print('ALL MATCH' if ok else 'MISMATCH')

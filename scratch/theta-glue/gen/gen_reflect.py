# Emits the data/check part for the reflection proof of IgusaAlg k.
import sys, pickle
from fractions import Fraction as F
from math import lcm
sys.path.insert(0, '../py')
from poly import P
from dup_sym import S, chars
from igusa import syz, goep
eps = pickle.load(open('../py/psi6_signs.pkl', 'rb')); key = lambda t: tuple(sorted(t))
PK = pickle.load(open('../py/pk.pkl', 'rb'))
def plit(p):
    items = sorted(p.d.items(), key=lambda kv: kv[0])
    return 'unpackP [' + ', '.join('(%d, %d)' % (int(c), e[3] + 256 * (e[2] + 256 * (e[1] + 256 * e[0]))) for e, c in items) + ']'
def lit(p):
    items = sorted(p.d.items(), key=lambda kv: kv[0])   # lex ascending on exponent tuples
    return '[' + ', '.join('(%d, (%d, %d, %d, %d))' % ((int(c),) + tuple(e)) for e, c in items) + ']'
def sq_defs():
    out = []
    for i, m in enumerate(chars):
        out.append('def Sp%d : Poly := %s' % (i, lit(S[m])))
    return '\n'.join(out)
idx = {m: i for i, m in enumerate(chars)}
def sgnP(terms):
    # terms: list of (sign, polyexpr); build padd/psub chain mirroring  t1 + t2 - t3 ...
    s0, e0 = terms[0]
    acc = e0 if s0 > 0 else 'pneg (%s)' % e0
    for s, e in terms[1:]:
        acc = '%s (%s) (%s)' % ('padd' if s > 0 else 'psub', acc, e)
    return acc
def poly_defs():
    S4 = sgnP([(1, 'ppow Sp%d 4' % idx[m]) for m in chars])
    S6 = sgnP([(eps[key(t)], 'ppow (pmul (pmul Sp%d Sp%d) Sp%d) 2' % (idx[t[0]], idx[t[1]], idx[t[2]])) for t in syz])
    PP = 'Sp0'
    for m in chars[1:]: PP = 'pmul (%s) Sp%d' % (PP, idx[m])
    def prod6(q):
        ms = [m for m in chars if m not in q]; e = 'Sp%d' % idx[ms[0]]
        for m in ms[1:]: e = 'pmul (%s) Sp%d' % (e, idx[m])
        return 'ppow (%s) 2' % e
    S12 = sgnP([(1, prod6(q)) for q in goep])
    return 'def S4p : Poly := %s\n\ndef S6p : Poly := %s\n\ndef Pp : Poly := %s\n\ndef S12p : Poly := %s\n' % (S4, S6, PP, S12)
def ylist():
    return 'def Ylist : List Poly := [' + ', '.join('ppow Sp%d 4' % i for i in range(10)) + ']'
def rhs_def(k):
    terms = {}
    for (a, b, c, d), cf in PK[k].items():
        terms[(a, b, c, d)] = F(cf) / (F(4)**a * F(4)**b * F(-2**14)**c * F(2**17 * 3)**d)
    DEN = 1
    for r in terms.values(): DEN = lcm(DEN, r.denominator)
    parts = []
    for (a, b, c, d), r in sorted(terms.items()):
        n = int(r * DEN)
        parts.append((n, a, b, c, d))
    e = None
    for n, a, b, c, d in parts:
        t = 'pscale (%d) (pmul (pmul (ppow S4p %d) (ppow S6p %d)) (pmul (ppow Pp %d) (ppow S12p %d)))' % (n, a, b, c, d)
        e = t if e is None else 'padd (%s) (%s)' % (e, t)
    return DEN, parts, 'def RHS%d : Poly := %s' % (k, e)
if __name__ == '__main__':
    k = int(sys.argv[1])
    DEN, parts, r = rhs_def(k)
    print(DEN, parts)

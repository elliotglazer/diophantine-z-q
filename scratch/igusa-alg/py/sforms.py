# Compute the s-forms (s_i = U_i^2) of the IgusaAlg identities, parsing psi6T / chi12T / igusaP
# from the Lean text of theta-glue (scratch/theta-glue/Alg4.lean), and check the identities exactly.
import re, sys, pickle
from fractions import Fraction as F
import sympy as sp
SRC = '../../theta-glue/Alg4.lean'
txt = open(SRC).read()
U = sp.symbols('U0:4')   # U0=u![0,0], U1=u![0,1], U2=u![1,0], U3=u![1,1]
s = sp.symbols('s0:4')
chars = [((0,0),(0,0)),((0,0),(0,1)),((0,0),(1,0)),((0,0),(1,1)),((0,1),(0,0)),((0,1),(1,0)),
         ((1,0),(0,0)),((1,0),(0,1)),((1,1),(0,0)),((1,1),(1,1))]
idx = {(0,0):0,(0,1):1,(1,0):2,(1,1):3}
def Sq(m):
    a, b = m
    tot = 0
    for c in [(0,0),(0,1),(1,0),(1,1)]:
        ca = ((c[0]+a[0])%2, (c[1]+a[1])%2)
        tot += (-1)**(ca[0]*b[0] + ca[1]*b[1]) * U[idx[c]] * U[idx[ca]]
    return sp.expand(tot)
T = {m: Sq(m) for m in chars}
def parse_block(name):
    body = txt.split('def %s' % name)[1].split('\n\n')[0]
    terms = []
    for line in body.split('\n'):
        mm = re.findall(r't \(!\[(\d), (\d)\], !\[(\d), (\d)\]\)', line)
        if not mm: continue
        sign = -1 if line.strip().startswith('-') else 1
        terms.append((sign, [((int(a),int(b)),(int(c),int(d))) for a,b,c,d in mm]))
    return terms
psi6terms = parse_block('psi6T'); chi12terms = parse_block('chi12T')
assert len(psi6terms) == 60 and len(chi12terms) == 15, (len(psi6terms), len(chi12terms))
def toS(p):
    p = sp.Poly(sp.expand(p), *U)
    out = 0
    for mon, c in p.terms():
        assert all(e % 2 == 0 for e in mon), mon
        out += c * sp.Mul(*[s[i]**(mon[i]//2) for i in range(4)])
    return sp.expand(out)
Psi4 = toS(sum(T[m]**4 for m in chars))                     # = 4 psi4T
Psi6 = toS(sum(sg*sp.Mul(*[T[m] for m in ms])**2 for sg, ms in psi6terms))   # = 4 psi6T
X10 = toS(sp.Mul(*[T[m] for m in chars]))                  # = -2^14 chi10T
X12 = toS(sum(sg*sp.Mul(*[T[m] for m in ms])**2 for sg, ms in chi12terms))  # = 2^17*3 chi12T
blocks = []
for i in range(4): blocks.append((toS(T[chars[i]]**4), sp.Integer(0)))
for i in (4, 6, 8):
    a, b = T[chars[i]]**4, T[chars[i+1]]**4
    blocks.append((toS(a + b), toS(a*b)))
# igusaP
P = {}
for k in range(3, 10):
    line = [l for l in txt.split('\n') if re.match(r'\s*\| %d, ' % k, l)][0]
    rhs = line.split('=>')[1]
    rhs = rhs.replace(': ℂ', '').replace('^', '**')
    a, b, c, d = sp.symbols('a b c d')
    P[k] = sp.expand(sp.sympify(rhs, locals={'a':a,'b':b,'c':c,'d':d}))
a, b, c, d = sp.symbols('a b c d')
def esymmP(bl, k):
    # coefficient of X^k in prod (1 + q X + r X^2)
    X = sp.Symbol('X')
    pr = sp.Integer(1)
    v = [sp.Integer(1)] + [sp.Integer(0)]*k
    for q, r in bl:
        w = [v[j] + (q*v[j-1] if j >= 1 else 0) + (r*v[j-2] if j >= 2 else 0) for j in range(k+1)]
        v = [sp.expand(x) for x in w]
    return v[k]
out = {'Psi4': Psi4, 'Psi6': Psi6, 'X10': X10, 'X12': X12, 'blocks': blocks, 'P': P}
print('terms Psi4 %d Psi6 %d X10 %d X12 %d' % tuple(len(sp.Add.make_args(x)) for x in (Psi4, Psi6, X10, X12)))
print('blocks', [(len(sp.Add.make_args(q)), len(sp.Add.make_args(r))) for q, r in blocks])
# integer forms: P_k(Psi4/4, Psi6/4, -X10/2^14, X12/(2^17*3)) = (1/D) sum n * A^i B^j C^l E^m
A, B, C, E = sp.symbols('A B C E')
INT = {}
for k in range(3, 10):
    expr = sp.expand(P[k].subs({a: A/4, b: B/4, c: -C/2**14, d: E/(2**17*3)}))
    pol = sp.Poly(expr, A, B, C, E)
    D = sp.ilcm(*[sp.fraction(cf)[1] for cf in pol.coeffs()])
    INT[k] = (int(D), [(mon, int(cf*D)) for mon, cf in pol.terms()])
    print('k', k, 'D', D, INT[k][1])
out['INT'] = INT
if '--check' in sys.argv:
    for k in range(3, 10):
        D, mons = INT[k]
        lhs = D * esymmP(blocks, k)
        rhs = sum(n * Psi4**i * Psi6**j * X10**l * X12**m for (i, j, l, m), n in mons)
        print('k', k, 'identity in s:', sp.expand(lhs - rhs) == 0, flush=True)
pickle.dump(out, open('sforms.pkl', 'wb'))

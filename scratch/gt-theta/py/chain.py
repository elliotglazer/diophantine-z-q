# Theta transformation chain for M4, M6 (gt-theta). Pure Python (cmath, fractions).
import cmath, math, itertools, random
from fractions import Fraction as F

def theta(c, d, Om, N=12):
    a, b, g = Om
    s = 0
    for n0 in range(-N, N+1):
        for n1 in range(-N, N+1):
            v0 = n0 + c[0]; v1 = n1 + c[1]
            s += cmath.exp(math.pi*1j*(a*v0*v0 + 2*b*v0*v1 + g*v1*v1) + 2*math.pi*1j*(v0*d[0]+v1*d[1]))
    return s

def trans(S, c, d):
    s00, s01, s11 = S
    ph = -(s00*(c[0]**2+c[0]) + s11*(c[1]**2+c[1]) + 2*s01*c[0]*c[1])   # units pi*i, for Th2 (not squared)
    d2 = (d[0] + s00*(c[0]+F(1,2)) + s01*c[1], d[1] + s11*(c[1]+F(1,2)) + s01*c[0])
    return ph, c, d2

def rot(kind, c, d):
    if kind == 'swapneg':   # Th2 r (-q) p c0 c1 d0 d1 = Th2 p q r (-c1) c0 (-d1) d0
        return (-c[1], c[0]), (-d[1], d[0])
    if kind == 'swap':
        return (c[1], c[0]), (d[1], d[0])

S2 = (1, -1, 2)
MATS = {'M4': ((0, 1, 0), 'swap'), 'M6': ((0, 0, 0), 'swapneg')}

def chain(name, c, d):
    S1, kind = MATS[name]
    P = F(0)
    ph, c, d = trans(S1, c, d); P += 2*ph
    c, d = rot(kind, c, d)
    P += 4*(c[0]*d[0] + c[1]*d[1])
    c, d = d, (-c[0], -c[1])
    ph, c, d = trans(S2, c, d); P += 2*ph
    return P, c, d   # Th2(MΩ)(c,d)^2 = -Δ1 * exp(πi P) * Th2(Ω)(c',d')^2

def mat_act(name, Om):
    a, b, g = Om
    a1, b1, g1 = a+1, b-1, g+2
    D = a1*g1 - b1*b1
    if name == 'M6':
        return (-a1/D, -b1/D, -g1/D), D
    else:
        return (-a1/D, b1/D + 1, -g1/D), D


def mm(X, Y): return [[sum(X[i][k]*Y[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def ma(X, Y): return [[X[i][j]+Y[i][j] for j in range(2)] for i in range(2)]
def inv(X):
    d = X[0][0]*X[1][1]-X[0][1]*X[1][0]
    return [[X[1][1]/d, -X[0][1]/d], [-X[1][0]/d, X[0][0]/d]], d

BLK = {'M4': ([[1,0],[0,1]], [[1,-2],[-2,2]], [[0,1],[1,0]], [[-1,2],[1,-1]]),
       'M6': ([[0,0],[0,0]], [[0,-1],[1,0]], [[0,1],[-1,0]], [[-1,2],[-1,1]])}

def direct_spact(name, Om):
    A, B, C, D = BLK[name]
    a, b, g = Om
    O = [[a, b], [b, g]]
    X = ma(mm(A, O), B); Y = ma(mm(C, O), D)
    Yi, det = inv(Y)
    R = mm(X, Yi)
    return (R[0][0], R[0][1], R[1][1]), det, R[1][0]

even = [((a0,a1),(b0,b1)) for a0 in (0,1) for a1 in (0,1) for b0 in (0,1) for b1 in (0,1) if (a0*b0+a1*b1)%2==0]
random.seed(1)
for name in ['M4', 'M6']:
    Om = (complex(0.3, 1.1), complex(-0.2, 0.3), complex(0.15, 0.9))
    Om2, D1 = mat_act(name, Om)
    R, det, r10 = direct_spact(name, Om)
    print(name, 'spAct match', max(abs(R[i]-Om2[i]) for i in range(3)), abs(r10-R[1]), 'spFactor/Δ1', det/D1)
    tot = F(0); sig = []
    for (a, b) in even:
        c = (F(a[0],2), F(a[1],2)); d = (F(b[0],2), F(b[1],2))
        P, c2, d2 = chain(name, c, d)
        lhs = theta(c, d, Om2)**2
        rhs = -D1 * cmath.exp(math.pi*1j*P) * theta(c2, d2, Om)**2
        tgt = (tuple(int(2*x) % 2 for x in c2), tuple(int(2*x) % 2 for x in d2))
        ok = abs(lhs-rhs) / max(abs(lhs), 1e-9)
        # reduced: also check against theta at reduced char
        rhs2 = -D1 * cmath.exp(math.pi*1j*P) * theta(tuple(F(x,2) for x in tgt[0]), tuple(F(x,2) for x in tgt[1]), Om)**2
        ok2 = abs(lhs-rhs2) / max(abs(lhs), 1e-9)
        print(' ', (a, b), '->', tgt, 'P=', P, 'P*4=', P*4, 'rel err', '%.1e %.1e' % (ok, ok2))
        tot += P; sig.append(tgt)
    print('  sum P =', tot, ' perm:', sorted(sig) == sorted(even))

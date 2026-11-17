# Siegel modular forms of even weight k for Sp4(Z) as invariant polynomials of degree 2k in U.
import itertools, random
from fractions import Fraction as F
from poly import P
from linalg import nullspace
random.seed(7)
def monos(d):
    return [e for e in itertools.product(range(d + 1), repeat=4) if sum(e) == d
            and (e[2] + e[3]) % 4 == 0 and (e[1] + e[3]) % 4 == 0 and e[3] % 2 == 0]
def orbit_basis(d):
    seen = set(); basis = []
    for e in monos(d):
        if e in seen: continue
        orb = set()
        for p in itertools.permutations([1, 2, 3]):
            f = (e[0], e[p[0]], e[p[1]], e[p[2]]); orb.add(f)
        seen |= orb; basis.append(P({o: F(1) for o in orb}, 4))
    return basis
def hadamard(x):
    u0, u1, u2, u3 = x
    h = F(1, 2)
    return [(u0 + u1 + u2 + u3) * h, (u0 - u1 + u2 - u3) * h, (u0 + u1 - u2 - u3) * h, (u0 - u1 - u2 + u3) * h]
def invariant_space(k, npts=None):
    B = orbit_basis(2 * k); n = len(B)
    pts = [[F(random.randint(-9, 9), random.randint(1, 5)) for _ in range(4)] for _ in range(n + 5)]
    rows = [[b.ev(hadamard(x)) - b.ev(x) for b in B] for x in pts]
    ns = nullspace(rows, n)
    return [sum((c * b for c, b in zip(v, B) if c != 0), P.const(0, 4)) for v in ns]
def is_modular(f):
    """exact check of the invariance conditions for a polynomial f in U (even weight)."""
    for e in f.d:
        if (e[2] + e[3]) % 4 or (e[1] + e[3]) % 4 or e[3] % 2: return False
    for p in itertools.permutations([1, 2, 3]):
        g = P({(e[0], e[p[0]], e[p[1]], e[p[2]]): c for e, c in f.d.items()}, 4)
        if not (g - f).iszero(): return False
    u = [P.var(i, 4) for i in range(4)]
    return (f.subst(hadamard(u)) - f).iszero()
if __name__ == '__main__':
    for k in (2, 3, 4, 5, 6):
        print('weight', k, 'dim', len(invariant_space(k)), 'orbit basis', len(orbit_basis(2 * k)))

# psi4, psi6, chi10, chi12 as polynomials in U; comparison with Igusa's theta expressions.
import itertools, random
from fractions import Fraction as F
from poly import P
from dup_sym import S, chars
from igusa import syz, goep, T4
from invariants import invariant_space, is_modular
from linalg import nullspace, solve
random.seed(11)
one = P.const(1, 4)
def prod(xs):
    r = one
    for x in xs: r = r * x
    return r
psi4 = sum((T4[m]**2 for m in chars), P.const(0, 4)) * F(1, 4)
chi10 = prod(S[m] for m in chars) * F(-1, 2**14)
V6 = invariant_space(6); assert len(V6) == 1
psi6 = V6[0] * (1 / V6[0].d[(12, 0, 0, 0)])
# diagonal restriction
D = [P.var(i, 4) for i in range(4)]  # u0,u1,v0,v1
diagU = [D[0]*D[2], D[0]*D[3], D[1]*D[2], D[1]*D[3]]
def g1(u0, u1):
    t3, t4, t2 = u0*u0 + u1*u1, u0*u0 - u1*u1, 2*u0*u1   # squares of genus-1 thetas
    E4 = (t2**4 + t3**4 + t4**4) * F(1, 2)
    E6 = (t2**2 + t3**2) * (t3**2 + t4**2) * (t4**2 - t2**2) * F(1, 2)
    Dl = (t2 * t3 * t4)**4 * F(1, 256)
    return E4, E6, Dl
E4u, E6u, Dlu = g1(D[0], D[1]); E4v, E6v, Dlv = g1(D[2], D[3])
def diag(f): return f.subst(diagU)
if __name__ == '__main__':
    print('psi4 modular:', is_modular(psi4), ' psi4|diag = E4 E4:', diag(psi4) == E4u * E4v)
    print('psi6 |diag = E6 E6:', diag(psi6) == E6u * E6v, ' #terms', len(psi6))
    print('chi10 modular:', is_modular(chi10), ' chi10|diag = 0:', diag(chi10).iszero())
    # chi12 in span(psi4^3, psi6^2, chi12): fix by diagonal restriction Delta x Delta
    V12 = invariant_space(12); assert len(V12) == 3
    tgt = Dlu * Dlv
    pts = [[F(random.randint(-9, 9), random.randint(1, 4)) for _ in range(4)] for _ in range(8)]
    dV = [diag(v) for v in V12]
    rows = [[dv.ev(x) for dv in dV] for x in pts]; rhs = [tgt.ev(x) for x in pts]
    co = solve(rows, rhs, 3)
    chi12 = sum((c * v for c, v in zip(co, V12)), P.const(0, 4))
    print('chi12|diag = Delta Delta:', diag(chi12) == tgt)
    # Igusa's theta expression for chi12: 2^-17 3^-1 sum over Goepel quadruples of prod_{m not in Q} theta_m^4
    h12 = sum((prod(T4[m] for m in chars if m not in q) for q in goep), P.const(0, 4))
    print('2^-17 3^-1 sum_Goepel prod_{complement} theta^4 == chi12:', h12 * F(1, 2**17 * 3) == chi12)
    # Igusa's psi6 = 2^-2 sum_syz +-(theta theta theta)^4: solve for the signs
    terms = [T4[t[0]] * T4[t[1]] * T4[t[2]] for t in syz]
    pts = [[F(random.randint(-9, 9), random.randint(1, 4)) for _ in range(4)] for _ in range(90)]
    rows = [[tm.ev(x) for tm in terms] for x in pts]; rhs = [4 * psi6.ev(x) for x in pts]
    sol = solve(rows, rhs, len(terms))
    ns = nullspace(rows, len(terms))
    print('sign solve: particular solution', sol is not None, ' nullity', len(ns))
    print('values', sorted(set(sol)))
    import pickle
    pickle.dump({'psi4': psi4.d, 'psi6': psi6.d, 'chi10': chi10.d, 'chi12': chi12.d, 'signs': sol},
                open('igusa_forms.pkl', 'wb'))

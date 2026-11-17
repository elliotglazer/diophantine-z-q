# Endomorphism lattice of the ppav with period matrix Om24 (scratch/qm-glue/ThetaValue24.lean),
# and its polarization-preserving automorphisms (R in Sp4(Z) with R.Om24 = Om24).
# Convention: lattice = columns of [Om | I]; R = [[a,b],[c,d]] acts by [Om I] R = rho [Om I].
import sympy as sp, itertools
s = sp.sqrt(-6)
Om = sp.Matrix([[(-4 + 3*s)/14, (-1 - s)/7], [(-1 - s)/7, (-4 + 3*s)/7]])
xs = sp.symbols('x0:16')
R = sp.Matrix(4, 4, xs)
a, b, c, d = R[:2, :2], R[:2, 2:], R[2:, :2], R[2:, 2:]
E = sp.expand(Om*a + c - (Om*b + d)*Om)
eqs = []
for e in E:
    e = sp.expand(e)
    re, im = e.subs(s, 0), sp.expand((e - e.subs(s, 0))/s)
    eqs += [re, im]
M = sp.Matrix([[sp.diff(e, x) for x in xs] for e in eqs])
ns = M.nullspace()
print("rank End =", len(ns))
# integral basis of the solution lattice: clear denominators and LLL via pari
import cypari2
pari = cypari2.Pari()
basis = []
for v in ns:
    den = sp.ilcm(*[sp.fraction(t)[1] for t in v])
    basis.append([int(t*den) for t in v])
# saturate: lattice of integer solutions = kernel of M over Z
Mint = [[int(t) for t in row] for row in (M*sp.ilcm(*[sp.fraction(t)[1] for t in M])).tolist()]
K = pari.matkerint(pari.matrix(len(Mint), 16, [x for row in Mint for x in row]))
K = [[int(K[i, j]) for i in range(16)] for j in range(len(K))]  # columns
print("Z-basis size", len(K))
J = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]])
found = []
rng = range(-2, 3)
for co in itertools.product(rng, repeat=len(K)):
    v = [sum(co[k]*K[k][i] for k in range(len(K))) for i in range(16)]
    Rm = sp.Matrix(4, 4, v)
    if Rm.T*J*Rm == J:
        found.append(Rm)
print("Sp4(Z) stabilizer elements found:", len(found))
for Rm in found:
    print(Rm.tolist(), "order", next(k for k in range(1, 13) if Rm**k == sp.eye(4)) if any(Rm**k == sp.eye(4) for k in range(1, 13)) else "?")

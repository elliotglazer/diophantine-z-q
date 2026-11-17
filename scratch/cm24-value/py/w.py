import sympy as sp
s = sp.sqrt(-6)
Om = sp.Matrix([[(-4 + 3*s)/14, (-1 - s)/7], [(-1 - s)/7, (-4 + 3*s)/7]])
W = sp.simplify(-Om.inv())
print("W=-Om^-1:", [sp.nsimplify(sp.radsimp(x)) for x in W])
# partial inversion on coordinate 1
O11,O12,O22 = Om[0,0],Om[0,1],Om[1,1]
P1 = sp.Matrix([[-1/O11, O12/O11],[O12/O11, O22-O12**2/O11]])
print("J1 Om:", [sp.radsimp(sp.simplify(x)) for x in P1])
P2 = sp.Matrix([[O11-O12**2/O22, O12/O22],[O12/O22, -1/O22]])
print("J2 Om:", [sp.radsimp(sp.simplify(x)) for x in P2])

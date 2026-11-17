import pickle, sympy as sp, math
d = pickle.load(open('sforms.pkl','rb'))
s = sp.symbols('s0:4')
def ab(p):  # abs-coefficient polynomial value at ones (as PE.abs would give for expanded trees)
    p = sp.Poly(sp.expand(p), *s); return sum(abs(int(c)) for c in p.coeffs()) if not p.is_zero else 0
A = {n: ab(d[n]) for n in ('Psi4','Psi6','X10','X12')}
bl = [(ab(q), ab(r)) for q, r in d['blocks']]
for k in range(3, 10):
    v = [1] + [0]*k
    for q, r in bl:
        v = [v[j] + (q*v[j-1] if j>=1 else 0) + (r*v[j-2] if j>=2 else 0) for j in range(k+1)]
    D, mons = d['INT'][k]
    M = D*v[k] + sum(abs(n)*A['Psi4']**i*A['Psi6']**j*A['X10']**l*A['X12']**m for (i,j,l,m), n in mons)
    b = M.bit_length()
    print(k, 'M bits', b, 'D', 4*k+1, 'H degree <', (4*k+1)**3, 'value bits ~', (b+1)*(4*k+1)**3)

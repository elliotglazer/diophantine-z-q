# Generate Lean PE (polynomial expression) trees for the s-forms from sforms.pkl.
import pickle, sympy as sp
d = pickle.load(open('sforms.pkl', 'rb'))
import subprocess
NB = {}
for line in open('bound.out'):
    w = line.split(); NB[int(w[0])] = int(w[3]) + 1
s = sp.symbols('s0:4')
def mono(c, e):
    fs = []
    for i, k in enumerate(e):
        if k == 1: fs.append('(.v %d)' % i)
        elif k > 1: fs.append('(.pow (.v %d) %d)' % (i, k))
    t = fs[-1] if fs else None
    for f in reversed(fs[:-1]): t = '(.mul %s %s)' % (f, t)
    c = int(c)
    if t is None: return '(.c (%d))' % c
    if c == 1: return t
    return '(.mul (.c (%d)) %s)' % (c, t)
def sumtree(ts):
    if len(ts) == 1: return ts[0]
    m = len(ts) // 2
    return '(.add %s %s)' % (sumtree(ts[:m]), sumtree(ts[m:]))
def pe(p):
    p = sp.Poly(sp.expand(p), *s)
    return sumtree([mono(c, e) for e, c in p.terms()])
def lin(signs):  # s0 + e1 s1 + e2 s2 + e3 s3
    return sumtree(['(.v 0)'] + [('(.v %d)' % i) if e > 0 else '(.mul (.c (-1)) (.v %d))' % i
                                 for i, e in zip((1, 2, 3), signs)])
out = []
out.append('/-- `Ψ₄ = 4ψ₄` in `s_i = U_i²`. -/\ndef psi4E : PE := %s\n' % pe(d['Psi4']))
out.append('/-- `Ψ₆ = 4ψ₆` in `s_i = U_i²`. -/\ndef psi6E : PE := %s\n' % pe(d['Psi6']))
out.append('/-- `X₁₀ = ∏ θ_m² = -2¹⁴χ₁₀` in `s_i = U_i²`. -/\ndef x10E : PE := %s\n' % pe(d['X10']))
X12 = sp.Poly(d['X12'], *s).terms()
ch = [X12[i:i+22] for i in range(0, len(X12), 22)]
for j, c in enumerate(ch):
    out.append('def x12E%d : PE := %s\n' % (j, sumtree([mono(cc, e) for e, cc in c])))
out.append('/-- `X₁₂ = 2¹⁷·3·χ₁₂` in `s_i = U_i²`. -/\ndef x12E : PE := %s\n' % sumtree(['x12E%d' % j for j in range(len(ch))]))
for i, (q, r) in enumerate(d['blocks']):
    out.append('def blkQ%d : PE := %s\n' % (i, pe(q)))
    out.append('def blkR%d : PE := %s\n' % (i, pe(r) if r != 0 else '(.mul (.c 0) (.pow (.v 0) 8))'))
out.append('def blocksPE : List (PE × PE) := [' + ', '.join('(blkQ%d, blkR%d)' % (i, i) for i in range(7)) + ']\n')
for k in range(3, 10):
    D, mons = d['INT'][k]
    terms = []
    for (i, j, l, m), n in mons:
        fs = [('psi4E', i), ('psi6E', j), ('x10E', l), ('x12E', m)]
        fs = [(f if e == 1 else '(.pow %s %d)' % (f, e)) for f, e in fs if e > 0]
        t = fs[-1]
        for f in reversed(fs[:-1]): t = '(.mul %s %s)' % (f, t)
        terms.append('(.mul (.c (%d)) %s)' % (n, t))
    out.append('/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = %d. -/\ndef rhsE%d : PE := %s\n' % (k, k, sumtree(terms)))
    out.append('def dK%d : ℤ := %d\n' % (k, D))
    out.append('def data%d : Data := ⟨blocksPE, %d, dK%d, rhsE%d⟩\n' % (k, k, k, k))
    out.append('''/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = %d, over every commutative ring. -/
theorem gen%d_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data%d.gen s0 s1 s2 s3 = 0 :=
  data%d.gen_eq_zero (2 ^ %d) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3
''' % (k, k, k, k, NB[k]))
open('../gen_pe.lean', 'w').write('\n'.join(out))
print(len('\n'.join(out)))

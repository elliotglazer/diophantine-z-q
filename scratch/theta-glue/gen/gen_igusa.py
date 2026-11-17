# Generates the Igusa part of ThetaGlue.lean (definitions with explicit signs/sets, igusaP).
import pickle, sys
sys.path.insert(0, '../py')
from fractions import Fraction as F
from igusa import syz, goep
from dup_sym import chars
eps = pickle.load(open('../py/psi6_signs.pkl', 'rb')); key = lambda t: tuple(sorted(t))
PK = pickle.load(open('../py/pk.pkl', 'rb'))
def ch(m): return '(![%d, %d], ![%d, %d])' % (m[0][0], m[0][1], m[1][0], m[1][1])
def th(m): return 'PkgI1.thetaConst %s Ω' % ch(m)
def sgn(s, first):
    if first: return '' if s > 0 else '-'
    return ' + ' if s > 0 else ' - '
out = []
# psi6Th
terms = []
for i, t in enumerate(syz):
    terms.append(sgn(eps[key(t)], i == 0) + '(%s * %s * %s) ^ 4' % (th(t[0]), th(t[1]), th(t[2])))
out.append('def psi6Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=\n  (1 / 4) * (' + '\n    '.join(terms) + ')')
terms = []
for i, t in enumerate(syz):
    terms.append(sgn(eps[key(t)], i == 0) + '(t %s * t %s * t %s) ^ 2' % (ch(t[0]), ch(t[1]), ch(t[2])))
out.append('def psi6T (t : PkgI1.Char2 → ℂ) : ℂ :=\n  (1 / 4) * (' + '\n    '.join(terms) + ')')
# chi12Th
comps = [[m for m in chars if m not in q] for q in goep]
terms = [('' if i == 0 else ' + ') + '(' + ' * '.join(th(m) for m in c) + ') ^ 4' for i, c in enumerate(comps)]
out.append('def chi12Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=\n  (1 / (2 ^ 17 * 3)) * (' + '\n    '.join(terms) + ')')
terms = [('' if i == 0 else ' + ') + '(' + ' * '.join('t %s' % ch(m) for m in c) + ') ^ 2' for i, c in enumerate(comps)]
out.append('def chi12T (t : PkgI1.Char2 → ℂ) : ℂ :=\n  (1 / (2 ^ 17 * 3)) * (' + '\n    '.join(terms) + ')')
# igusaP
def frac(c):
    c = F(c)
    return '(%d : ℂ)' % c.numerator if c.denominator == 1 else '(%d / %d : ℂ)' % (c.numerator, c.denominator)
cases = []
for k in range(3, 10):
    mons = []
    for (a, b, c, d), cf in sorted(PK[k].items()):
        fac = ['%s ^ %d' % (v, e) if e > 1 else v for v, e in zip('abcd', (a, b, c, d)) if e > 0]
        mons.append(' * '.join([frac(cf)] + fac))
    cases.append('  | %d, a, b, c, d => %s' % (k, ' + '.join(mons)))
out.append('def igusaP : ℕ → ℂ → ℂ → ℂ → ℂ → ℂ\n' + '\n'.join(cases) + '\n  | _, _, _, _, _ => 0')
open('igusa_defs.lean', 'w').write('\n\n'.join(out) + '\n')
print('ok', len(syz), len(comps))

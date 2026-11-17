# AlgK.lean (Mathlib-only, namespace ThetaGlueAlg): IgusaAlg k.  The heavy step is an identity with
# INTEGER coefficients in an arbitrary commutative ring (`algR`), proved by `ring`; IgusaAlg k follows by
# a linear_combination over the atoms e_k, S4, S6, P, S12.
import sys, pickle
from fractions import Fraction as F
from math import lcm
sys.path.insert(0, '../py')
from igusa import syz, goep
from dup_sym import chars
k = int(sys.argv[1])
mode = sys.argv[2] if len(sys.argv) > 2 else 'tree'
eps = pickle.load(open('../py/psi6_signs.pkl', 'rb')); key = lambda t: tuple(sorted(t))
PK = pickle.load(open('../py/pk.pkl', 'rb'))
pre = open('alg_prefix.lean').read()
pre = pre.replace('import ZInQKernel.OneProof.H.TailA', 'import Mathlib')
pre = pre.replace('namespace HDec.HSyn.G0Split.ThetaPt.ThetaGlue\n', '''namespace ThetaGlueAlg

/-! Verbatim copies from ZInQKernel/OneProof/H/LPrefix.lean (namespace `HDec.PkgI1`). -/
namespace PkgI1
/-- A half-integral characteristic `m = (a, b)`, `a b ∈ {0,1}²`. -/
abbrev Char2 := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)
/-- The ten even characteristics (`aᵀb ≡ 0 mod 2`). -/
def evenChars : Finset Char2 :=
  Finset.univ.filter fun m => ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 0
end PkgI1
''').replace('end HDec.HSyn.G0Split.ThetaPt.ThetaGlue\n', '')
quads = ["x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2", "x0 ^ 2 - x1 ^ 2 + x2 ^ 2 - x3 ^ 2",
 "x0 ^ 2 + x1 ^ 2 - x2 ^ 2 - x3 ^ 2", "x0 ^ 2 - x1 ^ 2 - x2 ^ 2 + x3 ^ 2",
 "2 * x0 * x1 + 2 * x2 * x3", "2 * x0 * x1 - 2 * x2 * x3", "2 * x0 * x2 + 2 * x1 * x3",
 "2 * x0 * x2 - 2 * x1 * x3", "2 * x0 * x3 + 2 * x1 * x2", "2 * x0 * x3 - 2 * x1 * x2"]
Q = {m: '(' + q + ')' for m, q in zip(chars, quads)}
def sgn(s, first): return ('' if s > 0 else '-') if first else (' + ' if s > 0 else ' - ')
S4 = ' + '.join('%s ^ 4' % Q[m] for m in chars)
S6 = ''.join(sgn(eps[key(t)], i == 0) + '(%s * %s * %s) ^ 2' % (Q[t[0]], Q[t[1]], Q[t[2]]) for i, t in enumerate(syz))
PP = ' * '.join(Q[m] for m in chars)
S12 = ' + '.join('(' + ' * '.join(Q[m] for m in chars if m not in q) + ') ^ 2' for q in goep)
# integer coefficients
terms = {}
for (a, b, c, d), cf in PK[k].items():
    terms[(a, b, c, d)] = F(cf) / (F(4)**a * F(4)**b * F(-2**14)**c * F(2**17 * 3)**d)
DEN = 1
for r in terms.values(): DEN = lcm(DEN, r.denominator)
def mono(w):
    a, b, c, d = w
    f = [('S4', a), ('S6', b), ('P', c), ('S12', d)]
    return ' * '.join(('%s ^ %d' % (v, e)) if e > 1 else v for v, e in f if e > 0)
rhs = ' + '.join('(%d : R) * %s' % (int(r * DEN), mono(w)) for w, r in sorted(terms.items()))
def U(t):
    for i, v in enumerate(['u ![0, 0]', 'u ![0, 1]', 'u ![1, 0]', 'u ![1, 1]']): t = t.replace('x%d' % i, v)
    return t
Ys = ', '.join('%s ^ 4' % Q[m] for m in chars)
L = ['''
def esymmG {R : Type*} [CommRing R] : List R → ℕ → R
  | _, 0 => 1
  | [], _ + 1 => 0
  | a :: l, k + 1 => esymmG l (k + 1) + a * esymmG l k

theorem esymmL_eq_G (l : List ℂ) (j : ℕ) : esymmL l j = esymmG l j := by
  induction l generalizing j with
  | nil => cases j <;> rfl
  | cons a l ih => cases j with
    | zero => rfl
    | succ j => simp only [esymmL, esymmG, ih]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- The weight-%d identity with integer coefficients, in any commutative ring. -/
theorem algR%d {R : Type*} [CommRing R] (x0 x1 x2 x3 S4 S6 P S12 : R)
    (h4 : S4 = %s)
    (h6 : S6 = %s)
    (hP : P = %s)
    (h12 : S12 = %s) :
    (%d : R) * esymmG [%s] %d = %s := by
  subst h4 h6 hP h12
  simp only [esymmG]
  ring

theorem hpsi4 (u : (Fin 2 → Fin 2) → ℂ) : psi4T (fun m => Sq m u) = (%s) / 4 := by
  simp only [psi4T, sum_evenChars, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]

theorem hpsi6 (u : (Fin 2 → Fin 2) → ℂ) : psi6T (fun m => Sq m u) = (1 / 4) * (%s) := by
  simp only [psi6T, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]

theorem hchi10 (u : (Fin 2 → Fin 2) → ℂ) : chi10T (fun m => Sq m u) = -(%s) / 2 ^ 14 := by
  simp only [chi10T, prod_evenChars, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]

theorem hchi12 (u : (Fin 2 → Fin 2) → ℂ) : chi12T (fun m => Sq m u) = (1 / (2 ^ 17 * 3)) * (%s) := by
  simp only [chi12T, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]

theorem atom%d (E S4 S6 P S12 : ℂ) (h : (%d : ℂ) * E = %s) :
    E = igusaP %d (S4 / 4) ((1 / 4) * S6) (-P / 2 ^ 14) ((1 / (2 ^ 17 * 3)) * S12) := by
  simp only [igusaP]
  linear_combination (1 / (%d : ℂ)) * h

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem igusaAlg%d : IgusaAlg %d := by
  intro u
  rw [evenChars_val, Multiset.map_coe, esymm_coe, esymmL_eq_G, hpsi4, hpsi6, hchi10, hchi12]
  simp only [List.map, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]
  refine atom%d _ _ _ _ _ ?_
  exact algR%d (u ![0, 0]) (u ![0, 1]) (u ![1, 0]) (u ![1, 1]) _ _ _ _ rfl rfl rfl rfl

end ThetaGlueAlg

#print axioms ThetaGlueAlg.algR%d
#print axioms ThetaGlueAlg.igusaAlg%d
''' % (4 * k, k, S4, S6, PP, S12, DEN, Ys, k, rhs, U(S4), U(S6), U(PP), U(S12), k, DEN, rhs.replace('(R)', '(ℂ)').replace(': R)', ': ℂ)'), k, DEN, k, k, k, k, k, k)]
open('../Alg%d.lean' % k, 'w').write(pre + '\n'.join(L))
print('DEN', DEN)

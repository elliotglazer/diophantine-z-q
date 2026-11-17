# AlgK.lean (Mathlib-only, namespace ThetaGlueAlg): IgusaAlg k with explicit intermediate normal forms
# (computed by py/), each proved by its own `ring`:
#   EA a : e_a(Y0..Y4) = NF,  EB b : e_b(Y5..Y9) = NF,  NS4/NS6/NP/NS12 : S = NF,
# then e_k(Y0..Y9) = sum_a e_a(Y0..Y4) e_{k-a}(Y5..Y9) (convolution, proved generically) and one final ring.
import sys, pickle
from fractions import Fraction as F
sys.path.insert(0, '../py')
from poly import P
from dup_sym import S, chars
from igusa import syz, goep
k = int(sys.argv[1])
out = sys.argv[2] if len(sys.argv) > 2 else '../Alg%d.lean' % k
eps = pickle.load(open('../py/psi6_signs.pkl', 'rb')); key = lambda t: tuple(sorted(t))
pre = open('alg_prefix.lean').read()
pre = pre.replace('import ZInQKernel.OneProof.H.TailA', 'import Mathlib')
pre = pre.replace('namespace HDec.HSyn.G0Split.ThetaPt.ThetaGlue\n', '''set_option profiler true
set_option profiler.threshold 2000

namespace ThetaGlueAlg

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
Qp = {m: S[m] for m in chars}
def ptxt(p):
    if p.iszero(): return '0'
    items = []
    for e, c in sorted(p.d.items(), reverse=True):
        c = F(c); assert c.denominator == 1
        items.append('(%d, %d, %d, %d, %d)' % ((c.numerator,) + tuple(e)))
    return 'pe [' + ', '.join(items) + '] x0 x1 x2 x3'
def ptxt_old(p):
    if p.iszero(): return '0'
    out = []
    for e, c in sorted(p.d.items(), reverse=True):
        mon = ' * '.join(('x%d ^ %d' % (i, n)) if n > 1 else 'x%d' % i for i, n in enumerate(e) if n > 0)
        c = F(c); cs = ('(%d : ℂ)' % c.numerator) if c.denominator == 1 else '(%d / %d : ℂ)' % (c.numerator, c.denominator)
        out.append(cs + (' * ' + mon if mon else ''))
    return ' + '.join(out)
def sgn(s, first): return ('' if s > 0 else '-') if first else (' + ' if s > 0 else ' - ')
one = P.const(1, 4)
def prod(xs):
    r = one
    for x in xs: r = r * x
    return r
S4t = ' + '.join('%s ^ 4' % Q[m] for m in chars); S4p = sum((Qp[m]**4 for m in chars), P.const(0, 4))
S6t = ''.join(sgn(eps[key(t)], i == 0) + '(%s * %s * %s) ^ 2' % (Q[t[0]], Q[t[1]], Q[t[2]]) for i, t in enumerate(syz))
S6p = sum(((Qp[t[0]] * Qp[t[1]] * Qp[t[2]])**2 * eps[key(t)] for t in syz), P.const(0, 4))
Pt = ' * '.join(Q[m] for m in chars); Pp = prod(Qp[m] for m in chars)
S12t = ' + '.join('(' + ' * '.join(Q[m] for m in chars if m not in q) + ') ^ 2' for q in goep)
S12p = sum((prod(Qp[m] for m in chars if m not in q)**2 for q in goep), P.const(0, 4))
Y = [Qp[m]**4 for m in chars]; Yt = ['%s ^ 4' % Q[m] for m in chars]
def esym(ys, j):
    e = [one] + [P.const(0, 4)] * j
    for y in ys:
        for t in range(j, 0, -1): e[t] = e[t] + e[t - 1] * y
    return e
EA = esym(Y[:5], min(k, 5)); EB = esym(Y[5:], min(k, 5))
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

/-- A polynomial in `x₀..x₃` from its list of (coefficient, exponents). -/
def pe (l : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (x0 x1 x2 x3 : ℂ) : ℂ :=
  (l.map fun t => (t.1 : ℂ) * x0 ^ t.2.1 * x1 ^ t.2.2.1 * x2 ^ t.2.2.2.1 * x3 ^ t.2.2.2.2).sum

theorem esymmG_eq_zero_of_lt {R : Type*} [CommRing R] :
    ∀ (l : List R) (j : ℕ), l.length < j → esymmG l j = 0
  | [], 0, h => absurd h (by simp)
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => absurd h (by simp)
  | a :: l, j + 1, h => by
    rw [esymmG, esymmG_eq_zero_of_lt l (j + 1) (by simp at h; omega),
      esymmG_eq_zero_of_lt l j (by simp at h; omega)]
    ring

theorem esymmG_nil {R : Type*} [CommRing R] (j : ℕ) : esymmG ([] : List R) j = if j = 0 then 1 else 0 := by
  cases j <;> rfl

/-- Convolution: `e_k(l₁ ++ l₂) = Σ_{a ≤ k} e_a(l₁) e_{k-a}(l₂)`. -/
theorem esymmG_append {R : Type*} [CommRing R] (l₁ l₂ : List R) (k : ℕ) :
    esymmG (l₁ ++ l₂) k = ∑ a ∈ Finset.range (k + 1), esymmG l₁ a * esymmG l₂ (k - a) := by
  induction l₁ generalizing k with
  | nil =>
    rw [Finset.sum_range_succ']
    simp [esymmG_nil]
  | cons x l ih =>
    cases k with
    | zero => simp [esymmG]
    | succ k =>
      rw [List.cons_append, esymmG, ih, ih]
      rw [Finset.sum_range_succ' (fun a => esymmG (x :: l) a * esymmG l₂ (k + 1 - a)) (k + 1)]
      rw [Finset.sum_range_succ' (fun a => esymmG l a * esymmG l₂ (k + 1 - a)) (k + 1)]
      simp only [esymmG, Nat.add_sub_add_right, Nat.sub_zero, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
      ring
''']
# definitions of the four theta-expression polynomials and the two half-lists (elaborated once)
U = lambda t: t.replace('x0', 'u ![0, 0]').replace('x1', 'u ![0, 1]').replace('x2', 'u ![1, 0]').replace('x3', 'u ![1, 1]')
SQ = 'Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9'
XU = "(u ![0, 0]) (u ![0, 1]) (u ![1, 0]) (u ![1, 1])"
D = lambda name, typ, body: "set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\ndef %s (x0 x1 x2 x3 : ℂ) : %s :=\n  %s\n" % (name, typ, body)
L.append(D('S4x', 'ℂ', S4t)); L.append(D('S6x', 'ℂ', S6t)); L.append(D('Px', 'ℂ', Pt)); L.append(D('S12x', 'ℂ', S12t))
L.append(D('YA', 'List ℂ', '[' + ', '.join(Yt[:5]) + ']')); L.append(D('YB', 'List ℂ', '[' + ', '.join(Yt[5:]) + ']'))
HP = """set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem %s (u : (Fin 2 → Fin 2) → ℂ) : %s (fun m => Sq m u) = %s := by
  simp only [%s, %s]
"""
L.append(HP % ('hpsi4', 'psi4T', 'S4x %s / 4' % XU, 'psi4T, sum_evenChars, S4x', SQ))
L.append(HP % ('hpsi6', 'psi6T', '(1 / 4) * S6x %s' % XU, 'psi6T, S6x', SQ))
L.append(HP % ('hchi10', 'chi10T', '-Px %s / 2 ^ 14' % XU, 'chi10T, prod_evenChars, Px', SQ))
L.append(HP % ('hchi12', 'chi12T', '(1 / (2 ^ 17 * 3)) * S12x %s' % XU, 'chi12T, S12x', SQ))
L.append("""set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem hY (u : (Fin 2 → Fin 2) → ℂ) :
    List.map (fun m => Sq m u ^ 4) [(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]),
      (![0, 0], ![1, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]), (![1, 0], ![0, 0]),
      (![1, 0], ![0, 1]), (![1, 1], ![0, 0]), (![1, 1], ![1, 1])] = YA %s ++ YB %s := by
  simp only [List.map, YA, YB, List.cons_append, List.nil_append, %s]
""" % (XU, XU, SQ))
def nf_lemma(name, lhs, p, unf):
    return """set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem %s (x0 x1 x2 x3 : ℂ) : %s =
    %s := by
  simp only [%s, pe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  all_goals ring
""" % (name, lhs, ptxt(p), unf)
X = 'x0 x1 x2 x3'
L.append(nf_lemma('NS4', 'S4x ' + X, S4p, 'S4x')); L.append(nf_lemma('NS6', 'S6x ' + X, S6p, 'S6x'))
L.append(nf_lemma('NP', 'Px ' + X, Pp, 'Px')); L.append(nf_lemma('NS12', 'S12x ' + X, S12p, 'S12x'))
for a in range(0, min(k, 5) + 1):
    L.append(nf_lemma('EA%d' % a, 'esymmG (YA %s) %d' % (X, a), EA[a], 'YA, esymmG'))
    L.append(nf_lemma('EB%d' % a, 'esymmG (YB %s) %d' % (X, a), EB[a], 'YB, esymmG'))
zs = []
for a in range(0, k + 1):
    if a > 5: zs.append('esymmG_eq_zero_of_lt (YA %s) %d (by simp [YA])' % (X, a))
    if k - a > 5: zs.append('esymmG_eq_zero_of_lt (YB %s) %d (by simp [YB])' % (X, k - a))
zline = ('  rw [%s]\n' % ', '.join(zs)) if zs else ''
ea = ', '.join('EA%d, EB%d' % (a, a) for a in range(0, min(k, 5) + 1))
L.append("""set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem igusaAlg%d : IgusaAlg %d := by
  intro u
  rw [evenChars_val, Multiset.map_coe, esymm_coe, esymmL_eq_G, hY, esymmG_append, hpsi4, hpsi6,
    hchi10, hchi12]
  generalize u ![0, 0] = x0
  generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2
  generalize u ![1, 1] = x3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub]
%s  simp only [%s, NS4, NS6, NP, NS12, igusaP]
  simp only [pe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

end ThetaGlueAlg

#print axioms ThetaGlueAlg.igusaAlg%d
""" % (k, k, zline, ea, k))
open(out, 'w').write(pre + '\n'.join(L))

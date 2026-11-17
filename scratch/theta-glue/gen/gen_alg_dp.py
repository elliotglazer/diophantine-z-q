# Generates AlgDP<k>.lean: IgusaAlg k by a dynamic programme over e_j(y_i..y_9) with ring_nf after
# each step (shares the intermediate normal forms instead of re-expanding the recursion tree).
import sys
k = int(sys.argv[1])
pre = open('alg_prefix.lean').read()
quads = ["x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2", "x0 ^ 2 - x1 ^ 2 + x2 ^ 2 - x3 ^ 2",
 "x0 ^ 2 + x1 ^ 2 - x2 ^ 2 - x3 ^ 2", "x0 ^ 2 - x1 ^ 2 - x2 ^ 2 + x3 ^ 2",
 "2 * x0 * x1 + 2 * x2 * x3", "2 * x0 * x1 - 2 * x2 * x3", "2 * x0 * x2 + 2 * x1 * x3",
 "2 * x0 * x2 - 2 * x1 * x3", "2 * x0 * x3 + 2 * x1 * x2", "2 * x0 * x3 - 2 * x1 * x2"]
L = []
L.append('''
theorem esymmL_eq_zero : ∀ (l : List ℂ) (j : ℕ), l.length < j → esymmL l j = 0
  | [], 0, h => absurd h (by simp)
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => absurd h (by simp)
  | a :: l, j + 1, h => by
    rw [esymmL, esymmL_eq_zero l (j + 1) (by simp at h; omega),
      esymmL_eq_zero l j (by simp at h; omega)]
    ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem igusaAlg%d : IgusaAlg %d := by
  intro u
  rw [evenChars_val, Multiset.map_coe, esymm_coe]
  simp only [psi4T, chi10T, psi6T, chi12T, igusaP, sum_evenChars, prod_evenChars, List.map]
  simp only [Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]
  generalize u ![0, 0] = x0
  generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2
  generalize u ![1, 1] = x3''' % (k, k))
for i, q in enumerate(quads):
    L.append('  generalize hY%d : (%s) ^ 4 = Y%d' % (i, q, i))
def lst(i): return '[' + ', '.join('Y%d' % t for t in range(i, 10)) + ']'
# base i = 9
L.append('  have d9_0 : esymmL %s 0 = 1 := rfl' % lst(9))
L.append('  have d9_1 : esymmL %s 1 = 0 + Y9 * 1 := rfl' % lst(9))
L.append('  conv at d9_1 => rhs; rw [← hY9]; ring_nf')
for i in range(8, -1, -1):
    n = 10 - i
    L.append('  have d%d_0 : esymmL %s 0 = 1 := rfl' % (i, lst(i)))
    for j in range(1, min(k, n) + 1):
        a = 'd%d_%d' % (i + 1, j) if j <= n - 1 else None
        b = 'd%d_%d' % (i + 1, j - 1)
        L.append('  have d%d_%d : esymmL %s %d = esymmL %s %d + Y%d * esymmL %s %d := rfl' %
                 (i, j, lst(i), j, lst(i + 1), j, i, lst(i + 1), j - 1))
        rw = ([a] if a else ['esymmL_eq_zero %s %d (by simp)' % (lst(i + 1), j)]) + [b]
        L.append('  rw [%s] at d%d_%d' % (', '.join(rw), i, j))
        L.append('  conv at d%d_%d => rhs; rw [← hY%d]; ring_nf' % (i, j, i))
    # clear level i+1 facts
    L.append('  clear %s' % ' '.join('d%d_%d' % (i + 1, j) for j in range(0, min(k, n - 1) + 1)))
L.append('  rw [d0_%d]' % k)
L.append('  subst %s' % ' '.join('hY%d' % i for i in range(10)))
L.append('  ring')
L.append('\nend HDec.HSyn.G0Split.ThetaPt.ThetaGlue\n\n#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaGlue.igusaAlg%d\n' % k)
open('../AlgDP%d.lean' % k, 'w').write(pre + '\n'.join(L))

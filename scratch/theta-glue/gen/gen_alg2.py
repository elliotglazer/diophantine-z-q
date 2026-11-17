# AlgK.lean (Mathlib-only): IgusaAlg k for a verbatim copy of the definitions, with the PkgI1 names
# copied verbatim from ZInQKernel/OneProof/H/LPrefix.lean; proof: normal forms of psi4, psi6, chi10,
# chi12 and a dynamic programme for e_k, each step normalized by ring_nf, then ring.
import sys
k = int(sys.argv[1])
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
''')
quads = ["x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2", "x0 ^ 2 - x1 ^ 2 + x2 ^ 2 - x3 ^ 2",
 "x0 ^ 2 + x1 ^ 2 - x2 ^ 2 - x3 ^ 2", "x0 ^ 2 - x1 ^ 2 - x2 ^ 2 + x3 ^ 2",
 "2 * x0 * x1 + 2 * x2 * x3", "2 * x0 * x1 - 2 * x2 * x3", "2 * x0 * x2 + 2 * x1 * x3",
 "2 * x0 * x2 - 2 * x1 * x3", "2 * x0 * x3 + 2 * x1 * x2", "2 * x0 * x3 - 2 * x1 * x2"]
L = ['''
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
  simp only [igusaP, List.map]
  generalize hA : psi4T (fun m => Sq m u) = A
  generalize hB : psi6T (fun m => Sq m u) = B
  generalize hC : chi10T (fun m => Sq m u) = C
  generalize hD : chi12T (fun m => Sq m u) = D
  simp only [psi4T, chi10T, psi6T, chi12T, sum_evenChars, prod_evenChars] at hA hB hC hD
  simp only [Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9] at hA hB hC hD ⊢
  generalize u ![0, 0] = x0 at hA hB hC hD ⊢
  generalize u ![0, 1] = x1 at hA hB hC hD ⊢
  generalize u ![1, 0] = x2 at hA hB hC hD ⊢
  generalize u ![1, 1] = x3 at hA hB hC hD ⊢
  conv at hA => lhs; ring_nf
  conv at hB => lhs; ring_nf
  conv at hC => lhs; ring_nf
  conv at hD => lhs; ring_nf''' % (k, k)]
for i, q in enumerate(quads):
    L.append('  generalize hY%d : (%s) ^ 4 = Y%d' % (i, q, i))
def lst(i): return '[' + ', '.join('Y%d' % t for t in range(i, 10)) + ']'
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
    L.append('  clear %s' % ' '.join('d%d_%d' % (i + 1, j) for j in range(0, min(k, n - 1) + 1)))
L.append('  rw [d0_%d]' % k)
L.append('  (try rw [← hA]); (try rw [← hB]); (try rw [← hC]); (try rw [← hD])')
L.append('  ring')
L.append('\nend ThetaGlueAlg\n\n#print axioms ThetaGlueAlg.igusaAlg%d\n' % k)
open('../Alg%d.lean' % k, 'w').write(pre.replace('end HDec.HSyn.G0Split.ThetaPt.ThetaGlue\n', '') + '\n'.join(L))

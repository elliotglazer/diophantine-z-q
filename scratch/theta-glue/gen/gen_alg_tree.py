# AlgK.lean (Mathlib-only, namespace ThetaGlueAlg): IgusaAlg k by unfolding everything and one closing
# tactic (ring or grind).
import sys
k = int(sys.argv[1]); tac = sys.argv[2] if len(sys.argv) > 2 else 'ring'
out = sys.argv[3] if len(sys.argv) > 3 else '../Alg%d.lean' % k
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
thm = '''
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem igusaAlg%d : IgusaAlg %d := by
  intro u
  rw [evenChars_val, Multiset.map_coe, esymm_coe]
  simp only [psi4T, chi10T, psi6T, chi12T, igusaP, sum_evenChars, prod_evenChars, List.map, esymmL]
  simp only [Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]
  generalize u ![0, 0] = x0
  generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2
  generalize u ![1, 1] = x3
  %s

end ThetaGlueAlg

#print axioms ThetaGlueAlg.igusaAlg%d
''' % (k, k, tac, k)
open(out, 'w').write(pre + thm)

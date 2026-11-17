# Assemble Bridge.lean: Core (Kronecker) + generated PE data + verbatim theta-glue definitions + bridge.
import sys
mode = sys.argv[1] if len(sys.argv) > 1 else 'dev'   # dev: Mathlib-only copies; final: TailA
ks = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else list(range(3, 10))
out = sys.argv[3] if len(sys.argv) > 3 else 'Bridge.lean'
core = open('Core.lean').read()
core = core.replace('end IgusaAlgEval\n', '').replace('import Mathlib\n', '')
gen = open('gen_pe.lean').read()
pre = open('../theta-glue/gen/alg_prefix.lean').read()
pre_body = pre.split('noncomputable section\n', 1)[1]
if mode == 'dev':
    hdr = 'import Mathlib\n'
    pre_body = pre_body.replace('namespace HDec.HSyn.G0Split.ThetaPt.ThetaGlue\n', '''namespace ThetaGlueAlg

/-! Verbatim copies from ZInQKernel/OneProof/H/LPrefix.lean (namespace `HDec.PkgI1`). -/
namespace PkgI1
/-- A half-integral characteristic `m = (a, b)`, `a b ∈ {0,1}²`. -/
abbrev Char2 := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)
/-- The ten even characteristics (`aᵀb ≡ 0 mod 2`). -/
def evenChars : Finset Char2 :=
  Finset.univ.filter fun m => ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 0
end PkgI1
''')
    ns_end = 'end ThetaGlueAlg\n'
    nsname = 'ThetaGlueAlg'
else:
    hdr = 'import ZInQKernel.OneProof.H.TailA\n'
    ns_end = 'end HDec.HSyn.G0Split.ThetaPt.ThetaGlue\n'
    nsname = 'HDec.HSyn.G0Split.ThetaPt.ThetaGlue'
EV = '''
theorem PE.eval_v0 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 0 = s0 := rfl
theorem PE.eval_v1 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 1 = s1 := rfl
theorem PE.eval_v2 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 2 = s2 := rfl
theorem PE.eval_v3 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 3 = s3 := rfl
'''
bridge = r'''
/-! ## igusa-alg: `IgusaAlg k` from the Kronecker-checked identities in `s_i = U_i²` -/

open IgusaAlgEval

theorem esymmL_nil (j : ℕ) : esymmL [] j = E ([] : List (ℂ × ℂ)) j := by cases j <;> rfl

theorem esymmL_single {l : List ℂ} {bl : List (ℂ × ℂ)} (h : ∀ j, esymmL l j = E bl j) (a : ℂ) :
    ∀ j, esymmL (a :: l) j = E ((a, 0) :: bl) j := by
  intro j
  cases j with
  | zero => simp [esymmL, E, ← h 0]
  | succ j => simp [esymmL, E, h]

theorem esymmL_pair {l : List ℂ} {bl : List (ℂ × ℂ)} (h : ∀ j, esymmL l j = E bl j) (a b : ℂ) :
    ∀ j, esymmL (a :: b :: l) j = E ((a + b, a * b) :: bl) j := by
  intro j
  rcases j with _ | _ | j
  · simp [esymmL, E, ← h 0]
  · simp [esymmL, E, ← h 0, ← h 1]; ring
  · simp [esymmL, E, h]; ring

theorem esymmL_blocks (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℂ) (k : ℕ) :
    esymmL [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] k =
      E [(a0, 0), (a1, 0), (a2, 0), (a3, 0), (a4 + a5, a4 * a5), (a6 + a7, a6 * a7), (a8 + a9, a8 * a9)] k :=
  esymmL_single (esymmL_single (esymmL_single (esymmL_single (esymmL_pair (esymmL_pair
    (esymmL_pair esymmL_nil a8 a9) a6 a7) a4 a5) a3) a2) a1) a0 k

set_option maxHeartbeats 4000000 in
theorem blocks_eval (x0 x1 x2 x3 : ℂ) :
    blocksPE.map (evB (x0 ^ 2) (x1 ^ 2) (x2 ^ 2) (x3 ^ 2)) =
      [((x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) ^ 4, 0), ((x0 ^ 2 - x1 ^ 2 + x2 ^ 2 - x3 ^ 2) ^ 4, 0),
       ((x0 ^ 2 + x1 ^ 2 - x2 ^ 2 - x3 ^ 2) ^ 4, 0), ((x0 ^ 2 - x1 ^ 2 - x2 ^ 2 + x3 ^ 2) ^ 4, 0),
       ((2 * x0 * x1 + 2 * x2 * x3) ^ 4 + (2 * x0 * x1 - 2 * x2 * x3) ^ 4,
         (2 * x0 * x1 + 2 * x2 * x3) ^ 4 * (2 * x0 * x1 - 2 * x2 * x3) ^ 4),
       ((2 * x0 * x2 + 2 * x1 * x3) ^ 4 + (2 * x0 * x2 - 2 * x1 * x3) ^ 4,
         (2 * x0 * x2 + 2 * x1 * x3) ^ 4 * (2 * x0 * x2 - 2 * x1 * x3) ^ 4),
       ((2 * x0 * x3 + 2 * x1 * x2) ^ 4 + (2 * x0 * x3 - 2 * x1 * x2) ^ 4,
         (2 * x0 * x3 + 2 * x1 * x2) ^ 4 * (2 * x0 * x3 - 2 * x1 * x2) ^ 4)] := by
  simp only [blocksPE, List.map_cons, List.map_nil, evB, blkQ0, blkQ1, blkQ2, blkQ3, blkQ4, blkQ5,
    blkQ6, blkR0, blkR1, blkR2, blkR3, blkR4, blkR5, blkR6, PE.eval, PE.eval_v0, PE.eval_v1,
    PE.eval_v2, PE.eval_v3, List.cons.injEq, Prod.mk.injEq, and_true]
  push_cast
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> ring

set_option maxHeartbeats 4000000 in
theorem psi4T_eq (u : (Fin 2 → Fin 2) → ℂ) : psi4T (fun m => Sq m u) =
    psi4E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2) / 4 := by
  simp only [psi4T, sum_evenChars, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, psi4E, PE.eval,
    PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

set_option maxHeartbeats 4000000 in
theorem psi6T_eq (u : (Fin 2 → Fin 2) → ℂ) : psi6T (fun m => Sq m u) =
    psi6E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2) / 4 := by
  simp only [psi6T, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, psi6E, PE.eval,
    PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

set_option maxHeartbeats 4000000 in
theorem chi10T_eq (u : (Fin 2 → Fin 2) → ℂ) : chi10T (fun m => Sq m u) =
    -(x10E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2)) / 2 ^ 14 := by
  simp only [chi10T, prod_evenChars, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, x10E, PE.eval,
    PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

set_option maxHeartbeats 0 in
theorem chi12T_eq (u : (Fin 2 → Fin 2) → ℂ) : chi12T (fun m => Sq m u) =
    x12E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2) / (2 ^ 17 * 3) := by
  simp only [chi12T, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, x12E, x12E0, x12E1, x12E2,
    x12E3, PE.eval, PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

theorem igusaAlg_of_data (k : ℕ) (X : Data) (hk : X.k = k) (hb : X.blocks = blocksPE) (hD : X.dK ≠ 0)
    (hgen : ∀ s0 s1 s2 s3 : ℂ, X.gen s0 s1 s2 s3 = 0)
    (hrhs : ∀ s0 s1 s2 s3 : ℂ, X.rhs.eval s0 s1 s2 s3 = (X.dK : ℂ) *
      igusaP k (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
        (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3))) :
    IgusaAlg k := by
  intro u
  have h := hgen (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2)
  rw [Data.gen, hrhs, hb, hk, sub_eq_zero, blocks_eval] at h
  rw [psi4T_eq, psi6T_eq, chi10T_eq, chi12T_eq, evenChars_val, Multiset.map_coe, esymm_coe]
  simp only [List.map, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]
  rw [esymmL_blocks]
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hD) h
'''
for k in ks:
    bridge += r'''
set_option maxHeartbeats 4000000 in
theorem rhs%(k)d_eq (s0 s1 s2 s3 : ℂ) : rhsE%(k)d.eval s0 s1 s2 s3 = ((dK%(k)d : ℤ) : ℂ) *
    igusaP %(k)d (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE%(k)d, dK%(k)d, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg %(k)d` (theta-glue's GLUE), proved.** -/
theorem igusaAlg%(k)d : IgusaAlg %(k)d :=
  igusaAlg_of_data %(k)d data%(k)d rfl rfl (by decide) (fun s0 s1 s2 s3 => gen%(k)d_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs%(k)d_eq s0 s1 s2 s3)
''' % {'k': k}
pre_body = pre_body.replace(ns_end, '')
src = hdr + '\n' + core + EV + '\n' + gen + '\nend IgusaAlgEval\n\nnoncomputable section\n' + pre_body + bridge + '\n' + ns_end + '\n'
src += ''.join('#print axioms %s.igusaAlg%d\n' % (nsname, k) for k in ks)
open(out, 'w').write(src)

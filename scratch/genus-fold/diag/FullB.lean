import ZInQKernel.OneProof.H.TailD
import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.T28.Assemble
import ZInQKernel.Contrib.RLeaf.X1ConstantField
import ZInQKernel.Contrib.Mobius.Main
import ZInQKernel.OneProof.H.LF2Stalks
import ZInQKernel.OneProof.H.LF2UnifRoot
import ZInQKernel.OneProof.H.LF2SmoothDim
import ZInQKernel.OneProof.H.LF2UnramConj
import ZInQKernel.Contrib.HeightBC.CotangentSpan
import ZInQKernel.Contrib.HeightBC.UniformizationLift
import ZInQKernel.Contrib.HeightBC.Main
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.AbVarBC.Tate
import ZInQKernel.Contrib.AbVarBC.Torsion
import ZInQKernel.Contrib.AbVarBC.Mul
import ZInQKernel.Contrib.AbVarBC.Tangent
import ZInQKernel.Contrib.AbVarBC.KerUnit
import ZInQKernel.Contrib.AbVarBC.G9Instance
import ZInQKernel.Contrib.AbVarBC.Main
import Lean
open Lean Elab Command
namespace HDec
namespace ZInQ.Contrib.AbVarBC
def diagT : Prop := ∀ (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      _root_.ZInQ.Contrib.AbVarBC.TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ),
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange
end ZInQ.Contrib.AbVarBC
end HDec
run_cmd do
  let some ci := (← getEnv).find? `HDec.ZInQ.Contrib.AbVarBC.diagT | throwError "x"
  logInfo m!"hash {ci.value!.hash}"
set_option pp.explicit true in
#print HDec.ZInQ.Contrib.AbVarBC.diagT

import ZInQKernel.OneProof.H.TailC
import ZInQKernel.Contrib.AbVarBC.Tate
import ZInQKernel.OneProof.Genus.LocalDer
set_option pp.explicit true
set_option pp.funBinderTypes true
open ZInQ.Contrib.AbVarBC in
def diagT : Prop := ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ
#print diagT

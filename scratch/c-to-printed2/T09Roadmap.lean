import ZInQKernel.OneProof.H.TailZ15

/-! # c-to-printed2: the first link of a published-form chain for T09 is statable today

Only a statability check (report §5, item 1); nothing here is used. `picardFunctor` is the vendored relative Picard
fppf sheaf (`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Picard/Sheaf.lean`), and
`PkgI3.AbVar` the shared abelian-variety structure (`ZInQKernel/HDecomp/Objects.lean`). -/

open CategoryTheory AlgebraicGeometry

namespace CToPrinted2.T09Roadmap

/-- **Candidate LEAF (not used; UNVERIFIED numbering): Grothendieck's representability of the Picard functor**, for
abelian varieties (projective over `K`). Grothendieck, FGA, Exp. 232, Thm 3.1; Kleiman, *The Picard scheme* (FGA
Explained, 2005), Thm 9.4.8; Mumford, *Abelian varieties*, §8, over an algebraically closed field. -/
def PicRepresentableAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ∃ P : Over (Spec (CommRingCat.of K)), Nonempty ((picardFunctor A.X.hom).obj.RepresentableBy P)

end CToPrinted2.T09Roadmap

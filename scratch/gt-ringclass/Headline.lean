import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! gt-ringclass: the single proof with hypothesis `hS` replaced by the two printed leaves
(the shape a fold of `T5Glue.shimuraReciprocityModFn_of_printed` gives `frozenTarget`). -/

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus in
theorem GtRingclass.frozenTarget_printedT5
    (r : HDec.HSyn.OpenResearchLeaves16) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves14)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : T5Glue.ShimuraMainCM) (hX : T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29 (T5Glue.shimuraReciprocityModFn_of_printed hCM hX) h33 hL2 hL3

#print axioms GtRingclass.frozenTarget_printedT5

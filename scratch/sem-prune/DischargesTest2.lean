import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges

/-! Positive and negative controls for `#discharges` (task contrib-kit). Expected:
`t1` discharges `OpenGlue7.quotientP1Coordinate` and still assumes it; `t2` discharges nothing;
`t3` discharges `OpenTextbookLeaves10.cartierSmooth` (sem-prune: bdRInvariants is pruned, so the control moves to another field) and is flagged for `sorry`. -/

theorem t1 (h : HDec.MCRGlue.QuotientP1Coordinate) : HDec.MCRGlue.QuotientP1Coordinate := h

theorem t2 : True := trivial

theorem t3 : _root_.AVGlue.CartierSmooth := sorry

#discharges

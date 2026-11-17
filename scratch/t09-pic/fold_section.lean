
/-! ## Fold check (not part of the report's proof): the field replaced in leaf-fold12's bundle -/

namespace HDec

namespace HSyn

/-- leaf-fold12's `OpenAddedLeaves11` with `t09SymmIsogenyExists` replaced by t09-pic's four printed leaves
(16 fields; the 12 other fields copied verbatim from `ZInQKernel/OneProof/H/TailZ18.lean`). -/
structure OpenAddedLeaves11T09Pic : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
  /-- t09-pic L1: `Pic_{A/K}` representable (Murre–Oort; FGA 232; Kleiman 9.4.8). -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic L2: `Pic⁰_{A/K}` is an abelian variety (Mumford §13; Kleiman 9.5). -/
  picZeroAbVar : _root_.T09Pic.PicZeroAbVar
  /-- t09-pic L3: `φ_L` is an isogeny for ample `L` (Mumford §6 App. 1, §8 Thm 1). -/
  phiAmpleIsogeny : _root_.T09Pic.PhiAmpleIsogeny
  /-- t09-pic L4: Mumford's `ē_n` at `Pic⁰` (Mumford §§20, 23). -/
  weilPairingMumford : _root_.T09Pic.WeilPairingMumford

/-- The bundle `OpenAddedLeaves11` from t09-pic's leaves. -/
theorem openAddedLeaves11_of_t09pic (l : OpenAddedLeaves11T09Pic) : OpenAddedLeaves11 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := _root_.T09Pic.t09SymmIsogenyExists_of_four
    l.picRepresentableAbVar l.picZeroAbVar l.phiAmpleIsogeny l.weilPairingMumford
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  deligneComponentsY3PrintedAb := l.deligneComponentsY3PrintedAb

/-- `ZInQ.SixContactMin` with t09-pic's leaves in place of `t09SymmIsogenyExists`. -/
theorem sixContactMin_of_open15_t09pic (r : OpenResearchLeaves12) (t : OpenTextbookLeaves10)
    (l : OpenAddedLeaves11T09Pic) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open15 r t (openAddedLeaves11_of_t09pic l) g

end HSyn

end HDec

example (l : HDec.HSyn.OpenAddedLeaves11) : HDec.WeilPairing.T09_SymmIsogenyExists := l.t09SymmIsogenyExists

#print axioms T09Pic.t09SymmIsogenyExists_of_four
#print axioms HDec.HSyn.sixContactMin_of_open15_t09pic

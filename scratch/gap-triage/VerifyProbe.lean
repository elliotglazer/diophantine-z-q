import ZInQKernel.OneProof.H.TailZ15
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-! gap-triage: #check of the library and chain declarations that the triage cites as VERIFIED. -/

open CategoryTheory AlgebraicGeometry

-- Mathlib (analytic tools for the Γ* valence formula, theta)
#check @jacobiTheta₂_functional_equation
#check @MeromorphicOn.circleAverage_log_norm
#check @MeasureTheory.IsFundamentalDomain.measure_eq
#check (inferInstance : MeasureTheory.SMulInvariantMeasure (GL (Fin 2) ℝ) UpperHalfPlane MeasureTheory.volume)
-- Mathlib + CloudW01 (EGA IV 8.10.5 open-immersion leaf)
#check @AlgebraicGeometry.exists_preimage_eq
#check @AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange
#check @AlgebraicGeometry.baseChangeConeIsLimit
-- chain: QM lattice route (qmCentralizerCMC, yuThm11)
#check @HDec.HSyn.G0Split.FibreQM.qmComplexUnif_of_textbook
#check @HDec.HSyn.G0Split.FibreQM.qmSkolemNoetherC_proof
#check @HDec.QMSplit.CNO.qmClassNumberOne_proof
#check @HDec.QMSplit.Aut.rows_of_C
#check @HDec.QMSplit.Yu.qmDichotomyYu_of_yu
#check @AvSplit.Final.h69
#check @AvSplit.Final.h38
-- chain: T5 over ℂ, AbVarBC tangent lemma, r6 piece
#check @T5Torsion.torsionStructureC_of_uniformization
#check @ZInQ.Contrib.AbVarBC.Tangent.eq_one_of_comp_intCast
#check @ReductGlue.exists_rational_of_fixed_etale
-- chain: G9 (bdRInvariants finding)
#check @ZInQ.Contrib.G9.g9Glue_of_fieldEmb
#check @HDec.G0Galois.g12Det_of
-- GZ: weakened statements in the tree

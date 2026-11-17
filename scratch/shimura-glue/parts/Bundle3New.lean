/-! # shimura-glue: the bundle with the ray-class form of Shimura reciprocity -/

namespace HDec.QMSplit.Moduli

/-- **`ShimuraGlueLeaves2` with `ReciprocityCanonical` replaced by its ray-class form
`ShimuraGlue.Ray.RayClassCM`.** -/
structure ShimuraGlueLeaves3 : Prop where
  deligneX6P : ShimuraGlue.DeligneComponentsX6Printed
  geomConn : GeomConnOfAlgClosure
  t5 : PkgI2.TorsionStructure.{0}
  babaGranathR : BabaGranathRational
  rayClass : ShimuraGlue.Ray.RayClassCM
  gonzalezRotger : GonzalezRotgerX6
  gonzalezRotgerCount : ShimuraSplit.GonzalezRotgerCountX6
  deligneY3P : ShimuraGlue.DeligneComponentsY3Printed
  elkiesT : ElkiesConicT

theorem shimuraGlueLeaves2_of_3 (L : ShimuraGlueLeaves3) : ShimuraGlueLeaves2 :=
  ⟨L.deligneX6P, L.geomConn, L.t5, L.babaGranathR,
    ShimuraGlue.Ray.reciprocityCanonical_of_rayClass L.rayClass, L.gonzalezRotger,
    L.gonzalezRotgerCount, L.deligneY3P, L.elkiesT⟩

/-- **Rows `r1r2`, `r1rec`, `r5`, `r5count`, `y3Connected`, `x6ConicModel` from `ShimuraGlueLeaves3`.** -/
theorem rows_of_shimuraGlueLeaves3 (L : ShimuraGlueLeaves3) :
    LeafAdopt.R1R2fpRep ∧ LeafQM.AV.R1rec ∧ LeafQM.AV.R5fp ∧ LeafQM.AV.R5fpCount ∧
      TSHecke.Y3Connected ∧ X6Kummer.X6ConicModel :=
  rows_of_shimuraGlueLeaves2 (shimuraGlueLeaves2_of_3 L)

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.rows_of_shimuraGlueLeaves3

example : HDec.QMSplit.Moduli.ShimuraGlueLeaves3 →
    HDec.LeafAdopt.R1R2fpRep ∧ _root_.LeafQM.AV.R1rec ∧ _root_.LeafQM.AV.R5fp ∧
      _root_.LeafQM.AV.R5fpCount ∧ HDec.TSHecke.Y3Connected ∧ HDec.X6Kummer.X6ConicModel :=
  HDec.QMSplit.Moduli.rows_of_shimuraGlueLeaves3

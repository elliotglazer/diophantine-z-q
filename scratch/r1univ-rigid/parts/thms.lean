
/-! ## §11 (4) Each leaf on `R1fpProps` from its abelian-scheme form and rigidity -/

namespace LeafQM.AV.R1UnivRigid

/-- Row H-142: `GonzalezRotgerX6` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem gonzalezRotgerX6_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.GonzalezRotgerX6 ↔ HDec.QMSplit.Moduli.GonzalezRotgerX6Ab := by
  unfold HDec.QMSplit.Moduli.GonzalezRotgerX6 HDec.QMSplit.Moduli.GonzalezRotgerX6Ab
  rw [r1fpProps_eq_ab hR]

/-- Row H-145: `GonzalezRotgerCountX6` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem gonzalezRotgerCountX6_iff_ab (hR : MumfordRigidity) : ShimuraSplit.GonzalezRotgerCountX6 ↔ ShimuraSplit.GonzalezRotgerCountX6Ab := by
  unfold ShimuraSplit.GonzalezRotgerCountX6 ShimuraSplit.GonzalezRotgerCountX6Ab
  rw [r1fpProps_eq_ab hR]

/-- Row H-149: `DeligneComponentsX6` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem deligneComponentsX6_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.DeligneComponentsX6 ↔ HDec.QMSplit.Moduli.DeligneComponentsX6Ab := by
  unfold HDec.QMSplit.Moduli.DeligneComponentsX6 HDec.QMSplit.Moduli.DeligneComponentsX6Ab
  rw [r1fpProps_eq_ab hR]

/-- Row H-151: `BabaGranathX6'` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem babaGranathX6_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.BabaGranathX6' ↔ HDec.QMSplit.Moduli.BabaGranathX6'Ab := by
  unfold HDec.QMSplit.Moduli.BabaGranathX6' HDec.QMSplit.Moduli.BabaGranathX6'Ab
  rw [r1fpProps_eq_ab hR]

/-- Row H-152: `ReciprocityCanonical` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem reciprocityCanonical_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.ReciprocityCanonical ↔ HDec.QMSplit.Moduli.ReciprocityCanonicalAb := by
  unfold HDec.QMSplit.Moduli.ReciprocityCanonical HDec.QMSplit.Moduli.ReciprocityCanonicalAb
  rw [r1fpProps_eq_ab hR]

/-- Row H-153: `ElkiesConicX6` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem elkiesConicX6_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.ElkiesConicX6 ↔ HDec.QMSplit.Moduli.ElkiesConicX6Ab := by
  unfold HDec.QMSplit.Moduli.ElkiesConicX6 HDec.QMSplit.Moduli.ElkiesConicX6Ab
  rw [r1fpProps_eq_ab hR]

/-- Row H-154: `ShimuraHolFamily` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem shimuraHolFamily_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.ShimuraHolFamily ↔ HDec.QMSplit.Moduli.ShimuraHolFamilyAb := by
  unfold HDec.QMSplit.Moduli.ShimuraHolFamily HDec.QMSplit.Moduli.ShimuraHolFamilyAb
  rw [r1fpProps_eq_ab hR]

/-- Row H-155: `DeligneComponentsY3` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem deligneComponentsY3_iff_ab (hR : MumfordRigidity) : ShimuraSplit.DeligneComponentsY3 ↔ ShimuraSplit.DeligneComponentsY3Ab := by
  unfold ShimuraSplit.DeligneComponentsY3 ShimuraSplit.DeligneComponentsY3Ab
  rw [r1fpProps_eq_ab hR]

/-- Row shimura-glue: `DeligneComponentsY3Printed` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem deligneComponentsY3Printed_iff_ab (hR : MumfordRigidity) : ShimuraGlue.DeligneComponentsY3Printed ↔ ShimuraGlue.DeligneComponentsY3PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsY3Printed ShimuraGlue.DeligneComponentsY3PrintedAb
  rw [r1fpProps_eq_ab hR]

/-- Row shimura-glue: `DeligneComponentsX6Printed` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem deligneComponentsX6Printed_iff_ab (hR : MumfordRigidity) : ShimuraGlue.DeligneComponentsX6Printed ↔ ShimuraGlue.DeligneComponentsX6PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsX6Printed ShimuraGlue.DeligneComponentsX6PrintedAb
  rw [r1fpProps_eq_ab hR]

/-- Row H-1 r1r2: `R1R2fpRep` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem r1R2fpRep_iff_ab (hR : MumfordRigidity) : HDec.LeafAdopt.R1R2fpRep ↔ HDec.LeafAdopt.R1R2fpRepAb := by
  unfold HDec.LeafAdopt.R1R2fpRep HDec.LeafAdopt.R1R2fpRepAb
  rw [r1fpProps_eq_ab hR]

/-- Row CanonicalModelY3: `CanonicalModelY3` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem canonicalModelY3_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.CanonicalModelY3 ↔ HDec.QMSplit.Moduli.CanonicalModelY3Ab := by
  unfold HDec.QMSplit.Moduli.CanonicalModelY3 HDec.QMSplit.Moduli.CanonicalModelY3Ab
  rw [r1fpProps_eq_ab hR]

/-- Row shimuraFamily H-139: `ShimuraFamily` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem shimuraFamily_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.ShimuraFamily ↔ HDec.QMSplit.Moduli.ShimuraFamilyAb := by
  unfold HDec.QMSplit.Moduli.ShimuraFamily HDec.QMSplit.Moduli.ShimuraFamilyAb
  rw [r1fpProps_eq_ab hR]

/-- Row y3Connected H-59: `Y3Connected` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem y3Connected_iff_ab (hR : MumfordRigidity) : HDec.TSHecke.Y3Connected ↔ HDec.TSHecke.Y3ConnectedAb := by
  unfold HDec.TSHecke.Y3Connected HDec.TSHecke.Y3ConnectedAb
  rw [r1fpProps_eq_ab hR]

/-- Row shimura-glue, replaces H-151: `BabaGranathRational` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem babaGranathRational_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.BabaGranathRational ↔ HDec.QMSplit.Moduli.BabaGranathRationalAb := by
  unfold HDec.QMSplit.Moduli.BabaGranathRational HDec.QMSplit.Moduli.BabaGranathRationalAb
  rw [r1fpProps_eq_ab hR]

/-- Row shimura-glue, replaces H-153: `ElkiesConicT` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem elkiesConicT_iff_ab (hR : MumfordRigidity) : HDec.QMSplit.Moduli.ElkiesConicT ↔ HDec.QMSplit.Moduli.ElkiesConicTAb := by
  unfold HDec.QMSplit.Moduli.ElkiesConicT HDec.QMSplit.Moduli.ElkiesConicTAb
  rw [r1fpProps_eq_ab hR]

end LeafQM.AV.R1UnivRigid

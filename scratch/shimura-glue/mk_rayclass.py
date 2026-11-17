"""Generate RayClass.lean = kernel/TC imports + shimura-split's `ReciprocityCanonical` (verbatim from
scratch/shimura-split/parts/RowsNew.lean) + parts/RayClassNew.lean."""
d='scratch/shimura-glue/'
s=open(d+'parts/RayClassNew.lean').read()
rows=open('scratch/shimura-split/parts/RowsNew.lean').read()
i=rows.index("/-- **LEAF-form (Shimura reciprocity at the three elliptic CM points")
j=rows.index("theorem r1rec_of_reciprocityCanonical")
hdr='''import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import Mathlib.NumberTheory.NumberField.Discriminant.Different

set_option linter.all false

noncomputable section

/-! ## shimura-split's `ReciprocityCanonical`, verbatim -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

'''+rows[i:j]+'''end HDec.QMSplit.Moduli

'''
open(d+'RayClass.lean','w').write(hdr+s)
print('ok')

"""Generate RowsGlue.lean = shimura-split Rows.lean (verbatim) + Adelic.lean body +
parts/DeligneNew.lean + parts/BundleNew.lean (imports merged). Rows.lean already contains
shimura-split's Y3Conn.lean and the definition DeligneComponentsX6."""
d='scratch/shimura-glue/'
def split(path):
    s=open(path).read()
    imports=[l for l in s.splitlines() if l.startswith('import ')]
    body='\n'.join(l for l in s.splitlines() if not l.startswith('import '))
    return imports, body
ir, br = split('scratch/shimura-split/Rows.lean')
ia, ba = split(d+'Adelic.lean')
_, bn = split(d+'parts/DeligneNew.lean')
_, bb = split(d+'parts/BundleNew.lean')
_, bp = split(d+'parts/MobiusProof.lean')
_, bm = split(d+'parts/MobiusNew.lean')
ir2, br2 = split(d+'parts/RayClassNew.lean')
_, b3 = split(d+'parts/Bundle3New.lean')
imports=[]
for l in ir+ia+['import ZInQKernel.HDecomp.QM.Polar','import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine','import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField','import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification','import Mathlib.NumberTheory.NumberField.Discriminant.Different']:
    if l not in imports: imports.append(l)
out='\n'.join(imports)+'\n'+br+'\n\n/-! # shimura-glue Part A: Adelic.lean -/\n'+ba+'\n\n/-! # shimura-glue Part B: parts/DeligneNew.lean -/\n'+bn+'\n\n/-! # shimura-glue Part C: parts/BundleNew.lean -/\n'+bb+'\n\n/-! # shimura-glue Part D: parts/MobiusProof.lean -/\n'+bp+'\n\n/-! # shimura-glue Part E: parts/MobiusNew.lean -/\n'+bm+'\n\n/-! # shimura-glue Part F: parts/RayClassNew.lean -/\n'+br2+'\n\n/-! # shimura-glue Part G: parts/Bundle3New.lean -/\n'+b3+'\n'
open(d+'RowsGlue.lean','w').write(out)
print('ok', out.count('\n'))

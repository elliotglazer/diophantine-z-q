"""Generate Mobius.lean = kernel import QM.Leaves + parts/MobiusProof.lean (the proof of MobiusCompose)."""
d='scratch/shimura-glue/'
body=open(d+'parts/MobiusProof.lean').read()
hdr='import ZInQKernel.HDecomp.QM.Leaves\nimport Mathlib.Topology.Compactification.OnePoint.ProjectiveLine\n\nset_option linter.all false\n\nnoncomputable section\n\n'
open(d+'Mobius.lean','w').write(hdr+body)
print('ok')

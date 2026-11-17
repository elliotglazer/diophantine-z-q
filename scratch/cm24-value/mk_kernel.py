# Assemble CM24Kernel.lean: the same proof against the build's own statement
# (import ZInQKernel.OneProof.H.TailZ3, which defines HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24).
t1 = open('T1.lean').read(); t1 = t1[t1.index('namespace CM24'):]
alg = open('Alg.lean').read(); alg = alg[alg.index('namespace CM24Alg'):]
p3 = open('P3.lean').read()
hdr = '''import ZInQKernel.OneProof.H.TailZ3

/-! # cm24-value against the build: the field `igusaCMValue24` (type
`HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24`, `ZInQKernel/OneProof/H/TailZ3.lean` l.1093) proved.
Same proof as `CM24Value.lean` (which uses the verbatim qm-glue copy), here over the build's own definitions. -/

set_option linter.all false
open Complex Matrix
open scoped Real

noncomputable section

'''
open('CM24Kernel.lean', 'w').write(hdr + t1 + '\n' + alg + '\n' + p3)

# Assemble CM24Value.lean = verbatim copy of scratch/qm-glue/ThetaValue24.lean (l.1-447) + T1 body + P3 body.
import re
src = open('../qm-glue/ThetaValue24.lean').read().split('\n')
copy = '\n'.join(src[:447])
t1 = open('T1.lean').read()
t1 = t1[t1.index('namespace CM24'):]
p3 = open('P3.lean').read()
alg = open('Alg.lean').read()
alg = alg[alg.index('namespace CM24Alg'):]
hdr = '''
/-! # cm24-value: the copy above is `scratch/qm-glue/ThetaValue24.lean` l.1-447, verbatim.
Below: the exact evaluation (namespace `CM24`). -/

open scoped Real

'''
open('CM24Value.lean', 'w').write(copy + '\n' + hdr + t1 + '\n' + alg + '\n' + p3)

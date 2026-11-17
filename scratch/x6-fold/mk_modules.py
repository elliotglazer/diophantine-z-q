"""Split scratch/x6-fold/x6body.lean (mk_tail.py) into ZInQKernel/OneProof/H/TailZ20.lean and TailZ21.lean."""
B = open('scratch/x6-fold/x6body.lean').read().split('\n')
imports = [l for l in open('scratch/x6-glue/X6Glue.lean').read().split('\n')
           if l.startswith('import ') and not l.endswith('TailK')]
a = B.index('/-! # shimura-glue Part A: Adelic.lean -/')
b = B.index('/-! # shimura-glue Part D: parts/MobiusProof.lean -/')
assert not any(l.startswith(('theorem', 'def', 'lemma', 'instance', 'abbrev', 'structure', 'noncomputable def'))
               for l in B[a:b] if not l.startswith('instance `'))
H20 = '''/-! # OneProof H, x6-fold (1/3): x6-glue's proof of `r1r2` and `x6ConicModel`, the part the chain lacks

x6-glue (docs/research/x6-glue.md) proves `HDec.QMSplit.Moduli.r1r2_of_published` and `x6ConicModel_of_published` in
`scratch/x6-glue/X6Glue.lean`, which is shimura-glue's `RowsGlue.lean` verbatim (itself shimura-split's `Rows.lean`
with qm-glue's coarse comparison, coarse-factor's `Discharge.lean` and curve-split's `CurveBij.lean`) followed by
x6-glue's four parts. This module and `TailZ21` are that file with every declaration the chain already has removed
(same name and same type in `TailU`, `TailR`, `TailZ8`, `TailZ12`; those are used), with every declaration not needed
by the two theorems removed, and with twelve verbatim copies of `TailR`'s `CurveSplit` lemmas replaced by an `open`
(`scratch/x6-fold/mk_tail.py`, `mk_modules.py`). Nothing else is changed. This module: qm-glue's coarse comparison,
coarse-factor's `FactorThroughSurj`, shimura-split's Bridge, BG and PairsLift parts and its additions over the chain.
`TailZ21`: shimura-glue's Möbius and ray-class parts and x6-glue's parts. -/

'''
H21 = '''/-! # OneProof H, x6-fold (2/3): shimura-glue's Möbius and ray-class glue, x6-glue's Elkies charts and the two rows

The second half of x6-glue's `X6Glue.lean` as trimmed by `scratch/x6-fold/mk_tail.py` (see `TailZ20`): shimura-glue's
`MobiusProof`, `MobiusNew` and `RayClassNew` parts, and x6-glue's `EvalAffine` (`K`-points of an affine open as ring
homs), `Charts` (`ElkiesCharts`), `ConicProof` (`conicModelT_of_charts`) and `X6New` (`ElkiesEquationsX6`,
`r1r2_of_published`, `x6ConicModel_of_published`). shimura-glue's Parts A-C (`Adelic`, `DeligneNew`, `BundleNew`) are
in `TailZ12`. -/

set_option linter.all false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

'''
p20 = ['import ZInQKernel.OneProof.H.TailZ19'] + imports + [''] + H20.split('\n') + B[:a]
p21 = ['import ZInQKernel.OneProof.H.TailZ20', ''] + H21.split('\n') + B[b:]
for name, p in (('TailZ20', p20), ('TailZ21', p21)):
    s = '\n'.join(p).rstrip('\n') + '\n'
    open(f'ZInQKernel/OneProof/H/{name}.lean', 'w').write(s)
    print(name, len(s.encode()))

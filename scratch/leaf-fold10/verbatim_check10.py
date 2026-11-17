#!/usr/bin/env python3
"""leaf-fold10: each copied module contains its source after the source's import lines as one block, with only the
listed lines dropped; the source's imports are among the module's (run from the repository root)."""
def check(src_path, mod_path, drop, first_import_replaced=None):
    src = open(src_path).read().split('\n')
    n = 0
    while src[n].startswith('import '):
        n += 1
    imps = src[:n]
    body = [l for l in src[n:] if not drop(l)]
    dropped = [l for l in src[n:] if drop(l)]
    body = '\n'.join(body).rstrip() + '\n'
    mod = open(mod_path).read()
    mimps = [l for l in mod.split('\n') if l.startswith('import ')]
    need = [l for l in imps if l != first_import_replaced]
    print(f'{mod_path} <- {src_path}')
    print('  imports of the module:', mimps)
    print('  source imports present (except the replaced one):', all(l in mimps for l in need),
          '; replaced:', first_import_replaced)
    print('  source body is a suffix block of the module:', mod.endswith(body))
    print('  dropped lines:', len(dropped), sorted(set(l.split()[0] + ' ' + l.split()[1] for l in dropped)))

check('scratch/dimjac-glue/DimJacGlue.lean', 'ZInQKernel/OneProof/H/TailZ10.lean',
      lambda l: l.startswith('#print axioms ModularSplit.DimJac.')
      or l == 'example : ZInQ.Contrib.CurvesG.DimJacobianEqGenus := ModularSplit.DimJac.dimJacobianEqGenus')
check('scratch/shimura-glue/Deligne.lean', 'ZInQKernel/OneProof/H/TailZ12.lean',
      lambda l: l.startswith('#print axioms'))
check('scratch/reduct-glue/Body.lean', 'ZInQKernel/OneProof/H/TailZ14.lean',
      lambda l: l.startswith('#print axioms'), first_import_replaced='import ReductSplitBase')

# reduct-glue's Base.lean (its Body's `ReductSplitBase`) is leaf-fold9's TailZ7 minus `#print` lines
b = open('scratch/reduct-glue/Base.lean').read().split('\n')
n = 0
while b[n].startswith('import '):
    n += 1
bb = '\n'.join(l for l in b[n:] if not l.startswith('#print')).rstrip() + '\n'
t7 = open('ZInQKernel/OneProof/H/TailZ7.lean').read()
print('reduct-glue Base.lean minus imports and #print lines is a suffix block of TailZ7:', t7.endswith(bb))
print('  same imports:', [l for l in b[:n]] == [l for l in t7.split('\n') if l.startswith('import ')])

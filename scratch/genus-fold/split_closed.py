"""Split scratch/genus-route/Closed.lean into ZInQKernel/OneProof/Genus/{DimJac,GenusBound,LocalDer}.lean.

Verbatim except: namespaces renamed (DimJacGlue -> GenusFold.DimJacGlue, ModularSplit.DimJac ->
GenusFold.DimJac, GenusRoute -> GenusFold) so that the root names do not clash with leaf-fold10's copy of
dimjac-glue in H/TailZ10.lean (root namespaces DimJacGlue, ModularSplit.DimJac); `#print` lines dropped;
each module gets the file-level header (imports, linter options, the outer `noncomputable section` and
`open CategoryTheory AlgebraicGeometry` of Closed.lean's line 49-50) it needs to stand alone.
Run from the repository root: python3 scratch/genus-fold/split_closed.py"""
import re
src = open('scratch/genus-route/Closed.lean').read().split('\n')
L = lambda a, b: src[a - 1:b]  # 1-indexed inclusive
imports = [l for l in src[:12] if l.startswith('import ')]
assert len(imports) == 10
def ren(lines):
    out = []
    for l in lines:
        if l.startswith('#print'):
            continue
        l = l.replace('ModularSplit.DimJac', 'GenusFold.DimJac')
        l = re.sub(r'(?<![.\w])DimJacGlue', 'GenusFold.DimJacGlue', l)
        l = l.replace('GenusRoute', 'GenusFold')
        out.append(l)
    return out
opts = ['set_option linter.style.longLine false', 'set_option linter.style.haveILetI false',
        'set_option linter.unusedSectionVars false']
assert L(46, 50) == opts + ['noncomputable section', 'open CategoryTheory AlgebraicGeometry']
assert src[687 - 1].startswith('example : ZInQ.Contrib.CurvesG.DimJacobianEqGenus')
assert src[2459 - 1] == 'end GenusRoute'
assert src[3472 - 1] == 'end'
note = lambda what: ['', f'/-! (genus-fold) {what} -/', '']
dimjac = imports + ren(L(11, 687)) + ['']
gb = imports + ['import ZInQKernel.OneProof.Genus.DimJac'] + note(
    'Part 2 of `scratch/genus-route/Closed.lean` (its lines 688-2459): the constant-field theorem and '
    'curve-split\'s genus bound. Namespace `GenusRoute` renamed `GenusFold`.') + opts + [
    'noncomputable section', 'open CategoryTheory AlgebraicGeometry'] + ren(L(688, 2459)) + ['']
ld = imports + ['import ZInQKernel.OneProof.Genus.GenusBound'] + note(
    'Part 3 of `scratch/genus-route/Closed.lean` (its lines 2460-end): the elementary genus bound, '
    '`localDerivation` and `dimJ1Le`. Namespace `GenusRoute` renamed `GenusFold`.') + opts + [
    'noncomputable section', 'open CategoryTheory AlgebraicGeometry', 'noncomputable section'] + ren(L(2460, len(src)))
hdr = ['/-! (genus-fold) Part 1 of `scratch/genus-route/Closed.lean` (its lines 1-687): dimjac-glue\'s proof of '
       '`ZInQ.Contrib.CurvesG.DimJacobianEqGenus`. Namespaces `DimJacGlue`, `ModularSplit.DimJac` renamed '
       '`GenusFold.DimJacGlue`, `GenusFold.DimJac` (leaf-fold10 has a root-namespace copy in H/TailZ10). -/', '']
dimjac = dimjac[:10] + [''] + hdr + dimjac[10:]
for name, lines in [('DimJac', dimjac), ('GenusBound', gb), ('LocalDer', ld)]:
    txt = '\n'.join(lines).rstrip('\n') + '\n'
    open(f'ZInQKernel/OneProof/Genus/{name}.lean', 'w').write(txt)
    print(name, len(txt.encode()), 'bytes')

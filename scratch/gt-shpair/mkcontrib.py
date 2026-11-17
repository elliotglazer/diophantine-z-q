#!/usr/bin/env python3
"""Assemble ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean from the scratch parts
GTCA1, GTCA2, GTCA3, GTFinal (namespace GTSHPair renamed GapSHPair)."""
import re
D = 'scratch/gt-shpair/'
parts = ['GTCA1', 'GTCA2', 'GTCA3', 'GTFinal']
header = '''import ZInQKernel.OneProof.H.TailZ14
import Mathlib

/-!
# `ReductGlue.StrictHenselizationPair` from one Néron leaf (task gt-shpair)

The hypothesis `ReductGlue.StrictHenselizationPair` (`ZInQKernel/OneProof/H/TailZ14.lean`, a GLUE
field rated composite) combines (i) strict henselization along a finite extension of DVRs with
(ii) Néron models commuting with strict henselization. This file proves (i) in Lean from Mathlib,
for every field (any characteristic) and every residue field (perfect or not), and isolates (ii) as
the single printed-form leaf `GapSHPair.NeronBaseChangeStrictHenselization` (BLR, *Néron models*,
§1.2 Prop. 2; a specialization of the chain's `ReductGlue.NeronBaseChangeUnramifiedDVR`).

Main results:
* `GapSHPair.strictHenselizationPair_of_neron :
    NeronBaseChangeStrictHenselization → ReductGlue.StrictHenselizationPair`;
* `GapSHPair.strictHenselizationPair_of_unramified :
    ReductGlue.NeronBaseChangeUnramifiedDVR → ReductGlue.StrictHenselizationPair`;
* `GapSHPair.shPair` (the commutative algebra, no hypotheses).

Construction: for `w` a valuation ring of `Ω = K̄'` over `O'`, the inertia field of `w` over `K`
(the union of the inertia fields of the finite Galois subextensions) and over `K'`. The finite
level (`key_finite`) uses Mathlib's fundamental identity and `Stab/Inertia ≃ Aut(κ(P)/κ(p))` with a
separable-degree count in place of `card_inertia_eq_ramificationIdxIn` (which needs separable
residue fields); the nesting `E_{K'} ⊆ E_K(K')` in characteristic `p` uses a `p`-power argument.
Adapted from task sh-route's characteristic-0 proof (`scratch/sh-route/CA*.lean`).
-/
'''
header += '''
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
'''
out = [header]
for p in parts:
    s = open(D + p + '.lean').read()
    s = '\n'.join(l for l in s.split('\n') if not l.startswith('import '))
    s = re.sub(r'^#print axioms.*$', '', s, flags=re.M)
    s = s.replace('GTSHPair', 'GapSHPair')
    out.append('\n-- ===== part ' + p + ' =====\n' + s)
open('ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean', 'w').write('\n'.join(out))

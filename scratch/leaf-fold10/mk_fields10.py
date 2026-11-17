#!/usr/bin/env python3
"""leaf-fold10: the field table of the new bundles (run from the repository root).

Reads leaf-fold9's `scratch/leaf-fold9/fields9.tsv`, drops the fields leaf-fold10 removes, adds the fields it adds,
writes `scratch/leaf-fold10/fields10.tsv` and the markdown tables `fields10_tables.md`, and prints the counts after
each fold."""
import csv

SRC = 'scratch/leaf-fold9/fields9.tsv'
D = 'scratch/leaf-fold10/'

REMOVED = {
    '(1) dimjac-glue (`dimJacobianEqGenus` proved, no hypotheses)': [('T', 'dimJacobianEqGenus')],
}
import sys
SHIMURA = 'shimura' in sys.argv[1:]
if SHIMURA:
    REMOVED['(2) shimura-glue (`y3Connected` from the printed Deligne leaf on `Y3`)'] = [('A', 'y3Connected')]
ADDED = {k: [] for k in REMOVED}
if SHIMURA:
    ADDED['(2) shimura-glue (`y3Connected` from the printed Deligne leaf on `Y3`)'] = [
        ('A', 'deligneComponentsY3Printed', '_root_.ShimuraGlue.DeligneComponentsY3Printed',
         'published form (specialization)',
         'Deligne, Sem. Bourbaki 389 (1971) Thm 2.4 and 3; PSPM 33 (1979) 2.1.3, 2.6.3; Milne 2005 Thms 5.17, 13.6 '
         '(UNVERIFIED): pi0(Y x_Q Qbar) = Q_{>0}^x \\ A_f^x / nrd(K3) with sigma acting by the cyclotomic idele to a '
         'fixed sign, for G = B^x, B = (2,-3|Q), at level K3, on one fine witness Y3 (with the R1fp clause list and '
         'Lemma QP, as for r1r2); over Mathlib\'s FiniteAdeleRing, QuaternionAlgebra, cyclotomicCharacter, '
         'ConnectedComponents', 'shimura-glue; folded by leaf-fold10', 'y3Connected (composite)'),
    ]
REDUCT = 'reduct' in sys.argv[1:]
K6 = '(2) reduct-glue (`r6` from `RaynaudSemistable`)'
K13 = '(2) reduct-glue (`semistableReductionThm`, `semistablePersists` from `SemistablePersistsDVR`, `NeronLocalizesDVR`)'
if REDUCT:
    REMOVED[K6] = [('R', 'r6')]
    REMOVED[K13] = [('R', 'semistableReductionThm'), ('R', 'semistablePersists')]
    ADDED[K6] = [('R', 'raynaudSemistable', '_root_.ReductSplit.RaynaudSemistable',
                  'published form (pending the base review)',
                  'SGA 7 I Exp. IX Prop. 4.7 (Raynaud\'s criterion; Silverberg-Zarhin 1995) over a DVR: m >= 3 invertible '
                  'in O and A[m] rational over K imply semistable reduction at O (the print may be over a strictly '
                  'henselian base: reduct-glue proves this leaf from RaynaudSemistableSH with StrictHenselizationNeron)',
                  'reduct-split, reduct-glue; folded by leaf-fold10',
                  'r6 (consequence), with semistableUnipotent, neronSchemeModelExistsDVR, mumfordTorsionAlgClosed and '
                  'mulEtaleAbelianScheme (FixedTorsionRationalImperfect proved)')]
    ADDED[K13] = [
        ('R', 'semistablePersistsDVR', '_root_.ReductSplit.SemistablePersistsDVR',
         'published form (specialization; pending the base review)',
         'SGA 7 I Exp. IX 3.3, first assertion, over a DVR, K\'/K finite (the print allows any extension of DVRs; '
         'it may be over a strictly henselian base: reduct-glue proves it from SemistablePersistsSH with '
         'StrictHenselizationPair)', 'reduct-split, reduct-glue; folded by leaf-fold10',
         'semistablePersists (consequence) and, with semistableReductionDVR, semistableReductionThm (consequence)'),
        ('R', 'neronLocalizesDVR', '_root_.ReductGlue.NeronLocalizesDVR', 'consequence of one theorem',
         'BLR, Neron models, 1.2 Prop. 4 ("only if": a Neron model over O_L localizes to a Neron model at the closed '
         'points), stated over every DVR of a number field L (every one is a localization: proved by reduct-glue)',
         'reduct-glue; folded by leaf-fold10',
         'SemistableLocalGlobal (reduct-split glue, now proved), for semistableReductionThm and semistablePersists'),
    ]
ORDER = list(REMOVED)
BUNDLES = [('R', 'OpenResearchLeaves10' if 'reduct' in sys.argv[1:] else 'OpenResearchLeaves9'), ('T', 'OpenTextbookLeaves10'),
           ('A', 'OpenAddedLeaves9' if SHIMURA else 'OpenAddedLeaves8'),
           ('G', 'OpenGlue7')]
KEYS = ['bundle', 'field', 'type', 'form', 'source', 'task', 'replaces']


def kind(form):
    if form.startswith('published form'):
        return 'LEAF'
    return {'consequence of one theorem': 'GLUE (c)', 'composite': 'GLUE (comp)', 'project glue': 'GLUE (pg)'}[form]


def counts(rows):
    c = {'pub': 0, 'c': 0, 'comp': 0, 'pg': 0}
    for r in rows:
        f = r['form']
        c['pub' if f.startswith('published form') else {'consequence of one theorem': 'c', 'composite': 'comp',
                                                          'project glue': 'pg'}[f]] += 1
    n = len(rows)
    return n, c, (c['pub'], n - c['pub']), (c['pub'] + c['c'], c['comp'] + c['pg'])


with open(SRC) as f:
    rd = csv.reader(f, delimiter='\t')
    hdr = next(rd)
    rows = [dict(zip(KEYS, r)) for r in rd]

# The task: keep reduct-split's four DVR leaves marked "published form pending the base review".
PENDING = {'serreTateThm2', 'semistableReductionDVR', 'semistableUnipotent', 'neronSchemeModelExistsDVR'}
for r in rows:
    if r['bundle'] == 'R' and r['field'] in PENDING:
        f = r['form']
        assert f.startswith('published form'), r
        r['form'] = (f[:-1] + '; pending the base review)') if f.endswith(')') else f + ' (pending the base review)'
assert sum(r['field'] in PENDING for r in rows) == 4

table = [('leaf-fold9 (`sixContactMin_of_open9`)', counts(rows))]
for step in ORDER:
    rem = set(REMOVED[step])
    assert all(any((r['bundle'], r['field']) == x for r in rows) for x in rem), step
    rows = [r for r in rows if (r['bundle'], r['field']) not in rem]
    for a in ADDED[step]:
        rows.append(dict(zip(KEYS, a)))
    table.append((step, counts(rows)))

with open(D + 'fields10.tsv', 'w') as f:
    f.write('\t'.join(hdr) + '\n')
    for b, _ in BUNDLES:
        for r in rows:
            if r['bundle'] == b:
                f.write('\t'.join(r[k] for k in KEYS) + '\n')

out = []
for b, name in BUNDLES:
    rs = [r for r in rows if r['bundle'] == b]
    out.append(f'### {name} ({len(rs)} field{"s" if len(rs) != 1 else ""})\n')
    out.append('| field | Lean type | strict kind | form | source | last task | replaces |')
    out.append('|---|---|---|---|---|---|---|')
    for r in rs:
        out.append(f"| `{r['field']}` | `{r['type']}` | {kind(r['form'])} | {r['form']} | {r['source']} | "
                   f"{r['task']} | {r['replaces']} |")
    out.append('')
open(D + 'fields10_tables.md', 'w').write('\n'.join(out))

print('| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |')
print('|---|---|---|---|---|---|---|---|')
for name, (n, c, s, l) in table:
    print(f"| {name} | {n} | {c['pub']} | {c['c']} | {c['comp']} | {c['pg']} | {s[0]} / {s[1]} | {l[0]} / {l[1]} |")

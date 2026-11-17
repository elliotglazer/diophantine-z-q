"""One-time seed of docs/one-proof/kinds.tsv (task contrib-kit, 2026-11-14).

Starts from leaf-fold10's table (scratch/leaf-fold10/fields10.tsv, frozenTarget at leaf-fold10) and applies
every change since, each listed below with its source: the prune, leaf-fold11 (genus-fold, route-a-fold),
leaf-fold12 (cm24-value, c-to-printed), and the strict counting convention (reduct-glue review v2; the
lead's rulings of 2026-11-14). From now on kinds.tsv is the source of truth: edit it, not this script.

Run from the repository root: python3 scripts/one_proof/seed_kinds.py
"""
import csv, subprocess

src = subprocess.run(['git', 'show', 'b5ff0474:scratch/leaf-fold10/fields10.tsv'],
                     capture_output=True, text=True, check=True).stdout.splitlines()
rows = list(csv.reader(src, delimiter='\t'))[1:]
BUNDLE = {'R': 'research', 'T': 'textbook', 'A': 'added', 'G': 'glue'}

def kind_of(form):
    f = form.lower()
    if f.startswith('published form'): return 'published'
    if f.startswith('consequence'): return 'consequence'
    if f.startswith('composite'): return 'composite'
    if 'glue' in f: return 'project glue'
    raise ValueError(form)

out = {}
for b, field, ty, form, source, task, _ in rows:
    flag = ''
    if 'pending the base review' in form: flag = 'pending reading: base'
    out[field] = dict(bundle=BUNDLE[b], field=field, type=ty, kind=kind_of(form), flag=flag,
                      form=form, source=source, rated_by=f'leaf-fold10 table ({task})')

def drop(f, why):
    del out[f]

# the prune (w62): unused hypotheses
for f in ['r3', 'serreTateThm2', 't10']: drop(f, 'prune')
# leaf-fold11 genus-fold: genus-route proves dim J1(N) <= N^2
drop('genusX1Field', 'genus-fold')
# leaf-fold11 route-a-fold: four fields restated on abelian schemes (kinds unchanged), one leaf added
for old in ['r1r2', 'shimuraFamily', 'gonzalezRotgerCountX6', 'deligneComponentsY3Printed']:
    r = out.pop(old); r['field'] = old + 'Ab'; r['type'] += 'Ab'
    r['rated_by'] += '; restated on abelian schemes by route-a-fold'
    out[r['field']] = r
out['mumfordRigidityCore'] = dict(bundle='research', field='mumfordRigidityCore',
    type='LeafQM.AV.R1UnivRigid.MumfordRigidityCore', kind='published', flag='', form='published form',
    source='Mumford, Geometric Invariant Theory, Thm 6.14 and Cor. 6.4 (numbers UNVERIFIED)',
    rated_by='route-a-fold')
# leaf-fold12: cm24-value proves igusaCMValue24; c-to-printed proves three fields from six printed leaves
drop('igusaCMValue24', 'cm24-value')
for f in ['neronLocalizesDVR', 'faltingsLemma5BC', 'semistableNeronBaseChange']: drop(f, 'c-to-printed')
for f, ty, kind, flag, src in [
    ('blr_1_2_4', 'CToPrinted.BLR_1_2_4', 'consequence', 'pending reading: may be printed in the strictly henselian form',
     'Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 4 (locator UNVERIFIED)'),
    ('faltingsLemma5Printed', 'CToPrinted.FaltingsLemma5Printed', 'published', 'unread',
     'Faltings 1983, Lemma 5 (locator UNVERIFIED; not read)'),
    ('raynaudKernelBound', 'CToPrinted.RaynaudKernelBound', 'published', '',
     "Raynaud's bound on the kernel term in Faltings' Lemma 5 (number UNVERIFIED)"),
    ('sga3_VIB_3_10', 'CToPrinted.SGA3_VIB_3_10', 'published', '', 'SGA 3 VI_B 3.10 (number UNVERIFIED)'),
    ('sga7_IX_3_3', 'CToPrinted.SGA7_IX_3_3', 'consequence', 'pending reading: base',
     'SGA 7 IX 3.3 (may be stated over a strictly henselian trait; used at number-field DVRs)'),
    ('egaIV_8_10_5_openImm', 'CToPrinted.EGAIV_8_10_5_openImm', 'published', '', 'EGA IV 8.10.5 (locator UNVERIFIED)')]:
    out[f] = dict(bundle='research', field=f, type=ty, kind=kind, flag=flag, form='', source=src, rated_by='c-to-printed; strict convention')
# strict convention: a flagged plausible weaker reading counts GLUE (reduct-glue review v2, K2/K4/K6)
for f in ['raynaudSemistable', 'semistablePersistsDVR', 'semistableReductionDVR', 'semistableUnipotent']:
    r = out[f]; r['kind'] = 'consequence'; r['flag'] = 'pending reading: base (strictly henselian trait vs number-field DVR)'
    r['rated_by'] += '; reduct-glue review v2'
# reduct-glue review v2 (section 4) rates neronSchemeModelExistsDVR (a), published form: the base review is done
r = out['neronSchemeModelExistsDVR']; r['flag'] = ''; r['rated_by'] += '; reduct-glue review v2: (a)'
# the public headline uses the strictest flagged reading: gonzalezRotgerCountX6Ab as a composite (frontier r5 4.8)
out['gonzalezRotgerCountX6Ab']['flag'] = 'strictest reading: composite (frontier r5 4.8)'

def strict(r):
    return 'LEAF' if r['kind'] == 'published' and not r['flag'].startswith('pending') else 'GLUE'
def strictest(r):
    return 'GLUE' if r['flag'].startswith('strictest') else strict(r)

order = {'research': 0, 'textbook': 1, 'added': 2, 'glue': 3}
cols = ['bundle', 'field', 'kind', 'flag', 'strict', 'strictest', 'source', 'rated_by']
with open('docs/one-proof/kinds.tsv', 'w', newline='') as fh:
    w = csv.writer(fh, delimiter='\t', lineterminator='\n')
    w.writerow(cols)
    for r in sorted(out.values(), key=lambda r: (order[r['bundle']], r['field'].lower())):
        w.writerow([r['bundle'], r['field'], r['kind'], r['flag'], strict(r), strictest(r), r['source'], r['rated_by']])
n = len(out); L = sum(strict(r) == 'LEAF' for r in out.values()); Ls = sum(strictest(r) == 'LEAF' for r in out.values())
print(f'{n} fields; strict {L}/{n - L}; strictest {Ls}/{n - Ls}')

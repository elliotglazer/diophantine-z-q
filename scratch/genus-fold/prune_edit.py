"""genus-fold step 3: delete scratch/genus-fold/prune-set.txt's fields from every bundle generation, the
assignments into them, and the dead readers of scratch/genus-fold/dead-cascade.txt (with their
`#print axioms` lines). Deletions only. Run from the repository root; prints every deleted line."""
import re
H = 'ZInQKernel/OneProof/H/'
files = {}
def get(f):
    if f not in files:
        files[f] = open(H + f + '.lean').read().split('\n')
    return files[f]
deleted = []
def drop(f, idxs, why):
    ls = get(f)
    for i in sorted(idxs, reverse=True):
        deleted.append((f, i + 1, why, ls[i]))
        ls[i] = None
def find(f, pred, start=0, end=None):
    ls = get(f)
    hits = [i for i in range(start, end if end is not None else len(ls)) if ls[i] is not None and pred(ls[i])]
    return hits
def block_of_struct(f, header):
    """line range [a, b) of `structure NAME ... where` and its indented body."""
    ls = get(f)
    a = find(f, lambda l: l.startswith(header))
    assert len(a) == 1, (f, header, a)
    a = a[0]
    b = a + 1
    while b < len(ls) and (ls[b] is None or ls[b].startswith(' ') or ls[b] == '' and ls[b + 1].startswith('  ')):
        b += 1
    return a, b
def drop_field(f, struct, field):
    a, b = block_of_struct(f, f'structure {struct} ')
    ls = get(f)
    hits = find(f, lambda l: l.startswith(f'  {field} : '), a, b)
    assert len(hits) == 1, (f, struct, field, hits)
    i = hits[0]
    idx = [i]
    # field docstring directly above
    if ls[i - 1].rstrip().endswith('-/') and not ls[i - 1].lstrip().startswith('--'):
        j = i - 1
        while not ls[j].lstrip().startswith('/--'):
            j -= 1
        assert ls[j].startswith('  /--'), (f, j, ls[j])
        idx += list(range(j, i))
    drop(f, idx, f'field {struct}.{field}')
def drop_assign(f, decl_header, field, exact=None):
    """`  field := ...` (one line) inside the declaration starting with decl_header."""
    ls = get(f)
    a = find(f, lambda l: l.startswith(decl_header))
    assert len(a) == 1, (f, decl_header, a)
    a = a[0]
    b = a + 1
    while b < len(ls) and (ls[b] is None or ls[b].startswith(' ')):
        b += 1
    hits = find(f, lambda l: l.startswith(f'  {field} := '), a, b)
    assert len(hits) == 1, (f, decl_header, field, hits)
    if exact is not None:
        assert ls[hits[0]] == exact, ls[hits[0]]
    drop(f, hits, f'assignment {field} in {decl_header.split()[1]}')
def drop_decl(f, name):
    ls = get(f)
    hits = find(f, lambda l: re.match(rf'theorem {re.escape(name)}\b', l) is not None)
    assert len(hits) == 1, (f, name, hits)
    i = hits[0]
    j = i
    if ls[i - 1].rstrip().endswith('-/'):
        j = i - 1
        while not ls[j].startswith('/--'):
            j -= 1
    if ls[j - 1].startswith('open ') and ls[j - 1].rstrip().endswith(' in'):
        j -= 1
    k = i + 1
    while k < len(ls) and ls[k] is not None and ls[k].strip() != '':
        assert ls[k].startswith(' '), (f, name, k, ls[k])
        k += 1
    # one blank line after the declaration goes too
    if k < len(ls) and ls[k] == '':
        k += 1
    drop(f, range(j, k), f'dead reader {name}')
    pr = find(f, lambda l: l.strip() == f'#print axioms HSyn.{name}')
    assert len(pr) == 1, (f, name, pr)
    drop(f, pr, f'#print of dead reader {name}')

# fields (prune-set.txt)
drop_field('LPrefix', 'TextbookLeaves', 't34')
drop_field('TailE', 'OpenTextbookLeaves2', 't34')
drop_field('TailI', 'OpenTextbookLeaves3', 't34')
drop_field('TailK', 'OpenTextbookLeaves4', 't34')
drop_field('TailO', 'OpenTextbookLeaves6', 'genusX1Field')
drop_field('TailX', 'OpenTextbookLeaves7', 'genusX1Field')
drop_field('TailZ4', 'OpenTextbookLeaves8', 'genusX1Field')
drop_field('TailZ9', 'OpenTextbookLeaves9', 'genusX1Field')
drop_field('TailZ11', 'OpenTextbookLeaves10', 'genusX1Field')
# assignments into removed fields
drop_assign('LPrefix', 'theorem textbookLeaves_of_open ', 't34', '  t34 := t.t34')
drop_assign('TailE', 'theorem textbookLeaves_of_open2 ', 't34', '  t34 := t.t34')
drop_assign('TailI', 'theorem textbookLeaves2_of_open3 ', 't34', '  t34 := t.t34')
drop_assign('TailK', 'theorem textbookLeaves3_of_open4 ', 't34', '  t34 := t.t34')
drop_assign('TailN', 'theorem textbookLeaves4_of_open5 ', 't34', '  t34 := t34_of_split5 t.dimJacobianEqGenus t.genusX1Field')
drop_assign('TailO', 'theorem textbookLeaves4_of_open6 ', 't34', '  t34 := t34_of_split5 t.dimJacobianEqGenus t.genusX1Field')
drop_assign('TailX', 'theorem textbookLeaves6_of_open7 ', 'genusX1Field', '  genusX1Field := t.genusX1Field')
drop_assign('TailZ4', 'theorem textbookLeaves7_of_open8 ', 'genusX1Field', '  genusX1Field := t.genusX1Field')
drop_assign('TailZ9', 'theorem textbookLeaves8_of_open9 ', 'genusX1Field', '  genusX1Field := t.genusX1Field')
drop_assign('TailZ11', 'theorem textbookLeaves9_of_open10 ', 'genusX1Field', '  genusX1Field := t.genusX1Field')
# the inline OpenTextbookLeaves6 literal in sixContactMin_of_open6_poincare (TailO)
ls = get('TailO')
s = ' genusX1Field := t.genusX1Field,'
hits = find('TailO', lambda l: s in l)
assert len(hits) == 1
i = hits[0]
deleted.append(('TailO', i + 1, 'inline assignment genusX1Field in sixContactMin_of_open6_poincare', s))
ls[i] = ls[i].replace(s, '')
# dead readers (dead-cascade.txt, generated casesOn/recOn excluded)
for f, n in [('LPrefix', 'modCurveLeaves_of_bundles'), ('LPrefix', 'glueOutputs_of_leaves'),
             ('LPrefix', 'sixContactMin_of_leaves'), ('LPrefix', 'sixContactMin_of_leaves_pin'),
             ('LPrefix', 'sixContactMin_of_open'), ('TailA', 'sixContactMin_of_leaves2')]:
    drop_decl(f, n)
for f, ls in files.items():
    open(H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')

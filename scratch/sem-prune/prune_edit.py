"""sem-prune step 2: delete scratch/sem-prune/prune-set-applied.txt's fields from every bundle generation, the
assignments into them, and the dead readers (scratch/sem-prune/dead-cascade.txt, generated casesOn/recOn
excluded; plus heightLeaves_of8/heightRows_of8, which read OpenResearchLeaves8.faltingsLemma5BC and leave the
closure once the r20 assignment goes), with their `#print axioms` lines and `example`s. Deletions only.
Adapted from genus-fold's prune_edit.py. Run from the repository root; prints every deleted line."""
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
    for i in sorted(set(idxs), reverse=True):
        assert ls[i] is not None, (f, i)
        deleted.append((f, i + 1, why, ls[i]))
        ls[i] = None
def find(f, pred, start=0, end=None):
    ls = get(f)
    return [i for i in range(start, end if end is not None else len(ls)) if ls[i] is not None and pred(ls[i])]
def doc_start(ls, i):
    """first line of the docstring directly above line i (i itself if none)."""
    if i == 0 or ls[i - 1] is None or not ls[i - 1].rstrip().endswith('-/'):
        return i
    j = i - 1
    while '/-' not in ls[j]:
        j -= 1
    return j if ls[j].lstrip().startswith('/--') else i
def block_of_struct(f, header):
    ls = get(f)
    a = find(f, lambda l: l.startswith(header))
    assert len(a) == 1, (f, header, a)
    a = a[0]
    b = a + 1
    while b < len(ls) and (ls[b] is None or ls[b].startswith(' ')):
        b += 1
    return a, b
def drop_field(f, struct, field):
    a, b = block_of_struct(f, f'structure {struct} ')
    ls = get(f)
    hits = find(f, lambda l: l.startswith(f'  {field} : '), a, b)
    assert len(hits) == 1, (f, struct, field, hits)
    i = hits[0]
    idx = [i]
    if ls[i - 1].rstrip().endswith('-/'):
        j = i - 1
        while '/-' not in ls[j]:
            j -= 1
        assert ls[j].startswith('  /--'), (f, j, ls[j])
        idx += list(range(j, i))
    drop(f, idx, f'field {struct}.{field}')
def drop_assign(f, decl_header, field, exact):
    ls = get(f)
    a = find(f, lambda l: l.startswith(decl_header))
    assert len(a) == 1, (f, decl_header, a)
    a = a[0]
    b = a + 1
    while b < len(ls) and (ls[b] is None or ls[b].startswith(' ')):
        b += 1
    hits = find(f, lambda l: l.startswith(f'  {field} := ') or l.startswith(f'    {field} := '), a, b)
    assert len(hits) == 1, (f, decl_header, field, hits)
    assert ls[hits[0]] == exact, (ls[hits[0]], exact)
    drop(f, hits, f'assignment {field} in {decl_header.split()[1]}')
def drop_decl(f, name):
    ls = get(f)
    hits = find(f, lambda l: re.match(rf'theorem (\S*\.)?{re.escape(name)}(\s|$)', l) is not None)
    assert len(hits) == 1, (f, name, hits)
    i = hits[0]
    j = doc_start(ls, i)
    if j > 0 and ls[j - 1] is not None and ls[j - 1].startswith('open ') and ls[j - 1].rstrip().endswith(' in'):
        j -= 1
    k = i + 1
    while k < len(ls) and ls[k] is not None and ls[k].strip() != '':
        assert ls[k].startswith(' '), (f, name, k, ls[k])
        k += 1
    if k < len(ls) and ls[k] == '':
        k += 1
    drop(f, range(j, k), f'dead reader {name}')
    short = name.split('.')[-1]
    pr = find(f, lambda l: l.startswith('#print axioms ') and l.split()[-1].split('.')[-1] == short)
    drop(f, pr, f'#print of dead reader {name}')
    # `example : ... := HDec.HSyn.NAME` blocks
    for e in find(f, lambda l: l.startswith('example ')):
        k = e
        while ls[k] is not None and ls[k].strip() != '':
            k += 1
        body = ' '.join(l for l in ls[e:k] if l is not None)
        if re.search(rf'\.{re.escape(short)}\s*$', body.strip()):
            end = k + 1 if k < len(ls) and ls[k] == '' else k
            drop(f, range(e, end), f'example of dead reader {name}')

# fields (prune-set-applied.txt)
for f, s, fl in [('LPrefix', 'TextbookLeaves', 't23'), ('TailD', 'ResearchLeaves3', 'r20'),
                 ('TailE', 'OpenResearchLeaves2', 'r20'), ('TailE', 'OpenTextbookLeaves2', 't23'),
                 ('TailI', 'OpenTextbookLeaves3', 't23'), ('TailK', 'OpenTextbookLeaves4', 't23'),
                 ('TailN', 'OpenResearchLeaves5', 'r20'), ('TailO', 'OpenTextbookLeaves6', 't23'),
                 ('TailX', 'OpenResearchLeaves7', 'r20'), ('TailX', 'OpenTextbookLeaves7', 'bdRInvariants'),
                 ('TailZ11', 'OpenTextbookLeaves10', 'bdRInvariants'),
                 ('TailZ23', 'OpenResearchLeaves14', 'raynaudKernelBound'),
                 ('TailZ4', 'OpenResearchLeaves8', 'faltingsLemma5BC'), ('TailZ4', 'OpenTextbookLeaves8', 'bdRInvariants'),
                 ('TailZ9', 'OpenResearchLeaves9', 'faltingsLemma5BC'), ('TailZ9', 'OpenTextbookLeaves9', 'bdRInvariants')]:
    drop_field(f, s, fl)
# assignments into removed fields
for f, h, fl, ex in [
        ('TailI', 'theorem textbookLeaves2_of_open3 ', 't23', '  t23 := t.t23'),
        ('TailD', 'theorem researchLeaves3_of ', 'r20', '    r20 := r.r20,'),
        ('TailK', 'theorem textbookLeaves3_of_open4 ', 't23', '  t23 := t.t23'),
        ('TailE', 'theorem researchLeaves3_of_open2 ', 'r20', '  r20 := r.r20'),
        ('TailE', 'theorem textbookLeaves_of_open2 ', 't23', '  t23 := t.t23'),
        ('TailN', 'theorem researchLeaves2_of_open5 ', 'r20', '  r20 := r.r20'),
        ('TailN', 'theorem textbookLeaves4_of_open5 ', 't23', '  t23 := t.t23'),
        ('LPrefix', 'theorem textbookLeaves_of_open ', 't23', '  t23 := t.t23'),
        ('TailX', 'theorem researchLeaves5_of_open7 ', 'r20', '  r20 := r.r20'),
        ('TailX', 'theorem textbookLeaves6_of_open7 ', 't23',
         '  t23 := HodgeLF7.t23 (_root_.ZInQ.Contrib.HodgeSplit.t23_all_of_bdrInvariants t.bdRInvariants)'),
        ('TailO', 'theorem textbookLeaves4_of_open6 ', 't23', '  t23 := t.t23'),
        ('TailZ4', 'theorem researchLeaves7_of_open8 ', 'r20', '  r20 := (heightRows_of8 r t).2.2.1'),
        ('TailZ4', 'theorem textbookLeaves7_of_open8 ', 'bdRInvariants', '  bdRInvariants := t.bdRInvariants'),
        ('TailZ11', 'theorem textbookLeaves9_of_open10 ', 'bdRInvariants', '  bdRInvariants := t.bdRInvariants'),
        ('TailZ23', 'theorem researchLeaves9_of_open14 ', 'faltingsLemma5BC',
         '  faltingsLemma5BC := _root_.CToPrinted.faltingsLemma5BC_of_printed r.faltingsLemma5Printed r.raynaudKernelBound'),
        ('TailZ15', 'theorem researchLeaves9_of_open10 ', 'faltingsLemma5BC', '  faltingsLemma5BC := r.faltingsLemma5BC'),
        ('TailZ9', 'theorem researchLeaves8_of_open9 ', 'faltingsLemma5BC', '  faltingsLemma5BC := r.faltingsLemma5BC'),
        ('TailZ9', 'theorem textbookLeaves8_of_open9 ', 'bdRInvariants', '  bdRInvariants := t.bdRInvariants')]:
    drop_assign(f, h, fl, ex)
# dead readers (dead-cascade.txt minus generated casesOn/recOn, plus the two TailZ4 readers)
for f, n in [('TailA', 'g8_g12_of_leaves'), ('TailA', 'newformG12Out_of_galois'), ('TailA', 'afterG7_of'),
             ('TailA', 'gluePieces_of_gluePieces2'), ('TailD', "sixContactMin_of_leaves3'"),
             ('TailD', 'sixContactMin_of_leaves3'), ('TailE', 'sixContactMin_of_open2'),
             ('TailF', 'HSyn.LinkedTate.afterG7_of_final'), ("TailF", "afterG7_of_linked'"),
             ('TailF', 'afterG7_of_linked'), ('TailI', 'sixContactMin_of_open3'), ('TailN', 'sixContactMin_of_open5'),
             ('TailO', 'sixContactMin_of_open6_poincare'), ('TailO', 'sixContactMin_of_openQ10'),
             ('TailO', 'sixContactMin_of_openQ9'), ('TailO', 'sixContactMin_of_openQ8'),
             ('TailO', 'sixContactMin_of_openQ7'), ('TailO', 'sixContactMin_of_openQ6'),
             ('TailO', 'sixContactMin_of_openQ5'), ('TailZ4', 'heightRows_of8'), ('TailZ4', 'heightLeaves_of8')]:
    drop_decl(f, n)
for f, ls in files.items():
    open(H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')

"""Trim scratch/x6-glue/X6Glue.lean to what the base chain (TailZ19) lacks and the fold needs.

Inputs (from Dump2.lean / Dump3.lean): scratch/x6-fold/x6dups.tsv (name, same|NEW against TailZ19),
scratch/x6-fold/x6edges.tsv (name, start, end, local constants used by type and value).
Kept: the local declarations reachable from ROOTS without passing through a declaration that the base already has
(same name and same type hash); plus, iteratively, any deleted declaration whose last name component occurs as a
word in the kept text (safety for simp/rw lists). Deleted: every other ranged declaration, every `example`, every
`#print`. Output: scratch/x6-fold/x6body.lean (the body without imports) and x6kept.tsv."""
import re, sys
D = 'scratch/x6-fold/'
src = open('scratch/x6-glue/X6Glue.lean').read().split('\n')
ROOTS = ['HDec.QMSplit.Moduli.r1r2_of_published', 'HDec.QMSplit.Moduli.x6ConicModel_of_published',
         'HDec.QMSplit.Moduli.X6Leaves', 'HDec.QMSplit.Moduli.x6Rows_of_leaves',
         'HDec.QMSplit.Moduli.ElkiesEquationsX6']
same = set(); 
for l in open(D + 'x6dups.tsv'):
    f = l.rstrip('\n').split('\t')
    if len(f) >= 2 and f[1] == 'same': same.add(f[0])
rng = {}; deps = {}
for l in open(D + 'x6edges.tsv'):
    f = l.rstrip('\n').split('\t')
    if len(f) < 4: continue
    n, a, b, ds = f[0], int(f[1]), int(f[2]), f[3]
    deps[n] = ds.split() if ds else []
    if a > 0: rng[n] = (a, b)
def prefixes(n):
    p = n.split('.')
    return ['.'.join(p[:i]) for i in range(1, len(p))]
def owner(n):
    # longest ranged prefix for unranged aux constants
    if n not in rng:
        cands = [q for q in prefixes(n) if q in rng]
        if not cands: return None
        n = cands[-1]
    # shortest ranged prefix whose range contains n's range (structure fields)
    a, b = rng[n]
    for q in prefixes(n):
        if q in rng and rng[q][0] <= a and b <= rng[q][1]: return q
    return n
top = {owner(n) for n in rng}
G = {}
for n, ds in deps.items():
    o = owner(n)
    if o is None: continue
    G.setdefault(o, set()).update(x for x in (owner(d) for d in ds) if x and x != o)
# coarse-factor's copies of curve-split lemmas (text identical after the docstring to TailR's CurveSplit.*)
ALIAS = ['SpecK', 'closure_mem_irreducibleComponents', 'isDomain_of_dim_one', 'stalk_closed_normal',
         'isReduced_of_smooth', 'components_disjoint', 'isOpen_irreducibleComponent', 'topDim_le_one',
         'isNormal_of_integral', 'isIntegrallyClosed_of_normal',
         'isLocalization_of_cofinal', 'bijective_of_finrank_eq_one']
same.update('CoarseFactorAG.' + a for a in ALIAS)
is_same = lambda o: o in same
kept = set(); todo = [owner(r) for r in ROOTS]
while todo:
    o = todo.pop()
    if o in kept or is_same(o): continue
    kept.add(o); todo.extend(G.get(o, ()))
def line_set(names):
    s = set()
    for o in names:
        a, b = rng[o]; s.update(range(a, b + 1))
    return s
# textual safety
while True:
    ktext = '\n'.join(src[i - 1] for i in sorted(line_set(kept)))
    add = set()
    for o in top - kept:
        if is_same(o): continue
        last = o.split('.')[-1]
        if len(last) >= 3 and re.search(r'(?<![\w.\'])' + re.escape(last) + r'(?![\w\'])', ktext):
            add.add(o)
    # closure of additions
    todo = list(add); new = False
    while todo:
        o = todo.pop()
        if o in kept or is_same(o): continue
        kept.add(o); new = True; todo.extend(G.get(o, ()))
    if not new: break
dele = set()
for o in top - kept:
    a, b = rng[o]
    dele.update(range(a, b + 1))
    j = a - 1
    while j >= 1 and re.match(r'^(set_option .* in|open .* in|@\[[^\]]*\])\s*$', src[j - 1]):
        dele.add(j); j -= 1
# examples and #print
i = 1
while i <= len(src):
    l = src[i - 1]
    if l.startswith('#print'): dele.add(i)
    if l.startswith('example'):
        k = i - 1
        if k >= 1 and src[k - 1].rstrip().endswith('-/'):
            m = k
            while m >= 1 and not src[m - 1].startswith('/--') and not src[m - 1].startswith('/-'): m -= 1
            if m >= 1 and src[m - 1].startswith('/--'): dele.update(range(m, k + 1))
        j = i
        dele.add(j); j += 1
        while j <= len(src) and src[j - 1].strip() and src[j - 1][0] in ' \t)': dele.add(j); j += 1
    i += 1
body = []
for k, l in enumerate(src, 1):
    if k in dele or l.startswith('import '): continue
    body.append(l)
    if l == 'namespace CoarseFactorAG':
        body += ['', '/-! x6-fold: twelve lemmas of coarse-factor that are verbatim copies of curve-split\'s (`TailR`) are',
                 'not repeated; the copies in `TailR` are used. -/',
                 'open _root_.CurveSplit (' + ' '.join(ALIAS) + ')']
# drop the emptied CurveSplit block (all of its declarations are in TailR)
i0 = next(i for i, l in enumerate(body) if l == 'namespace CurveSplit')
i0 = max(i for i in range(i0) if body[i] == 'open CategoryTheory AlgebraicGeometry Limits')
i1 = next(i for i in range(i0, len(body)) if body[i] == 'end CurveSplit')
i2 = next(i for i in range(i1 + 1, len(body)) if body[i].strip())
assert body[i2] == 'end', body[i2]
blk = body[i0:i2 + 1]
assert not any(re.match(r'^(theorem|lemma|def|noncomputable def|instance|abbrev|structure)\b', l) for l in blk)
body[i0:i2 + 1] = ['/-! x6-fold: curve-split\'s `CurveSplit` part of this file is in `TailR` (every declaration). -/']
# collapse runs of blank lines
out = []; blank = 0
for l in body:
    blank = blank + 1 if not l.strip() else 0
    if blank <= 1: out.append(l)
open(D + 'x6body.lean', 'w').write('\n'.join(out) + '\n')
with open(D + 'x6kept.tsv', 'w') as f:
    for o in sorted(kept, key=lambda o: rng[o][0]): f.write(f'{o}\t{rng[o][0]}\t{rng[o][1]}\n')
print('top', len(top), 'kept', len(kept), 'same', len([o for o in top if is_same(o)]), 'lines', len(out),
      'bytes', len('\n'.join(out)))

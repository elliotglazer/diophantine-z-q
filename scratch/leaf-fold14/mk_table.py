"""Section 2 of docs/research/leaf-fold14.md: one table per bundle from open-statements.json and kinds.tsv.
Run from the repository root: python3 scratch/leaf-fold14/mk_table.py > scratch/leaf-fold14/fields14.md"""
import csv, json
D = 'docs/one-proof/'
hyps = json.load(open(D + 'open-statements.json'))['hypotheses']
kinds = {r['field']: r for r in csv.DictReader(open(D + 'kinds.tsv'), delimiter='\t')}
NEW = {'raynaudSemistableSH', 'semistablePersistsSHcp', 'strictHenselizationPair', 'picRepresentableAbVar',
       'picZeroAbVar', 'phiAmpleIsogeny', 'weilPairingMumford'}
bundles = []
for h in hyps:
    if h['bundle'] != 'frozenTarget' and h['bundle'] not in bundles:
        bundles.append(h['bundle'])
for b in bundles:
    fs = [h for h in hyps if h['bundle'] == b]
    print(f'### {b} ({len(fs)} fields)\n')
    print('| field | Lean type | kind | strict | strictest | flag | new |')
    print('|---|---|---|---|---|---|---|')
    for h in fs:
        k = kinds[h['field']]
        print(f"| `{h['field']}` | `{h['type']}` | {k['kind']} | {k['strict']} | {k['strictest']} | "
              f"{k['flag'].replace('|', '/')} | {'**new**' if h['field'] in NEW else ''} |")
    print()

"""Assemble the four independent Gaussian audit patches against exact bytes."""
from pathlib import Path
import hashlib
import json
import re
import difflib

ROOT = Path(__file__).resolve().parent
BASE_SHA = '06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c'
raw = (ROOT / 'baseline.tex').read_bytes()
assert hashlib.sha256(raw).hexdigest() == BASE_SHA
base = raw.decode('utf-8')
lines = base.splitlines(keepends=True)
edits = []

def replace_lines(first, last, replacement, owner):
    start = sum(map(len, lines[:first - 1]))
    end = sum(map(len, lines[:last]))
    edits.append((start, end, replacement, owner, first, last))

def read_text(path):
    return path.read_text(encoding='utf-8')

replace_lines(16389, 16531, read_text(ROOT/'tail/replacement-tail.tex'), 'tail')
replace_lines(16533, 17940, read_text(ROOT/'weights/weights_fragment.tex'), 'weights')
replace_lines(17941, 18279, read_text(ROOT/'transference/replacement.tex'), 'transference')
spec = json.loads(read_text(ROOT/'patterns/edit-specs.json'))
for e in spec['edits']:
    if 'replacement_file' in e:
        replacement = read_text(ROOT/'patterns'/e['replacement_file'])
    else:
        old_line = ''.join(lines[e['baseline_start_line']-1:e['baseline_end_line']])
        assert old_line.count(e['old_text']) == 1
        replacement = old_line.replace(e['old_text'], e['new_text'])
    replace_lines(e['baseline_start_line'], e['baseline_end_line'], replacement, 'patterns')

old = 'Fix the coefficients, $M$, and the base modulus first. Choose one fixed\n$L$ so large that\n'
new = 'Fix the coefficients, $M$, and the base modulus first. Choose one fixed\n$L\\geq\\max(L_1,L_*)$ so large that\n'
assert base.count(old) == 1
start = base.index(old)
edits.append((start, start+len(old), new, 'root:explicit-final-cutoff', None, None))
edits.sort()
for a,b in zip(edits, edits[1:]):
    assert a[1] <= b[0], (a[3],b[3])
candidate = base
for start,end,replacement,*_ in reversed(edits):
    candidate = candidate[:start] + replacement + candidate[end:]

labels = lambda text: re.findall(r'\\label\{([^}]+)\}', text)
old_labels, new_labels = labels(base), labels(candidate)
assert set(old_labels) <= set(new_labels)
assert set(new_labels) - set(old_labels) == {'cor:ga-fixed-centered-nilsequence'}
assert len(new_labels) == len(set(new_labels))
assert candidate[:base.index('\\section{A fixed-field') if '\\section{A fixed-field' in base else edits[0][0]] == base[:base.index('\\section{A fixed-field') if '\\section{A fixed-field' in base else edits[0][0]]
output = ROOT/'quartic_962.tex'
output.write_bytes(candidate.encode('utf-8'))
receipt = {
    'baseline_sha256': BASE_SHA,
    'candidate': {'path': output.name, 'sha256': hashlib.sha256(output.read_bytes()).hexdigest(), 'bytes': output.stat().st_size},
    'edits': [{'owner': owner, 'baseline_lines': [first,last], 'start_character':start, 'end_character':end, 'replacement_sha256':hashlib.sha256(replacement.encode()).hexdigest()} for start,end,replacement,owner,first,last in edits],
    'checks': ['exact baseline hash', 'nonoverlapping edits', 'all prior labels retained', 'only one new corollary label', 'no duplicate labels', 'all bytes outside explicit edit ranges unchanged'],
    'scope': 'Gaussian appendix and Tao-Ziegler bibliography only; no change to polynomial constructions or final theorem statement',
}
(ROOT/'assembly.json').write_text(json.dumps(receipt, indent=2)+'\n',encoding='utf-8')
(ROOT/'changes.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True),candidate.splitlines(True),fromfile='baseline.tex',tofile='quartic_962.tex')),encoding='utf-8')
print(json.dumps(receipt['candidate']))

"""Compare the pinned English translation with the previously inspected arXiv PDF."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import unicodedata
from pypdf import PdfReader

HERE = Path(__file__).resolve().parent
ARXIV = HERE.parent / 'height/primary/yuan.pdf'
TRANSLATION = HERE / 'primary/yuan-author-translation.pdf'

def normalize(text):
    return re.sub(r'\s+', '', unicodedata.normalize('NFKC', text))

a = PdfReader(ARXIV)
b = PdfReader(TRANSLATION)
assert len(a.pages) == len(b.pages) == 32
diffs = []
different = []
character_changes = []
for i, (pa, pb) in enumerate(zip(a.pages, b.pages), 1):
    ta, tb = pa.extract_text(), pb.extract_text()
    if normalize(ta) != normalize(tb):
        different.append(i)
        diffs.append(f'PAGE {i}\n' + '\n'.join(difflib.unified_diff(
            ta.splitlines(), tb.splitlines(), fromfile='arxiv', tofile='translation')))
        x, y = normalize(ta), normalize(tb)
        character_changes.append({'page': i, 'changes': [
            [tag, x[l:r], y[s:t]] for tag,l,r,s,t in
            difflib.SequenceMatcher(None,x,y,autojunk=False).get_opcodes()
            if tag != 'equal']})
(HERE / 'translation-arxiv-diff.txt').write_text('\n\n'.join(diffs), encoding='utf8')
report = {
    'schema': 'yuan-translation-comparison/v1',
    'arxiv_sha256': hashlib.sha256(ARXIV.read_bytes()).hexdigest(),
    'translation_sha256': hashlib.sha256(TRANSLATION.read_bytes()).hexdigest(),
    'pages': 32,
    'normalization': 'Unicode NFKC and whitespace removal, using pypdf extraction',
    'different_pages': different,
    'character_changes': character_changes,
    'scope': 'Text extraction comparison only; not a comparison to the Chinese journal PDF.'
}
(HERE / 'translation-comparison.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf8')
print(json.dumps(report, indent=2))

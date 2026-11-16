from pathlib import Path
import hashlib
import json
import urllib.request
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent
DEST = ROOT / 'sources'
DEST.mkdir(exist_ok=True)
SOURCES = [
    ('kane-v5.pdf', 'https://arxiv.org/pdf/1009.1368v5',
     'Author arXiv v5 2012-11-05 of published IJNT 9 (2013), 1073-1111; final typeset bytes not compared'),
    ('kane-author.pdf', 'https://cseweb.ucsd.edu/~dakane/chebGold.pdf',
     'Author-hosted version of published IJNT 9 (2013), 1073-1111; final typeset bytes not compared'),
    ('kollar-author.pdf', 'https://arxiv.org/pdf/math/0005146',
     'Author arXiv v1 of published JIMJ 1 (2002), 467-476; final typeset bytes not compared'),
]
rows = []
for name, url, status in SOURCES:
    target = DEST / name
    try:
        if not target.exists():
            request = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(request, timeout=30) as response:
                raw = response.read()
            if not raw.startswith(b'%PDF'):
                raise ValueError('Response is not a PDF')
            target.write_bytes(raw)
        raw = target.read_bytes()
        reader = PdfReader(target)
        text = '\n\n'.join(f'PDF PAGE {i+1}\n{page.extract_text()}'
                           for i, page in enumerate(reader.pages))
        target.with_suffix('.txt').write_text(text, encoding='utf-8')
        rows.append(dict(file=name, url=url, version_status=status,
                         sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw),
                         pages=len(reader.pages)))
    except Exception as exc:
        rows.append(dict(file=name, url=url, error=str(exc)))
(DEST / 'SOURCES.json').write_text(json.dumps(rows, indent=2) + '\n', encoding='utf-8')
print(json.dumps(rows, indent=2))

from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
BASE = OUT.parent / 'baseline.tex'
expected = '06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c'
assert hashlib.sha256(BASE.read_bytes()).hexdigest() == expected
text = BASE.read_text(encoding='utf-8')
lines = text.splitlines(keepends=True)
fragment = ''.join(lines[16532:17940])
addition = (OUT / 'centered_nilsequence_discharge.tex').read_text(encoding='utf-8')
edits = [
    {
        'kind': 'stale-comment cleanup',
        'old': '% Working proof fragment, not integrated into a release.\n',
        'new': '',
    },
    {
        'kind': 'stale-comment cleanup',
        'old': '% Scope: these are mean-zero minor-arc estimates.  Progression main terms,\n% fixed-field Hecke Siegel--Walfisz, factorization and the final cube/counting\n% argument remain separately proved inputs; no integration is asserted here.\n',
        'new': '',
    },
    {
        'kind': 'explanatory addition; no changed mathematical hypothesis',
        'old': '% Replacement analytic bridge. It assumes the separately proved Gaussian\n% centered-nilsequence theorem, not any theorem of Frei--Tinkova.\n% Restrict prop:v5-artin-patterns to the fixed Gaussian ray fields used below.\n',
        'new': addition + '\n\n% The analytic bridge below uses the fixed-modulus centered nilsequence\n% estimate just proved for the Gaussian ray fields under consideration.\n',
    },
]
for edit in edits:
    assert fragment.count(edit['old']) == 1, edit['kind']
    fragment = fragment.replace(edit['old'], edit['new'])
(OUT / 'weights_fragment.tex').write_text(fragment, encoding='utf-8')
(OUT / 'edits.json').write_text(json.dumps({
    'baseline_sha256': expected,
    'owned_lines_inclusive': [16533, 17940],
    'changes_to_mathematical_claims_or_hypotheses': [],
    'edits': edits,
}, indent=2) + '\n', encoding='utf-8')
sources = [
    ('Mitsui1956', ROOT / 'work/frei-tinkova-removal-001/published-input-audit/mitsui1956.pdf', ['2-3', '11-12']),
    ('GTOrbits2012', ROOT / 'work/quartic-version5-release/sun-proof/sources/GT-orbits-published.pdf', ['476', '480', '490', '501-502', 'Appendix A']),
    ('moebius', ROOT / 'work/quartic-version5-release/sun-proof/sources/GT-mobius-published.pdf', ['545-547']),
]
(OUT / 'source_pins.json').write_text(json.dumps([
    {'citation_key': key, 'path': str(path.relative_to(ROOT)),
     'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
     'printed_pages_checked': pages}
    for key, path, pages in sources
], indent=2) + '\n', encoding='utf-8')
harness = r'''\documentclass{article}
\usepackage{amsmath,amssymb,amsthm}
\newtheorem{corollary}{Corollary}
\newcommand{\Q}{\mathbb Q}
\begin{document}
''' + addition + '\n\\end{document}\n'
(OUT / 'check_discharge.tex').write_text(harness, encoding='utf-8')
print(json.dumps({'baseline_verified': True, 'edits': len(edits),
                  'fragment_lines': len(fragment.splitlines()),
                  'fragment_sha256': hashlib.sha256(fragment.encode()).hexdigest()}))

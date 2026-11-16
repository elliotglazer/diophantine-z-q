from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
WORK = ROOT.parent
bridge = ROOT / 'gowers-bridge/bridge.tex'
contexts = [ROOT / p for p in ['factorization/factorization.tex', 'factorization/affine_pullback.tex', 'progression_mainterms.tex']]
contexts += [WORK / 'quartic-version5-release/sun-proof/sun_appendix.tex']
labels = set()
for path in [bridge] + contexts:
    labels.update(re.findall(r'\\label\{([^}]+)\}', path.read_text(encoding='utf-8')))
refs = set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', bridge.read_text(encoding='utf-8')))
def entry(path):
    return {'path': str(path.relative_to(WORK)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
sources = [WORK / ('quartic-version5-release/sun-proof/sources/' + name) for name in ['DK-v4.pdf', 'TZ-published.pdf', 'Bienvenu-published.pdf']]
report = {
    'status': 'accepted_source_interface_review',
    'date': '2026-11-06',
    'review': 'REVIEW.md',
    'bridge': entry(bridge),
    'contexts': [entry(path) for path in contexts],
    'localSources': [entry(path) for path in sources],
    'remoteSource': {'url': 'https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf', 'version': 'published PDF, directly inspected via web', 'locators': ['Proposition 6.4, pp.1780-1781', 'Proposition 7.1, pp.1781-1782', 'Appendix D construction, pp.1839-1842'], 'binaryHash': None},
    'bridgeReferences': sorted(refs),
    'unresolvedBridgeReferences': sorted(refs-labels),
    'sourceQualification': 'DK checked against arXiv v4 pp.12-13; no publisher-typeset comparison. GT source was viewed remotely, not cached or binary-hashed.',
    'compilation': 'not claimed',
    'upstreamArithmeticAudit': 'separate receipts; this review checks exact consumption interface, not a fresh proof of those inputs',
}
assert report['bridge']['sha256'] == 'b9284d40889c3d4308fd0c3d532b7d59c792f22894acc6db21c19a2422c307cd'
assert not report['unresolvedBridgeReferences']
(HERE / 'receipt.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'status': report['status'], 'bridge': report['bridge'], 'unresolved': report['unresolvedBridgeReferences']}, indent=2))

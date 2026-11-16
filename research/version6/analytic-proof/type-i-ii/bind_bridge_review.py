"""Bind this independent mathematical review to the agreed author snapshot."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
EXPECTED='b9284d40889c3d4308fd0c3d532b7d59c792f22894acc6db21c19a2422c307cd'
def entry(p):
    return {'path':str(p.relative_to(ROOT)),
            'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
target=entry(ROOT/'gowers-bridge/bridge.tex')
assert target['sha256']==EXPECTED,target
receipt={
 'schema':'gaussian-gowers-bridge-independent-review-v1',
 'status':'accepted mathematical implication, conditional on separately established centered-nilsequence input and cited published transference theorems',
 'reviewer':'elimination / Type I-II worker, independent of bridge author',
 'target':target,
 'review':entry(HERE/'bridge-independent-review.md'),
 'checked':['fixed-modulus to slow auxiliary-cutoff diagonal',
   'physical thresholds for inner scale N/V_z',
   'majorant U^(2s) norm and 4^s forms',
   'truncation and positive domination rescaling',
   'uniform normalized affine offsets and convex regions',
   'integer-bijective full-box normal-form extension',
   'bounded admissibility mass rather than V_z^d amplification',
   'genuine o_N fixed-system replacement before appendix local-factor errors',
   'centered cube algebra and q-divisor O(1/log v) bound',
   'cumulative boundary-strip tests for arbitrary T=o(sqrt N)',
   'weighted L2 localization from full-group polynomial moments to intervals'],
 'authorCorrectionsVerified':['choose majorant tolerance cutoff before size threshold',
   'explicit physical inner-scale diagonal',
   'explicit normal-form bijection, including active single-form direction',
   'cumulative fixed-epsilon boundary tests instead of imposing stage rate on T',
   'source-reviewer weighted-L2 boundary localization and two-limit errors'],
 'scope':'Fixed Gaussian ray fields, not arbitrary Galois extensions; no integration or publication authorized or performed by this review.',
 'remainingSeparateWork':['published-source and bibliography fidelity audit',
   'retain upstream Gaussian Hecke SW and factorization audits in final integration']}
(HERE/'BRIDGE_REVIEW_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

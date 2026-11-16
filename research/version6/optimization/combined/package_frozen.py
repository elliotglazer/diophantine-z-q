"""Collect the self-contained frozen artifact and record every file hash."""
from pathlib import Path
import hashlib
import json
import shutil

HERE=Path(__file__).resolve().parent
WORK=HERE.parent
BASE=WORK.parent/'quartic-version5-release/repository/quartics/quartic-1272'
OUT=HERE/'frozen'
def copy(src,dst):
    dst=OUT/dst
    dst.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(src,dst)
for name in ('build_source.cjs','raw-ir.json','raw-translated-ir.json','transformations.json','PROOF.md','reproduce.py','measured-census.json'):
    copy(HERE/name,name)
copy(HERE/'sources/diophantine_optimization_20261106_v3.tex','sources/diophantine_optimization_20261106_v3.tex')
copy(BASE/'compiler/compile_ir.py','compiler/compile_ir.py')
copy(BASE/'checker/checker.cjs','checker/checker.cjs')
copy(BASE/'builder/build_source.cjs','baseline/build_source.cjs')
copy(BASE/'MANIFEST.json','baseline/MANIFEST.json')

components={
 'detector-circuits':['patch_builder.py','patch_eval_blocks.py','patch_weight_factor.py','README.md','BLOCK_EVAL_PROOF.md','verification.json','combined-block-eval/verification.json','combined-weight-factor/verification.json','frozen-independent-check.json','other-workers-review.json','FROZEN_REVIEW.md','frozen-local-checks.json','verify_frozen_locals.py'],
 'dag-sharing':['log-replacement.cjs','point-replacement.cjs','REPORT.md','POINT_EQUIVALENCE.md','log-candidate/independent-check.json','point-candidate/algebra-check.json','verify-point.cjs','COMBINED_REVIEW.md','combined-integration-check.json','review-combined.cjs'],
 'field-quotients':['patch-certificate.json','EQUIVALENCE.md','identity-check.json','final-b/patch.json','final-b/PROOF.md','final-b/verification.json'],
 'source-compression':['build_variant.py','PROOF.md','verify_identities.py','identity-check.json','measured.json'],
 'elimination':['frozen-962-review.json','audit_frozen.py'],
}
for component,names in components.items():
    for name in names:
        src=WORK/component/name
        if src.exists(): copy(src,'evidence/'+component+'/'+name)
        else: print('pending optional evidence',src)
if (HERE/'reproduction-check/independent-check.json').exists():
    copy(HERE/'reproduction-check/independent-check.json','evidence/fresh-reproduction-check.json')
report=json.loads((OUT/'compiler-report.json').read_text())
readme='''# Frozen 962-coordinate quartic

This package specifies an integer polynomial of degree four with 962 active rational coordinates, including its unchanged input coordinate. Its rational zero projection equals the frozen 1,272-variable baseline. The separate claim that this projection equals the integers retains the baseline arithmetic qualifications, including the current Frei–Tinková input. This package is not a publication approval.

The polynomial has 55,409 monomials, primitive coefficient content one, and maximum coefficient magnitude 64*S², where S=3^(2^27) is a fixed integer coefficient. The raw system has 994 coordinates and 951 quadratic residuals. The compiler removes 32 coordinates, leaving 962 coordinates and 919 quadratic residuals. There are 961 existential witness coordinates in addition to the input.

`polynomial.json` is the complete coefficient table. `compiled-ir.json` and `reduction-certificate.json` provide the exact residual system and reversible elimination certificate. `PROOF.md` proves the rational witness maps for every change. The evidence directory records independent checks and component proofs. `MANIFEST.json` hashes every packaged file except itself.

Reproduce in a fresh temporary directory with Python 3 and Node:

    python reproduce.py --node /path/to/node

No nonstandard Python or Node library is needed. The script validates package integrity, regenerates both raw systems and the complete table, independently replays every gate and compiler operation, and compares seven deterministic artifacts byte for byte. S is never expanded into decimal digits.

The producer, compiler, checker, source text and evidence are bundled. No production repository or network access is needed. The baseline builder and manifest are included for comparison; their own relative source paths are historical and they are not run during reproduction.
'''
(OUT/'README.md').write_text(readme)
files={str(p.relative_to(OUT)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='MANIFEST.json' and '__pycache__' not in p.parts}
# Include the historical baseline manifest, which is distinct from this one.
files['baseline/MANIFEST.json']=hashlib.sha256((OUT/'baseline/MANIFEST.json').read_bytes()).hexdigest()
manifest={'schema':'quartic962-frozen-v1','status':'frozen; exact algebra and rational witness maps independently reviewed; inherited arithmetic qualifications persist','baselineManifestSha256':'aa7f04c54e8b778a419a1be8d24e0b3a9a8540c50202d41815864a156d6985c6','baselinePolynomialSha256':'02e4771ba6e6c2abc749e33e8440cc256939f48005d5102fba7d9853489c8586','claim':'same rational input projection as baseline; inherited arithmetic qualifications persist','counts':report['final'],'coefficientHeight':'64*S^2, S=3^(2^27)','files':files}
(OUT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'files':len(files),'manifestSha256':hashlib.sha256((OUT/'MANIFEST.json').read_bytes()).hexdigest(),'polynomialSha256':files['polynomial.json']}))

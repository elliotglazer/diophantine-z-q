"""Validate and reproduce the frozen 962-variable quartic without modifying it.

Use Python 3.10+ and Node.js 18+, with only their standard libraries.
After integration in scripts/, the package defaults to quartics/quartic-962/.
"""
from pathlib import Path, PurePosixPath
import argparse
from collections import Counter
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
PACKAGE_SHA = '36fca72cb0eb126193ffa43d890ff09d5e29cbf1274561d2632ed1e227163787'
POLYNOMIAL_SHA = '6b798de7d00ac3c7d725ca0a69d39f1eac1ddb02fee2756cb6323770b952af32'
BASELINE_SHA = '02e4771ba6e6c2abc749e33e8440cc256939f48005d5102fba7d9853489c8586'
BASELINE_MANIFEST_SHA = 'aa7f04c54e8b778a419a1be8d24e0b3a9a8540c50202d41815864a156d6985c6'
SOURCE_SHA = 'fc8bc7b8fae727e24f934ddd7de0a7cff8a005e89c3d0cac1ea14e5191b910ca'
STABLE = ['raw-ir.json', 'raw-translated-ir.json', 'compiled-ir.json',
          'reduction-certificate.json', 'coordinate-map.json', 'polynomial.json',
          'specialization-certificate.json']
REQUIRED_CHECKS = [
    'package_integrity', 'serialization_policy', 'baseline_source_bindings',
    'accepted_equivalence_evidence', 'compiler_selftest', 'build', 'compile_translated',
    'independent_certificate_check', 'emitted_quotient_semantics', 'point_chart_equivalence',
    'emitted_polynomial_circuits', 'anchor_equivalence', 'frozen_artifact_identity',
    'fixed_integer_statistics',
]
RESULT = {'variablesIncludingInput': 962, 'existentialWitnesses': 961, 'degree': 4,
          'monomials': 55409, 'quadraticResiduals': 919, 'primitiveContent': '1',
          'height': '64*3^(2^28)'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def insist(condition, message):
    if not condition:
        raise ValueError(message)


def package_integrity(package):
    insist(sha(package/'MANIFEST.json') == PACKAGE_SHA, 'Frozen 962 package manifest differs')
    manifest = read(package/'MANIFEST.json')
    insist(manifest['schema'] == 'quartic962-frozen-v1', 'Wrong frozen package schema')
    for name, expected in manifest['files'].items():
        rel = PurePosixPath(name)
        insist(not rel.is_absolute() and '..' not in rel.parts and '\\' not in name and ':' not in name,
                'Unsafe manifest path')
        target = package.joinpath(*rel.parts)
        insist(not target.is_symlink() and target.resolve().is_relative_to(package) and target.is_file(),
                'Missing or unsafe package file: '+name)
        insist(sha(target) == expected, 'Frozen package file differs: '+name)
    actual = {p.relative_to(package).as_posix() for p in package.rglob('*') if p.is_file()}
    insist(actual == set(manifest['files']) | {'MANIFEST.json'}, 'Frozen package inventory differs')
    insist(sha(package/'polynomial.json') == POLYNOMIAL_SHA, 'Frozen polynomial differs')
    return manifest


def serialization_policy(package):
    for name in STABLE:
        raw = (package/name).read_bytes()
        raw.decode('utf-8')
        if name == 'polynomial.json':
            remainder = raw.replace(b'\r\n', b'')
            valid = raw.endswith(b'\r\n') and b'\r' not in remainder and b'\n' not in remainder
        else:
            valid = raw.endswith(b'\n') and b'\r' not in raw
        insist(valid, 'Noncanonical line endings: '+name)


def baseline_source_bindings(package, manifest):
    insist(manifest['baselineManifestSha256'] == BASELINE_MANIFEST_SHA, 'Baseline manifest binding differs')
    insist(manifest['baselinePolynomialSha256'] == BASELINE_SHA, 'Baseline polynomial binding differs')
    insist(sha(package/'baseline/MANIFEST.json') == BASELINE_MANIFEST_SHA, 'Bundled baseline manifest differs')
    baseline = read(package/'baseline/MANIFEST.json')
    baseline_entries = {x['path']:x['sha256'] for x in baseline['files']}
    insist(baseline_entries['builder/build_source.cjs'] == sha(package/'baseline/build_source.cjs'),
            'Bundled baseline builder does not match its manifest')
    source = 'sources/diophantine_optimization_20261106_v3.tex'
    insist(sha(package/source) == SOURCE_SHA, 'Pinned mathematical source differs')
    for name in ['raw-ir.json', 'raw-translated-ir.json']:
        raw = read(package/name)
        insist(raw['source']['sha256'] == SOURCE_SHA and raw['source']['path'] == source,
                'Raw source binding differs')
        insist(raw['fixedParameter'] == {'name':'S', 'value':'3^(2^27)', 'coordinate':False},
                'Fixed parameter binding differs')


def accepted_equivalence_evidence(package):
    """Bind the already reviewed proofs; this does not turn prose into a machine proof."""
    raw_sha = sha(package/'raw-translated-ir.json')
    local = read(package/'evidence/detector-circuits/frozen-local-checks.json')
    insist(local['status'] == 'pass' and local['translated_sha256'] == raw_sha,
            'Local source-equivalence receipt is not bound to this raw program')
    integration = read(package/'evidence/dag-sharing/combined-integration-check.json')
    insist(integration['status'] == 'passed' and integration['rawSha256'] == raw_sha and
            integration['gateIdentities'] == 904 and integration['semanticAssertions'] == 136,
            'Combined source-equivalence receipt differs')
    elimination = read(package/'evidence/elimination/frozen-962-review.json')
    insist(elimination['verified'] is True and elimination['rawSha256'] == raw_sha and
            elimination['coordinates'] == 962 and elimination['unusedCoordinates'] == 0 and
            elimination['inputPreserved'] is True, 'Elimination receipt differs')
    full = read(package/'evidence/detector-circuits/frozen-independent-check.json')
    insist(full['status'] == 'passed_exact_algebra_checks' and full['inputSha256'] == raw_sha and
            full['artifactHashes']['quartic']['sha256'] == POLYNOMIAL_SHA,
            'Frozen independent coefficient receipt differs')
    return ['PROOF.md', 'evidence/dag-sharing/COMBINED_REVIEW.md',
            'evidence/detector-circuits/FROZEN_REVIEW.md',
            'evidence/dag-sharing/POINT_EQUIVALENCE.md',
            'evidence/field-quotients/EQUIVALENCE.md', 'evidence/field-quotients/final-b/PROOF.md',
            'evidence/source-compression/PROOF.md', 'evidence/detector-circuits/BLOCK_EVAL_PROOF.md']


def reproduce(package, output, node):
    start = time.monotonic()
    package, output = package.resolve(), output.resolve()
    insist(not output.is_relative_to(package), 'Output must be outside the frozen package')
    insist(not output.exists() or (output.is_dir() and not any(output.iterdir())),
            'Output must be a new or empty directory')
    insist(node is not None, 'Node.js 18+ is required')
    version = subprocess.check_output([node,'--version'],text=True).strip()
    insist(int(version.lstrip('v').split('.')[0]) >= 18, 'Node.js 18+ is required')
    checks=[]
    def record(name, operation):
        when=time.monotonic(); result=operation()
        checks.append({'name':name,'status':'PASS','seconds':round(time.monotonic()-when,3),'log':None})
        print(name+': PASS',flush=True)
        return result
    manifest=record('package_integrity',lambda:package_integrity(package))
    record('serialization_policy',lambda:serialization_policy(package))
    record('baseline_source_bindings',lambda:baseline_source_bindings(package,manifest))
    proof_files=record('accepted_equivalence_evidence',lambda:accepted_equivalence_evidence(package))
    output.mkdir(parents=True,exist_ok=True)
    work=output/'rebuild';work.mkdir();logs=output/'logs';logs.mkdir();reports=output/'reports';reports.mkdir()
    shutil.copyfile(package/'build_source.cjs',work/'build_source.cjs')
    shutil.copytree(package/'sources',work/'sources')
    def run(name,command):
        when=time.monotonic()
        process=subprocess.run([str(x)for x in command],cwd=work,stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace',
            env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        log=logs/(name+'.log');log.write_text(process.stdout,encoding='utf-8',newline='\n')
        insist(process.returncode==0,name+' failed; inspect '+str(log))
        checks.append({'name':name,'status':'PASS','seconds':round(time.monotonic()-when,3),
                       'log':'logs/'+log.name})
        print(name+': PASS',flush=True)
    run('compiler_selftest',[sys.executable,package/'compiler/compile_ir.py','--self-test'])
    run('build',[node,work/'build_source.cjs'])
    run('compile_translated',[sys.executable,package/'compiler/compile_ir.py',work/'raw-translated-ir.json',work])
    run('independent_certificate_check',[node,package/'checker/checker.cjs','--input',work/'raw-translated-ir.json',
        '--compiled',work/'compiled-ir.json','--certificate',work/'reduction-certificate.json',
        '--coordinate-map',work/'coordinate-map.json','--quartic',work/'polynomial.json',
        '--report',reports/'independent-check.json'])
    helper=HERE/'quartic962_checks.cjs'
    for name,mode,count in [('emitted_quotient_semantics','quotients',136),('point_chart_equivalence','points',135),
                            ('emitted_polynomial_circuits','circuits',659),('anchor_equivalence','anchor',957)]:
        run(name,[node,helper,mode,package,work,reports/(name+'.json')])
        local=read(reports/(name+'.json'))
        insist(local['status']=='PASS' and local['assertions']==count and
                local['rawSha256']==manifest['files']['raw-translated-ir.json'],
                'Local semantic coverage differs: '+name)
    def compare():
        serialization_policy(work)
        for name in STABLE:
            insist(sha(work/name)==manifest['files'][name], 'Rebuilt artifact differs byte for byte: '+name)
    record('frozen_artifact_identity',compare)
    def statistics():
        check=read(reports/'independent-check.json');stats=check['statistics']
        insist(check['coordinateCount']==962 and check['residualCount']==919 and
                check['gateIdentities']['checked']==904 and check['transformation']['operations']==894,
                'Checker counts differ')
        for key,value in {'degree':4,'activeCoordinateCount':962,'monomials':55409,
                          'primitiveContent':'1','integerCoefficients':True,'specializedSupportCertified':True}.items():
            insist(stats[key]==value,'Checker statistic differs: '+key)
        insist(stats['maximumAbsoluteCoefficient']['coefficient']==[{'sPower':2,'coefficient':'64/1'}],
                'Exact height differs')
        operations=Counter(x['kind']for x in read(work/'reduction-certificate.json')['operations'])
        insist(operations=={'eliminate':32,'normalize':862},'Compiler operation counts differ')
        poly=read(work/'polynomial.json')
        input_terms=[x for x in poly['terms']if x['monomial']==[0,0,0,0]]
        insist(input_terms==[{'monomial':[0,0,0,0],'sPower':0,'coefficient':'1'}],
                'Input fourth-power coefficient is not exactly one')
    record('fixed_integer_statistics',statistics)
    insist([x['name']for x in checks]==REQUIRED_CHECKS,'Check inventory differs')
    receipt={'schema':'quartic-962-reproduction-v1','status':'PASS','packageManifestSha256':PACKAGE_SHA,
        'frozenPolynomialSha256':POLYNOMIAL_SHA,'rebuiltPolynomialSha256':sha(work/'polynomial.json'),
        'byteIdentical':True,'result':RESULT,'checks':checks,'requiredChecks':REQUIRED_CHECKS,
        'baselinePolynomialSha256':BASELINE_SHA,'baselineManifestSha256':BASELINE_MANIFEST_SHA,
        'reviewedEquivalenceProofs':[{'path':name,'sha256':manifest['files'][name]}for name in proof_files],
        'validationTools':[{'path':name,'sha256':sha(HERE/name)}for name in ['check_quartic962.py','quartic962_checks.cjs']],
        'runtimes':{'python':sys.version.split()[0],'node':version},
        'elapsedSeconds':round(time.monotonic()-start,3),
        'scope':'Exact finite construction, emitted local identities and byte reproduction. Reviewed rational witness maps are pinned. External arithmetic inputs and the Version 6 manuscript arguments are not proved by this program.'}
    (output/'REPRODUCTION.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:receipt[k]for k in ['status','result','byteIdentical','elapsedSeconds']},indent=2))
    return receipt


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package',type=Path,default=HERE.parent/'quartics/quartic-962')
    parser.add_argument('--out',type=Path)
    parser.add_argument('--node',default=shutil.which('node'))
    args=parser.parse_args()
    if args.out:reproduce(args.package,args.out,args.node)
    else:
        with tempfile.TemporaryDirectory(prefix='quartic962-')as directory:
            reproduce(args.package,Path(directory),args.node)

"""Rebuild and independently verify the frozen 962-coordinate quartic."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args): subprocess.run([str(x) for x in args],check=True,stdout=subprocess.DEVNULL)

def reproduce(node,work):
    manifest=json.loads((HERE/'MANIFEST.json').read_text())
    for name,expected in manifest['files'].items():
        actual=sha(HERE/name)
        if actual!=expected: raise RuntimeError(f'Frozen file changed: {name}')
    work.mkdir(parents=True,exist_ok=True)
    shutil.copy2(HERE/'build_source.cjs',work/'build_source.cjs')
    shutil.copytree(HERE/'sources',work/'sources',dirs_exist_ok=True)
    run([node,work/'build_source.cjs'])
    run([sys.executable,HERE/'compiler/compile_ir.py',work/'raw-translated-ir.json',work/'compiled'])
    run([node,HERE/'checker/checker.cjs','--input',work/'raw-translated-ir.json',
         '--compiled',work/'compiled/compiled-ir.json','--certificate',work/'compiled/reduction-certificate.json',
         '--coordinate-map',work/'compiled/coordinate-map.json','--quartic',work/'compiled/polynomial.json',
         '--report',work/'independent-check.json'])
    comparisons={'raw-ir.json':work/'raw-ir.json','raw-translated-ir.json':work/'raw-translated-ir.json'}
    comparisons.update({name:work/'compiled'/name for name in ('compiled-ir.json','reduction-certificate.json','coordinate-map.json','polynomial.json','specialization-certificate.json')})
    for name,path in comparisons.items():
        if sha(path)!=manifest['files'][name]: raise RuntimeError(f'Rebuild differs: {name}')
    receipt=json.loads((work/'independent-check.json').read_text())
    report={'status':'passed','identical_artifacts':list(comparisons),'statistics':receipt['statistics'],'gate_identities':receipt['gateIdentities']['checked'],'compiler_operations':receipt['transformation']['operations']}
    print(json.dumps({k:v for k,v in report.items() if k!='statistics'}))
    print(json.dumps({k:report['statistics'][k] for k in ('degree','monomials','activeCoordinateCount','primitiveContent','maximumAbsoluteCoefficient')}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--node',default=shutil.which('node'))
    parser.add_argument('--work',type=Path)
    args=parser.parse_args()
    if not args.node: parser.error('Node is required; specify --node')
    if args.work: reproduce(args.node,args.work.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='quartic962-') as directory:
            reproduce(args.node,Path(directory))

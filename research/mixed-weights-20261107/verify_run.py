"""Replay a generated mixed-weight variant, including its ordinary quartic."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from verify_weights import verify as weights

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/combined-comparison'))
from verify_variants import check_chain, budgets
spec=importlib.util.spec_from_file_location('logs',ROOT/'research/v6-comparison/verify_identities.py')
logs=importlib.util.module_from_spec(spec);spec.loader.exec_module(logs)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('output',type=Path)
    ap.add_argument('--target-shift',type=int,choices=(1,2),required=True)
    a=ap.parse_args()
    d=a.output.resolve()/'precision40_quotients'
    for manifest in [HERE/'INPUTS.json',ROOT/'research/v6-comparison/INPUTS.json']:
        for path,sha in json.loads(manifest.read_text())['sha256'].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==sha,path
    load=lambda p:json.loads(p.read_text())
    raw=load(d/'parameter-source-ir.json')
    chain=check_chain(raw,load(d/'source-ir.json'),26)
    numerical=budgets()
    # The historical verifier also returns a handwritten old weight chain.
    # Consume only its actual emitted logarithm checks; use weights() below.
    logarithms=logs.verify(raw)['logarithmCircuits']
    weight_result=weights(raw)
    expected=load(HERE/'RESULTS.json')[str(a.target_shift)]
    ordinary=d/'compiled/ordinary-polynomial.json'
    assert hashlib.sha256(ordinary.read_bytes()).hexdigest()==expected['ordinaryExportSha256']
    table=load(ordinary)
    assert table['schema']=='ordinary-integer-quartic-v1' and table['fixedParameter'] is None
    assert all(isinstance(t['coefficient'],str) and str(int(t['coefficient']))==t['coefficient'] for t in table['terms'])
    assert max(abs(int(t['coefficient'])).bit_length() for t in table['terms'])==3247
    table['schema']='brox-sparse-polynomial-v1';table['fixedParameter']='S = 3^(2^27)'
    for t in table['terms']:t['sPower']=0
    with TemporaryDirectory() as tmp:
        p=Path(tmp)/'quartic.json';p.write_text(json.dumps(table))
        command=['node',str(ROOT/'quartics/quartic-962/checker/checker.cjs'),
            '--input',str(d/'source-ir.json'),'--compiled',str(d/'compiled/compiled-ir.json'),
            '--certificate',str(d/'compiled/reduction-certificate.json'),
            '--coordinate-map',str(d/'compiled/coordinate-map.json'),'--quartic',str(p)]
        checked=json.loads(subprocess.check_output(command,text=True))
    assert checked['coordinates']==expected['coordinates']
    assert checked['residuals']==expected['residuals']
    assert checked['monomials']==expected['ordinaryCoordinateMonomials']
    assert checked['degree']==4 and checked['content']=='1'
    files=['build_source.cjs','parameter-source-ir.json','source-ir.json',
           'compiled/compiled-ir.json','compiled/reduction-certificate.json',
           'compiled/coordinate-map.json','compiled/ordinary-polynomial.json']
    print(json.dumps({'targetShift':a.target_shift,'status':'passed',
        'algebraicChecker':checked,'chainCoordinates':chain,
        'arithmeticBudgets':numerical,'logarithmIdentities':logarithms,
        'weightIdentities':weight_result,
        'sha256':{f:hashlib.sha256((d/f).read_bytes()).hexdigest() for f in files},
        'reviewStatus':'Exact algebra and numerical checks; inherited number theory and new proof prose have AI self-review only'},indent=2))

if __name__=='__main__':main()

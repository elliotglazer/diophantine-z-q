"""Verify actual emitted split evaluations as exact polynomials in upstream symbols."""
import hashlib, importlib.util, json
from fractions import Fraction
from pathlib import Path
from patch_builder import BASE,HERE
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
o=module('oracle',BASE/'oracle/check_oracle.py');cmod=module('compiler',BASE/'compiler/compile_ir.py');P=o.Poly
where=HERE/'combined-block-eval';raw=where/'raw-ir.json';d=json.loads(raw.read_text())
env={c['id']:P.var('v'+str(c['id'])) for c in d['coordinates']}
def ev(terms):
    out=P(0)
    for t in terms:
        assert not t['sPower'];v=P(Fraction(t['coefficient']))
        for i in t['monomial']:v=v*env[i]
        out=out+v
    return out
def val(name):return ev(d['values'][name]['terms'])
co=[[P(1),P(0)]]+[[val(f'symmetric.1.co{k}.{j}') for j in [0,1]] for k in range(1,11)]
checks=[]
for i in range(9):
    name=f'detector{i}.E1';q=val(f'detector{i}.q1')
    gates=[g for g in d['gates'] if d['coordinates'][g['coordinateId']]['name'].startswith(name+'.')]
    assert len(gates)==8,(name,len(gates))
    for g in gates:
        assert g['operation']=='quadratic_assignment';env[g['coordinateId']]=ev(g['expression'])
        row=d['residuals'][g['definitionResidualId']]
        assert ev(row['terms'])==P(0)
    for j in [0,1]:
        want=sum((co[k][j]*q**k for k in range(11)),P(0));assert val(name+f'.{j}')==want
    checks.append({'detector':i,'gates':len(gates),'components_verified':2})
ct=cmod.Compiler(json.loads((where/'raw-translated-ir.json').read_text()));reduction=ct.reduce();ct.normalize()
cmod.write_json(where/'reduced-ir.json',ct.output());cmod.write_json(where/'reduction-certificate.json',ct.certificate)
out={'status':'pass','scope':'All18 actual emitted E1 output components equal sum(c_k*q^k) as exact polynomials with upstream symbols independent; all72 local residuals vanish identically.','evaluations':checks,'raw_coordinates':len(d['coordinates']),'compiled_coordinates':len(ct.coordinates),'compiled_residuals':len(ct.rows),'maximum_residual_degree':max(map(cmod.degree,ct.rows.values())),'reduction':reduction,'raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'patch_sha256':hashlib.sha256((HERE/'patch_eval_blocks.py').read_bytes()).hexdigest()}
(where/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

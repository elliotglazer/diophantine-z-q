"""Exact identities for each emitted common-factor weight circuit and census."""
import hashlib,importlib.util,json
from fractions import Fraction
from patch_builder import BASE,HERE
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
P=module('oracle',BASE/'oracle/check_oracle.py').Poly;cmod=module('compiler',BASE/'compiler/compile_ir.py')
where=HERE/'combined-weight-factor';raw=where/'raw-ir.json';d=json.loads(raw.read_text());env={c['id']:P.var('v'+str(c['id'])) for c in d['coordinates']}
def ev(terms):
    out=P(0)
    for t in terms:
        assert not t['sPower'];v=P(Fraction(t['coefficient']))
        for i in t['monomial']:v=v*env[i]
        out=out+v
    return out
def val(name):return ev(d['values'][name]['terms'])
for i in range(9):
    name=f'detector{i}';q,e6,e24,e96=[val(name+'.'+s) for s in ['q1','e6','e24','e96']]
    names={name+'.'+s+'.quadratic' for s in ['q1e6','q16','q52']}
    gates=[g for g in d['gates'] if d['coordinates'][g['coordinateId']]['name'] in names];assert len(gates)==3
    for g in gates:
        assert g['operation']=='quadratic_assignment';env[g['coordinateId']]=ev(g['expression']);assert ev(d['residuals'][g['definitionResidualId']]['terms'])==P(0)
    assert val(name+'.q16')==q*e6*e24
    assert val(name+'.q52')==q*e6*e96
c=cmod.Compiler(json.loads((where/'raw-translated-ir.json').read_text()));reduction=c.reduce();c.normalize();cmod.write_json(where/'reduced-ir.json',c.output());cmod.write_json(where/'reduction-certificate.json',c.certificate)
out={'status':'pass','actual_emitted_component_identities':18,'actual_emitted_gate_residuals':27,'raw_coordinates':len(d['coordinates']),'compiled_coordinates':len(c.coordinates),'compiled_residuals':len(c.rows),'maximum_residual_degree':max(map(cmod.degree,c.rows.values())),'reduction':reduction,'raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'patch_sha256':hashlib.sha256((HERE/'patch_weight_factor.py').read_bytes()).hexdigest()}
(where/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

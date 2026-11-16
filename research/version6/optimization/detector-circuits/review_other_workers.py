"""Independent exact check of actual emitted source-compression rows."""
import hashlib, importlib.util, json
from fractions import Fraction
from pathlib import Path
from patch_builder import BASE, HERE
ROOT=HERE.parent
spec=importlib.util.spec_from_file_location('oracle',BASE/'oracle/check_oracle.py');oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
P=oracle.Poly
directory=ROOT/'source-compression';data=json.loads((directory/'raw-ir.json').read_text())
env={c['id']:P.var('x'+str(c['id'])) for c in data['coordinates']}
def evaluate(terms):
    out=P(0)
    for term in terms:
        assert not term['sPower']
        value=P(Fraction(term['coefficient']))
        for v in term['monomial']:value=value*env[v]
        out=out+value
    return out
def alias(name):return evaluate(data['values'][name]['terms'])
coords={c['name']:c['id'] for c in data['coordinates']}
rows={r['name']:r for r in data['residuals']}
checked=[]
for name in [f'detector{i}' for i in range(9)]+['scalar']:
    # Upstream arithmetic is arbitrary here: all its coordinates remain independent symbols.
    b=alias(name+('.b' if name=='scalar' else '.Bsemantic'))
    C=17*b;z=env[coords[name+'.scaled_e']];p=env[coords[name+'.p']];s=env[coords[name+'.s']];q=env[coords[name+'.q']]
    U=alias('scalar.U') if name=='scalar' else b
    targets={name+'.'+suffix+'.quadratic' for suffix in ['p2','U2','Bh','s2','q2']}
    found=[]
    for gate in data['gates']:
        cname=data['coordinates'][gate['coordinateId']]['name']
        if cname in targets:
            assert gate['operation']=='quadratic_assignment'
            env[gate['coordinateId']]=evaluate(gate['expression']);found.append(cname)
    assert len(found)==5,(name,found)
    first=evaluate(rows[name+'.firstConic']['terms'])
    second=evaluate(rows[name+'.secondConic']['terms'])
    H=z*(C-U*U)
    assert first==C*p*p-(C-z)*(C+3*z),name+' first'
    assert second==C*q*q-(s*s-H)*(s*s+3*H),name+' second'
    checked.append(name)
chain=[env[coords['correction.partial.'+str(p)]] for p in [2,3,5,7,11,13,17,'sign']]
assert evaluate(rows['correction.initialSign']['terms'])==chain[0]**2-1
for j,p in enumerate([2,3,5,7,11,13,17],1):
    assert evaluate(rows[f'correction.partialProduct{j}']['terms'])==(chain[j]-chain[j-1])*(chain[j]-p*chain[j-1])
paths=[directory/'build_variant.py',directory/'build_source.cjs',directory/'raw-ir.json',directory/'PROOF.md',ROOT/'dag-sharing/log-replacement.cjs',ROOT/'dag-sharing/log-candidate/raw-translated-ir.json']
report={'status':'pass','scope':'Actual emitted pole gates expanded and all20 structural pole rows exactly equal canonical formulas; all8 emitted correction rows factor exactly. Independent coordinates used for upstream expressions.','poles':checked,'hashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
(HERE/'other-workers-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

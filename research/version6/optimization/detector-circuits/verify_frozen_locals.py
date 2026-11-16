"""Reuse exact local verifiers against the final frozen combined raw system."""
from pathlib import Path
import hashlib,json
from patch_builder import HERE

checks=[]
s=(HERE/'verify_eval_blocks.py').read_text()
s=s.replace("where=HERE/'combined-block-eval'", "where=HERE.parent/'combined'")
s=s[:s.index('ct=cmod.Compiler(')]
exec(compile(s,'verify_eval_blocks_on_frozen','exec'),{})
checks.append('18 emitted E1 components and72 local residuals')
s=(HERE/'verify_weight_factor.py').read_text()
s=s.replace("where=HERE/'combined-weight-factor'", "where=HERE.parent/'combined'")
s=s[:s.index('c=cmod.Compiler(')]
exec(compile(s,'verify_weight_factor_on_frozen','exec'),{})
checks.append('18 emitted q16/q52 identities and27 local residuals')
s=(HERE/'review_other_workers.py').read_text()
s=s.replace("directory=ROOT/'source-compression'", "directory=ROOT/'combined'")
s=s[:s.index('paths=[')]
exec(compile(s,'review_poles_on_frozen','exec'),{})
checks.append('20 emitted pole structural identities and8 exact correction factorizations')
import importlib.util
from fractions import Fraction
from patch_builder import BASE
spec=importlib.util.spec_from_file_location('baseline_oracle',BASE/'oracle/check_oracle.py');oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
P=oracle.Poly
data=json.loads((HERE.parent/'combined/raw-ir.json').read_text())
env={c['id']:P.var('x'+str(c['id'])) for c in data['coordinates']}
def evaluate(terms):
    out=P(0)
    for t in terms:
        assert not t['sPower'];p=P(Fraction(t['coefficient']))
        for i in t['monomial']:p=p*env[i]
        out=out+p
    return out
def field(name):return [evaluate(data['values'][name+'.'+str(j)]['terms']) for j in [0,1]]
def mul(a,b):return [a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0]]
coeff=[Fraction(1),Fraction(-2,5)]
for j in range(2,13):coeff.append(coeff[-1]*Fraction(4*j-5,4*j+1))
for side in ['U','V']:
    for i in range(5):
        prefix=side+str(i);name='log'+prefix;f=field(prefix+'.f');w=mul([P(11),P(-6)],mul(f,f))
        power=[P(1),P(0)];expect=[P(0),P(0)]
        for a in coeff[:4 if i==1 else 13]:
            expect=[expect[j]+a*power[j] for j in [0,1]];power=mul(power,w)
        gates=[g for g in data['gates'] if data['coordinates'][g['coordinateId']]['name'].startswith(name+'.')]
        for g in gates:
            if g['operation']=='quadratic_assignment':env[g['coordinateId']]=evaluate(g['expression'])
        if i:
            assert field(name)==mul(field(prefix+'.z'),expect)
        else:
            point='H' if side=='U' else 'V0';x=field(point+'.x');y=field(point+'.y');ell=field(name)
            lhs=mul(y,ell);rhs=mul(x,expect)
            qg=[g for g in gates if g['operation']=='field_quotient_component'];assert len(qg)==2
            for g in qg:
                j=g['component'];assert evaluate(data['residuals'][g['definitionResidualId']]['terms'])==lhs[j]+rhs[j]
checks.append('All10 frozen emitted log identities, including both denominator-fused residual pairs')
raw=HERE.parent/'combined/raw-ir.json';translated=HERE.parent/'combined/raw-translated-ir.json'
report={'status':'pass','checks':checks,'raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'translated_sha256':hashlib.sha256(translated.read_bytes()).hexdigest()}
(HERE/'frozen-local-checks.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

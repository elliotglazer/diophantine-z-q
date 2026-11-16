"""Read-only assembly replay and exact preservation checks."""
from pathlib import Path
import contextlib, hashlib, io, json, runpy, difflib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREP = HERE.parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
base = ROOT / 'work/quartic-version5-release/repository/quartic_1272.tex'
target = PREP / 'manuscript/quartic_962-analytic-candidate.tex'
old, new = base.read_text(encoding='utf-8'), target.read_text(encoding='utf-8')
new_without_lower = new.replace((PREP/'lower-bound/degree_lower_bound.tex').read_text(encoding='utf-8')+'\n\n','',1)
checks = []
def check(name, test):
    checks.append({'check':name,'passed':bool(test)})
    assert test, name
check('target requested hash', sha(target)=='b43f096ba3a4b1a979778ae1593ce3ad89048a2d28016e5ee9f35b124238dce7')
check('frozen V5 source hash',sha(base)=='16033e0471df605093b28210a9f81718c2486b147016ec8afc75d166dff0b90f')

captured = {}
write_text, mkdir = Path.write_text, Path.mkdir
def capture(self, data, *args, **kwargs):
    captured[self.resolve()] = data
    return len(data)
try:
    Path.write_text, Path.mkdir = capture, lambda *args,**kwargs:None
    for name in ['assemble_preparation.py','assemble_analytic_candidate.py']:
        with contextlib.redirect_stdout(io.StringIO()):
            runpy.run_path(str(PREP/name),run_name='__main__')
finally:
    Path.write_text, Path.mkdir = write_text, mkdir
for path,data in captured.items():
    if path.suffix=='.tex':
        check('read-only script replay: '+path.name, data==path.read_text(encoding='utf-8'))

def span(s,start,end):
    i=s.index(start)
    return s[i:s.index(end,i)]
for name,start,end in [
 ('original construction and arithmetic foundations','% End quartic introduction addition', '% Begin explicit quartic constructions'),
 ('4973 construction','% Begin explicit quartic constructions','% Begin Version 5 additions'),
 ('smaller-quartic arithmetic interfaces',r'\section{Arithmetic interfaces for the smaller quartic}',r'\section{The shared-point quartic'),
 ('retained shared-point source',r'\subsection{Points, local parameters, and quotient domains}',r'\subsection{Exact quadratic compilation and the complete table}'),
 ('downstream old arithmetic appendices',r'\section{Dependency order in the arithmetic argument}',r'\section{Simultaneous primes with coprime adjacent norms}')]:
    if name=='original construction and arithmetic foundations' and start not in old:
        continue
    if name=='retained shared-point source':
        check(name,span(old,start,end)==span(new,start,'% Replace the former exact-compilation subsection'))
    else:
        check(name,span(old,start,end)==span(new_without_lower,start,end))

A=ROOT/'work/frei-tinkova-removal-001'
for rel in ['quotient-audit/norm_transfer.tex','type-i-ii/type_i_ii.tex','factorization/affine_pullback.tex','factorization/factorization.tex','gowers-bridge/bridge.tex','published-input-audit/gaussian_hecke_sw.tex']:
    text=(A/rel).read_text(encoding='utf-8')
    text=text.replace('{GTMobius2012}','{moebius}').replace('{v6gtlinear}','{greentao}')
    if 'affine_pullback' in rel:
        text=text.replace(r'\Lambda_{b,W}',r'\lambda_{b,W}')
    check('exact transformed insertion: '+rel,new.count(text)==1)
for rel in ['quartic-962/construction.tex','lower-bound/degree_lower_bound.tex']:
    check('exact insertion: '+rel,new.count((PREP/rel).read_text(encoding='utf-8'))==1)
report=json.loads((PREP/'manuscript/ANALYTIC_CANDIDATE.json').read_text())
for row in report['inputs']:
    check('input hash: '+row['path'],sha(ROOT/row['path'])==row['sha256'])
F=ROOT/'work/quartic-sub1000-20261106/combined/frozen'
manifest=json.loads((F/'MANIFEST.json').read_text())
check('frozen manifest pin',sha(F/'MANIFEST.json')=='36fca72cb0eb126193ffa43d890ff09d5e29cbf1274561d2632ed1e227163787')
check('all frozen manifest file hashes',all(sha(F/p)==h for p,h in manifest['files'].items()))
check('baseline builder equals V5 builder',(F/'baseline/build_source.cjs').read_bytes()==(ROOT/'work/quartic-version5-release/repository/quartics/quartic-1272/builder/build_source.cjs').read_bytes())
counts=manifest['counts']
check('final counts',(counts['coordinates'],counts['residuals'],counts['ordinaryCoordinateMonomials'],counts['degree'])==(962,919,55409,4))
mapping=json.loads((F/'coordinate-map.json').read_text())['mapping']
check('input fixed and all 962 compact coordinates present',mapping[0]=={'sourceId':0,'compactId':0,'name':'input'} and sorted(r['compactId'] for r in mapping)==list(range(962)))
lower_review=json.loads((PREP/'lower-bound/independent-review/receipt.json').read_text())
check('lower-bound reviewed fragment hash',all(sha(ROOT/r['path'])==r['sha256'] for r in lower_review['files']))

diff=[]
for tag,i,j,k,l in difflib.SequenceMatcher(None,old.splitlines(),new.splitlines(),autojunk=False).get_opcodes():
    if tag!='equal':
        diff.append({'kind':tag,'V5_lines':[i+1,j],'candidate_lines':[k+1,l]})
result={'status':'passed','checks':checks,'changed_ranges':diff,'files':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for p in [base,target,PREP/'assemble_preparation.py',PREP/'assemble_analytic_candidate.py']]}
(HERE/'assembly-check.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))

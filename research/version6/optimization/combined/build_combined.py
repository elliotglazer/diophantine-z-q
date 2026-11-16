"""Compose the four independently documented circuit changes, with exact edits."""
from pathlib import Path
import hashlib
import importlib.util
import json
import shutil

HERE=Path(__file__).resolve().parent
WORK=HERE.parent
BASE=WORK.parent/'quartic-version5-release/repository/quartics/quartic-1272'
source=BASE/'builder/build_source.cjs'
text=source.read_text()
events=[]
def edit(old,new,name,count=1):
    global text
    assert text.count(old)==count,(name,text.count(old),count)
    text=text.replace(old,new)
    events.append({'name':name,'occurrences':count,'old':old,'new':new})

spec=importlib.util.spec_from_file_location('detector_patch',WORK/'detector-circuits/patch_builder.py')
det=importlib.util.module_from_spec(spec)
spec.loader.exec_module(det)
text=det.patch(text)
events.append({'name':'detector primary patch','source':'../detector-circuits/patch_builder.py::patch','optional_weights':False})

start=text.index('function log(name,p,e){')
end=text.index('const LU=',start)
edit(text[start:end],(WORK/'dag-sharing/log-replacement.cjs').read_text(),'DAG exact square-completion evaluator')

edit(" const B=scale(b,17), ee=assign(name+'.ePolynomial',mul(sub(one,p.e),add(one,scale(p.e,3))));\n residual(name+'.firstConic',sub(sq(p.p),mul(B,ee)));", " const B=scale(b,17), pp=rsq(name+'.p2',p.p);\n residual(name+'.firstConic',sub(mul(B,pp),mul(sub(B,p.e),add(B,scale(p.e,3)))));",'pole first conic rescaling')
edit("let h=rm(name+'.h',p.e,sub(B,rsq(name+'.U2',Up))),Bh=rm(name+'.Bh',B,h),ss=", "let Bh=rm(name+'.Bh',p.e,sub(B,rsq(name+'.U2',Up))),ss=",'pole direct scaled H')
edit("e:fresh('detector'+r+'.e','base')", "e:fresh('detector'+r+'.scaled_e','base')",'detector witness name')
edit("e:fresh('scalar.e','base')", "e:fresh('scalar.scaled_e','base')",'scalar witness name')
edit("let correction=sub(one,scale(booleans[7],2));for(let i=0;i<7;i++)correction=rm('correction.product'+i,correction,add(one,scale(booleans[i],[2,3,5,7,11,13,17][i]-1)));\nfor(let i=0;i<8;i++)residual('correction.boolean'+i,sub(sq(booleans[i]),booleans[i]));", "residual('correction.initialSign',sub(sq(booleans[0]),one));\nfor(let i=1;i<8;i++){const p=[2,3,5,7,11,13,17][i-1];residual('correction.partialProduct'+i,add(sq(booleans[i]),scale(mul(booleans[i],booleans[i-1]),-p-1),scale(sq(booleans[i-1]),p)));}\nlet correction=booleans[7];",'signed correction chain')
edit("fresh('correction.'+p,'base')","fresh('correction.partial.'+p,'base')",'correction witness names')

quot=json.loads((WORK/'field-quotients/patch-certificate.json').read_text())
assert quot['baselineBuilderSha256']==hashlib.sha256(source.read_bytes()).hexdigest()
for change in quot['changes']:
    # The square-completion evaluator has an order52 and order16 return.
    # Both receive the same conditional U0/V0 quotient fusion.
    count=2 if change['name']=='fuse logs into local-parameter quotient' else 1
    edit(change['old'],change['new'],change['name'],count)

spec=importlib.util.spec_from_file_location('evaluation_patch',WORK/'detector-circuits/patch_eval_blocks.py')
evaluation=importlib.util.module_from_spec(spec)
spec.loader.exec_module(evaluation)
text=evaluation.patch(text)
events.append({'name':'split degree10 evaluator with fused low block','source':'../detector-circuits/patch_eval_blocks.py::patch','expectedSavings':27})
for change in json.loads((WORK/'field-quotients/final-b/patch.json').read_text()):
    edit(change['old'],change['new'],'final-B quotient fusion')
edit('let points={};for(let n of names)points[n]=double(n,half[n],true);',(WORK/'dag-sharing/point-replacement.cjs').read_text(),'quadratic point chart')
for old,new in [('.half.x0','.chart.t0'),('.half.x1','.chart.t1'),('.half.y0','.chart.h0'),('.half.y1','.chart.h1')]:
    edit(old,new,'point base coordinate semantics')
spec=importlib.util.spec_from_file_location('weight_patch',WORK/'detector-circuits/patch_weight_factor.py')
weights=importlib.util.module_from_spec(spec)
spec.loader.exec_module(weights)
text=weights.patch(text)
events.append({'name':'share q1*e6 between q16 and q52','source':'../detector-circuits/patch_weight_factor.py::patch','expectedSavings':9})
old_source='const inputSource='+json.dumps(str(BASE / 'sources/diophantine_optimization_20261106_v3.tex'))+';'
edit(old_source,"const inputSource=path.resolve(__dirname,'sources/diophantine_optimization_20261106_v3.tex');",'portable source provenance path')
(HERE/'sources').mkdir(exist_ok=True)
shutil.copyfile(BASE/'sources/diophantine_optimization_20261106_v3.tex',HERE/'sources/diophantine_optimization_20261106_v3.tex')

edit("fs.writeFileSync(path.join(OUT,'raw-ir.json')", "data.variant={name:'combined_primary',status:'pending_independent_review',transformations:'transformations.json',inputUnchanged:true};\nfs.writeFileSync(path.join(OUT,'raw-ir.json')",'candidate provenance')
out=HERE/'build_source.cjs'
out.write_text(text,newline='\n')
files=[source,WORK/'detector-circuits/patch_builder.py',WORK/'dag-sharing/log-replacement.cjs',WORK/'source-compression/build_variant.py',WORK/'field-quotients/patch-certificate.json']
files.extend([WORK/'detector-circuits/patch_eval_blocks.py',WORK/'field-quotients/final-b/patch.json',WORK/'dag-sharing/point-replacement.cjs'])
files.append(WORK/'detector-circuits/patch_weight_factor.py')
manifest={'baseline':str(BASE),'components':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files],'edits':events,'builderSha256':hashlib.sha256(out.read_bytes()).hexdigest(),'status':'pending_independent_review'}
(HERE/'transformations.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(out)

"""Produce the independently editable quotient-fusion candidate from frozen bytes."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1] / 'quartic-version5-release/repository/quartics/quartic-1272'
source = BASE / 'builder/build_source.cjs'
s = source.read_text()
changes = []
def replace(old, new, name):
    global s
    assert s.count(old) == 1, (name, s.count(old))
    s = s.replace(old, new)
    changes.append({'name': name, 'old': old, 'new': new})

replace("function parameters(name,p){return{f:finv(name+'.f',p.x),z:fquot(name+'.z',fscale(p.x,-1),p.y,'finite_double_or_difference_nonzero_y_Brox4311_4348')};}",
"function parameters(name,p){return{point:p,f:finv(name+'.f',p.x),z:(name==='U0'||name==='V0')?null:fquot(name+'.z',fscale(p.x,-1),p.y,'finite_double_or_difference_nonzero_y_Brox4311_4348')};}", 'omit two shared-denominator z pairs')
replace("return fmul(name,p.z,out);", "return p.z?fmul(name,p.z,out):fquot(name,[scale(add(mul(p.point.x[0],out[0]),scale(mul(p.point.x[1],out[1]),2)),-1),scale(add(mul(p.point.x[0],out[1]),mul(p.point.x[1],out[0])),-1)],p.point.y,'finite_double_or_difference_nonzero_y_Brox4311_4348');", 'fuse logs into local-parameter quotient')
replace("zRatio=fquot('scalar.zRatio',PS.z,PU[0].z,'finite_double_nonzero_z_Brox4350_4352')", "zRatio=fquot('scalar.zRatio',[scale(add(mul(PS.z[0],PU[0].point.y[0]),scale(mul(PS.z[1],PU[0].point.y[1]),2)),-1),scale(add(mul(PS.z[0],PU[0].point.y[1]),mul(PS.z[1],PU[0].point.y[0])),-1)],PU[0].point.x,'retained_U0_f_inverse')", 'fuse scalar ratio without U0 local parameter')
replace("let ep=rm('detector'+r+'.eWeight',rp('detector'+r+'.Adelta5',Ad,5),fi),ei=inv('detector'+r+'.eWeightInverse',ep),Rv=rm('detector'+r+'.R',ei,di);", "let ep=rquot('detector'+r+'.eWeight',mul(rp('detector'+r+'.Adelta4',Ad,4),Ad),Fv,'retained_FInverse'),Rv=rquot('detector'+r+'.R',di,ep,'nonzero_numerator_di_enforces_denominator');", 'fuse weight and reciprocal R')
replace("let fi=inv('detector'+r+'.FInverse',Fv),di=inv('detector'+r+'.deltaInverse',delta),Ad=rm('detector'+r+'.Adelta',A,delta);", "let di=inv('detector'+r+'.deltaInverse',delta),Ad=rm('detector'+r+'.Adelta',A,delta);", 'remove F inverse using strictly positive fixed scale')
replace("'retained_FInverse'", "'positive_scale_and_deltaInverse_make_numerator_nonzero'", 'record F domain proof')
replace("let q1=rm('detector'+r+'.q1',ep,rp('detector'+r+'.deltaInverse3',di,3));", "let q1=rquot('detector'+r+'.q1',mul(ep,rsq('detector'+r+'.deltaInverse2',di)),delta,'retained_deltaInverse');", 'fuse inverse-cube product')
replace("let wi=inv('detector'+r+'.w0Inverse',w[0]),norm=assign('detector'+r+'.norm',sub(sq(w[0]),scale(sq(w[1]),2))),nw=rm('detector'+r+'.normOver2w0',scale(norm,Q(1,2)),wi),bv=rm('detector'+r+'.B',Rv,rsq('detector'+r+'.normOver2w0Square',nw));", "let wi=inv('detector'+r+'.w0Inverse',w[0]),nw=rquot('detector'+r+'.normOver2w0',scale(sub(sq(w[0]),scale(sq(w[1]),2)),Q(1,2)),w[0],'retained_w0Inverse'),bv=rm('detector'+r+'.B',Rv,rsq('detector'+r+'.normOver2w0Square',nw));", 'fuse norm quotient retaining trace guard')
replace("const inputSource=path.resolve(__dirname,'..',sourceName);", 'const inputSource='+json.dumps(str(BASE / 'sources/diophantine_optimization_20261106_v3.tex'))+';', 'resolve immutable mathematical source')
(HERE/'build_candidate.cjs').write_text(s, newline='\n')
(HERE/'patch-certificate.json').write_text(json.dumps({'baselineBuilderSha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'changes': changes},indent=2)+'\n')
print('wrote candidate builder and exact patch certificate')

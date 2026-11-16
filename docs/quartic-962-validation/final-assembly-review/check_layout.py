"""Verify only display layout changed since the accepted editorial version."""
from pathlib import Path
import ast,contextlib,hashlib,io,json,re
HERE=Path(__file__).resolve().parent
P=HERE.parent
script=P/'assemble_analytic_candidate.py'
code=script.read_text(encoding='utf-8')
displays=[n for n in ast.walk(ast.parse(code)) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ['old_display','new_display']]
displays.sort(key=lambda n:n.lineno)
assert len(displays)==4
pairs=[(ast.literal_eval(displays[i].value),ast.literal_eval(displays[i+1].value)) for i in [0,2]]
def math_tokens(s):
    for token in [r'\begin{aligned}',r'\end{aligned}',r'\qquad',r'\quad',r'\\','&']:
        s=s.replace(token,'')
    return re.sub(r'\s+','',s)
assert all(math_tokens(old)==math_tokens(new) for old,new in pairs)
target=P/'manuscript/quartic_962-analytic-candidate.tex'
current=target.read_text(encoding='utf-8')
previous=current
for old,new in pairs:
    assert previous.count(new)==1
    previous=previous.replace(new,old)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
assert sha(previous)=='a00e3aca8bb55987bce8548ab9e5ce4392c89d1d76459a7c7ac33fca303a287b'
assert sha(current)=='06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c'
outputs={}
original_write,original_mkdir=Path.write_text,Path.mkdir
def capture(self,data,*a,**kw):
    outputs[self.resolve()]=data
    return len(data)
try:
    Path.write_text,Path.mkdir=capture,lambda *a,**kw:None
    with contextlib.redirect_stdout(io.StringIO()):
        exec(compile(code,str(script),'exec'),{'__file__':str(script),'__name__':'__main__'})
finally:
    Path.write_text,Path.mkdir=original_write,original_mkdir
checks=[]
for path,text in outputs.items():
    if path.suffix=='.tex':
        assert text==path.read_text(encoding='utf-8')
        checks.append({'path':str(path.relative_to(P)),'sha256':sha(text),'exact_replay':True})
result={'status':'passed','previous_candidate_sha256':sha(previous),'candidate_sha256':sha(current),'two_layout_changes_only':True,'math_tokens_identical_after_removing_alignment_and_spacing':True,'exact_outputs':checks,'script_sha256':hashlib.sha256(script.read_bytes()).hexdigest()}
(HERE/'layout-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

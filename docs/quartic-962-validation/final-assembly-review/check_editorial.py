"""Check the authorized attribution delta, without writing assembly outputs."""
from pathlib import Path
import contextlib,hashlib,io,json,re
HERE=Path(__file__).resolve().parent
P=HERE.parent
script=P/'assemble_analytic_candidate.py'
code=script.read_text(encoding='utf-8')
start=code.index("once('Brox. Thus the degree of a quartic definition is optimal.'")
end=code.index('labels = re.findall',start)
editorial=code[start:end]
assert editorial.count('once(')==8
def run(text):
    outputs={}
    original_write,original_mkdir=Path.write_text,Path.mkdir
    def capture(self,data,*args,**kwargs):
        outputs[self.resolve()]=data
        return len(data)
    try:
        Path.write_text,Path.mkdir=capture,lambda *a,**kw:None
        with contextlib.redirect_stdout(io.StringIO()):
            exec(compile(text,str(script),'exec'),{'__file__':str(script),'__name__':'__main__'})
    finally:
        Path.write_text,Path.mkdir=original_write,original_mkdir
    return outputs
before=run(code[:start]+code[end:])
after=run(code)
target=(P/'manuscript/quartic_962-analytic-candidate.tex').resolve()
hash_text=lambda s:hashlib.sha256(s.encode()).hexdigest()
assert hash_text(before[target])=='b43f096ba3a4b1a979778ae1593ce3ad89048a2d28016e5ee9f35b124238dce7'
assert hash_text(after[target])=='a00e3aca8bb55987bce8548ab9e5ce4392c89d1d76459a7c7ac33fca303a287b'
checks=[]
for path,text in after.items():
    if path.suffix=='.tex':
        assert text==path.read_text(encoding='utf-8'),path
        checks.append({'path':str(path.relative_to(P)),'sha256':hash_text(text),'exact_replay':True})
assert r'\author{}' in after[target]
assert after[target].count(r'\author{')==1
visible=re.sub(r'\\href\{[^}]*\}',r'\\href{URL}',after[target])
assert 'Brox' not in visible
assert 'Brox2026' not in after[target]
assert re.findall(r'https?://[^}\s]+',before[target])==re.findall(r'https?://[^}\s]+',after[target])
result={'status':'passed','previous_candidate_sha256':hash_text(before[target]),'candidate_sha256':hash_text(after[target]),'eight_editorial_replacements_and_citation_key_only':True,'author_blank':True,'no_visible_personal_attribution':True,'all_real_urls_preserved':True,'exact_outputs':checks,'script_sha256':hashlib.sha256(script.read_bytes()).hexdigest()}
(HERE/'editorial-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

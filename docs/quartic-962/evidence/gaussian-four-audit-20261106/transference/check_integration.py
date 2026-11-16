"""Read-only independent reconstruction; writes only this audit directory."""
from pathlib import Path
import hashlib, json, re, difflib

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda x:hashlib.sha256(x).hexdigest()
raw=(ROOT/'baseline.tex').read_bytes()
candidate_raw=(ROOT/'quartic_962.tex').read_bytes()
assert sha(raw)=='06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c'
assert sha(candidate_raw)=='8ca476687a7ab761f3de4d0c964608a3e7d249a97a6c7647d9057ec5a4638c29'
base=raw.decode(); candidate=candidate_raw.decode(); lines=base.splitlines(True)
# This range list is independent of execution of integrate.py.
ranges=[(16389,16531,'tail/replacement-tail.tex'),
        (16533,17940,'weights/weights_fragment.tex'),
        (17941,18279,'transference/replacement.tex'),
        (18387,18392,'patterns/repair-dense-model.tex'),
        (18517,18526,'patterns/repair-ray-fixed-field.tex')]
pieces=[]; cursor=0; fragments=[]
for first,last,path in ranges:
    assert cursor<=first-1
    text=(ROOT/path).read_text(encoding='utf-8')
    pieces.extend([''.join(lines[cursor:first-1]),text]); cursor=last
    fragments.append({'path':path,'baseline_inclusive_lines':[first,last],
                      'sha256':sha((ROOT/path).read_bytes()),
                      'normalized_text_sha256':sha(text.encode()),
                      'occurrences_in_candidate':candidate.count(text)})
    assert candidate.count(text)==1
pieces.append(''.join(lines[cursor:]))
expected=''.join(pieces)
old='Fix the coefficients, $M$, and the base modulus first. Choose one fixed\n$L$ so large that\n'
new=old.replace('$L$','$L\\geq\\max(L_1,L_*)$')
assert expected.count(old)==1
expected=expected.replace(old,new)
oldbib=r'Forum Math. Pi \textbf{6} (2018), e1, 73 pp.'
newbib=oldbib.replace('73 pp.','60 pp.')
assert expected.count(oldbib)==1
expected=expected.replace(oldbib,newbib)
assert expected.encode()==candidate_raw

spec=json.loads((ROOT/'patterns/edit-specs.json').read_text())
assert [(e['baseline_start_line'],e['baseline_end_line']) for e in spec['edits']]==[(18387,18392),(18517,18526),(18686,18686)]
assert spec['edits'][2]['old_text']==oldbib and spec['edits'][2]['new_text']==newbib
actual_diff=(ROOT/'changes.diff').read_text(encoding='utf-8')
expected_diff=''.join(difflib.unified_diff(base.splitlines(True),candidate.splitlines(True),fromfile='baseline.tex',tofile='quartic_962.tex'))
assert actual_diff==expected_diff

labels=lambda s:re.findall(r'\\label\{([^}]+)\}',s)
ol,nl=labels(base),labels(candidate)
assert len(nl)==len(set(nl))
assert set(ol)<=set(nl)
assert set(nl)-set(ol)=={'cor:ga-fixed-centered-nilsequence'}
refs=lambda s:set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',s))
assert (refs(candidate)-refs(base))<=set(nl)

def declaration(text,label,env):
    pos=text.index('\\label{'+label+'}')
    start=text.rfind('\\begin{'+env+'}',0,pos)
    end=text.index('\\end{'+env+'}',pos)+len('\\end{'+env+'}')
    assert start>=0
    return text[start:end]
unchanged=[]
for label,env in [('thm:v5-simultaneous-primes','theorem'),('prop:v5-artin-patterns','proposition')]:
    a=declaration(base,label,env); b=declaration(candidate,label,env)
    assert a==b
    unchanged.append({'label':label,'sha256':sha(a.encode())})
discharge=(ROOT/'weights/centered_nilsequence_discharge.tex').read_text()
assert candidate.count(discharge)==1
assert candidate.index('\\label{cor:ga-fixed-centered-nilsequence}')<candidate.index('\\label{subsec:gaussian-gowers-bridge}')
assert 'uniformly for $L\\geq L_*$' in candidate
assert new in candidate
assert 'pp.~12--13; the final typeset statement was not compared.' in candidate
assert candidate_raw== (ROOT/'quartic_962.tex').read_bytes()

result={'status':'accepted_assembly_and_interfaces','scope':'Assembly and handoff consistency only; not a second full proof audit.',
 'baseline_sha256':sha(raw),'candidate':{'path':'quartic_962.tex','sha256':sha(candidate_raw),'bytes':len(candidate_raw)},
 'reviewed_files':{p:sha((ROOT/p).read_bytes()) for p in ['integrate.py','changes.diff','assembly.json','patterns/edit-specs.json']},
 'fragment_checks':fragments,'independent_reconstruction_matches_exact_candidate_bytes':True,
 'diff_matches_independent_unified_diff':True,'changes_outside_authorized_intervals':False,
 'root_addition':'L >= max(L_1,L_*), before fixing K_L and before any asymptotic limit',
 'all_prior_labels_preserved':True,'only_new_label':'cor:ga-fixed-centered-nilsequence',
 'duplicate_labels':[],'new_unresolved_references':[],
 'unchanged_target_declarations':unchanged,
 'interfaces':{'tail_to_final_cutoff':'accepted','weights_to_centered_nilsequence_input':'accepted','linear_to_local_cube':'unchanged and accepted','transference_to_dense_model':'accepted','ray_quotient_to_density':'same stated quotient and density inputs preserved','source_version_qualifications':'preserved'},
 'candidate_modified_by_review':False,'findings':[],
 'limitations':['No new full proof audit','No full-manuscript TeX compilation in this integration review','DK final typeset comparison remains unverified as stated in candidate']}
(HERE/'integration-review.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))

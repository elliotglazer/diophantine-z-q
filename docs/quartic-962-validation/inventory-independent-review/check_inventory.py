"""Independent pin, source-span and dependency-scope checks."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
T=ROOT/'work/quartic-version6-release/inventory-tools'
S=ROOT/'work/inventory-sandbox/version6'
register=T/'new-applications.json'
d=json.loads(register.read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
candidate=ROOT/'work/quartic-version6-preparation/manuscript/quartic_962-analytic-candidate.tex'
assert sha(candidate)==d['candidate_pin']['sha256']=='06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c'
text=candidate.read_text(encoding='utf-8')
count=0
def walk(v):
    global count
    if isinstance(v,dict):
        if {'start_character','end_character','text_sha256'}<=v.keys() and v.get('path','').replace('\\','/').endswith(('quartic_962.tex','quartic_962-analytic-candidate.tex')):
            excerpt=text[v['start_character']:v['end_character']]
            assert hashlib.sha256(excerpt.encode()).hexdigest()==v['text_sha256'],v
            count+=1
        for key,a in v.items():
            if not key.startswith('reviewed_component_'):walk(a)
    elif isinstance(v,list):
        for a in v:walk(a)
for name in ['theorem-applications.json','internal-results.json','citations.json']:
    walk(json.loads((S/'docs/quartic-962'/name).read_text(encoding='utf-8')))
evidence=[]
for row in d['evidence_pins']:
    p=S/row['path']
    assert p.exists(),p
    assert sha(p)==row['sha256'],p
    evidence.append(row['path'])
source_pins={}
for a in d['applications']:
    for version in a.get('exact_source_versions',[]):
        for row in version.get('files',[]):
            rel=row.get('path',row.get('workspace_relative_path'))
            if rel and (ROOT/rel).exists():
                assert sha(ROOT/rel)==row['sha256'],rel
                source_pins[rel]=row['sha256']
ids={a['id'] for a in d['applications']}
retired={a['id'] for a in d['retired_applications']}
assert not retired.intersection(ids|set(d['inherit_v5_applications']))
assert 'V5-SUN-FT-LINEAR' in retired and 'V5-SUN-DK-RELATIVE-INVERSE' in retired
assert 'V6-GA-DK-INVERSE' in ids
assert d['dependency_policy']['uses_frei_tinkova_as_assumed_theorem'] is False
assert d['dependency_policy']['all_final_published_versions_checked'] is False
for row in d['retired_applications']:
    assert set(row['replacement_ids'])<=ids
for row in d['reviewed_fragments']:
    if row['provenance']['kind']=='reviewed':
        p=S/row['provenance']['receipt_path']; receipt=json.loads(p.read_text())
        def pointer(v,ptr):
            for part in ptr.strip('/').split('/'):v=v[part]
            return v
        assert pointer(receipt,row['provenance']['status_pointer'])==row['provenance']['accepted_status']
        assert pointer(receipt,row['provenance']['sha256_pointer'])==sha(S/row['path'])==row['sha256']
result={'status':'passed','candidate_sha256':sha(candidate),'register_sha256':sha(register),'current_source_spans_checked':count,'evidence_pins_checked':len(evidence),'locally_available_source_versions_checked':source_pins,'new_applications':len(ids),'retired_applications':len(retired),'review_scope':'Pin fidelity and correct retirement scope; mathematical coverage assessed in REVIEW.md, not inferred from these checks.'}
(HERE/'check-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

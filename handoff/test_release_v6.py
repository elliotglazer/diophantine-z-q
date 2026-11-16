"""Adversarial Version 6 metadata tests using small artificial payloads."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import zipfile
from release_config import (V6_CHECKS,V6_METRICS,V6_PACKAGE_REQUIRED,baseline_for_release,
                            validate_current,generated_state,generated_start)


def encoded(value):return json.dumps(value,sort_keys=True).encode()
def record(raw):return {'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


def fixture():
    root='quartics/quartic-962/'
    package={name:('fixture '+name).encode() for name in V6_PACKAGE_REQUIRED-{'MANIFEST.json'}}
    package['MANIFEST.json']=encoded({'schema':'quartic962-frozen-v1',
        'baselineManifestSha256':'aa7f04c54e8b778a419a1be8d24e0b3a9a8540c50202d41815864a156d6985c6',
        'baselinePolynomialSha256':'02e4771ba6e6c2abc749e33e8440cc256939f48005d5102fba7d9853489c8586',
        'counts':{'coordinates':962,'activeCoordinates':962,'residuals':919,
                  'ordinaryCoordinateMonomials':55409,'degree':4},
        'files':{name:record(raw)['sha256'] for name,raw in package.items()}})
    objects={root+name:raw for name,raw in package.items()}
    objects.update({'quartic_962.tex':b'Version 6','quartic_962.pdf':b'%PDF fixture',
        'quartic_4973.tex':b'preserved 4973','docs/quartic-962/README.md':b'inventory',
        'scripts/check_quartic962.py':b'wrapper','scripts/quartic962_checks.cjs':b'checker',
        'research/version6/README.md':b'research guide'})
    reviews={group:'docs/quartic-962-validation/'+group+'.json'
             for group in ('analytic-proof','lower-bound','optimization','inventory')}
    objects.update({name:b'{"status":"fixture"}' for name in reviews.values()})
    inventory_input='docs/quartic-962/new-applications.json'
    objects[inventory_input]=b'{"fixture":"authored inventory"}'
    objects[reviews['inventory']]=encoded({'status':'accepted_scoped_inventory_and_evidence_binding',
        'candidate_sha256':record(objects['quartic_962.tex'])['sha256'],
        'authored_register_sha256':record(objects[inventory_input])['sha256'],'checks':{'status':'passed'}})
    assembly_receipt='docs/quartic-962-validation/assembly.json'
    objects[assembly_receipt]=encoded({'status':'accepted_assembly_fidelity',
        'candidate_sha256':record(objects['quartic_962.tex'])['sha256']})
    selection=[]
    for group in ('analytic-proof','lower-bound','optimization'):
        name='research/version6/'+group+'/README.md'; raw=group.encode(); objects[name]=raw
        selection.append({'group':group,'source':group+'/README.md','decision':'include',
                          'repositoryPath':name,**record(raw)})
    manifest='handoff/V6_RESEARCH_MANIFEST.json'
    objects[manifest]=encoded({'schema':'quartic-v6-research-selection-v1','status':'FROZEN','files':selection})
    polynomial=record(package['polynomial.json'])['sha256']
    receipt='handoff/releases/version6/REPRODUCTION.json'
    objects[receipt]=encoded({'schema':'quartic-962-reproduction-v1','status':'PASS',
        'packageManifestSha256':record(package['MANIFEST.json'])['sha256'],
        'frozenPolynomialSha256':polynomial,'rebuiltPolynomialSha256':polynomial,'byteIdentical':True,
        'result':{'variablesIncludingInput':962,'existentialWitnesses':961,'degree':4,'monomials':55409,
                  'quadraticResiduals':919,'primitiveContent':'1','height':'64*3^(2^28)'},
        'requiredChecks':V6_CHECKS,'checks':[{'name':name,'status':'PASS'} for name in V6_CHECKS]})
    release={'format':'quartic-handoff-release/v3','state':'READY','version':6,'date':'2026-11-06',
        'release_tag':'quartic-962-version-6','manuscript':'quartic_962.tex','pdf':'quartic_962.pdf',
        'package':root[:-1],'package_manifest':'MANIFEST.json','polynomial':'polynomial.json',
        'inventory':'docs/quartic-962/README.md','source_id':'fixture-only','source_contract':{'scope':'fixture'},
        'expected':deepcopy(V6_METRICS),'polynomial_sha256':polynomial,'verification_receipt':receipt,
        'research_manifest':manifest,'review_files':reviews,'inventory_input':inventory_input,
        'inventory_input_sha256':record(objects[inventory_input])['sha256'],'assembly_receipt':assembly_receipt,
        'support_files':['scripts/check_quartic962.py','scripts/quartic962_checks.cjs'],
        'assets':{'full':'z-in-q-version6-full-handoff.zip','current':'z-in-q-version6-current-handoff.zip'},
        'snapshot_pins':{name:record(raw) for name,raw in objects.items() if name!='quartic_4973.tex'},
        'preserved_pins':{'quartic_4973.tex':record(objects['quartic_4973.tex'])}}
    objects['handoff/release.json']=encoded(release)
    return release,objects,receipt


def run_tests():
    release,objects,receipt=fixture(); validate_current(objects.__getitem__,set(objects),release,receipt)
    cases=[]
    def reject(name,mutate,rebind=False):
        r,o,p=fixture(); mutate(r,o,p)
        if rebind:
            r['snapshot_pins']={name:record(o[name]) for name in r['snapshot_pins'] if name in o}
            o['handoff/release.json']=encoded(r)
        try:validate_current(o.__getitem__,set(o),r,p)
        except (ValueError,KeyError):cases.append(name)
        else:raise AssertionError('Accepted invalid fixture: '+name)
    def change(o,path,key,value):
        data=json.loads(o[path]); data[key]=value; o[path]=encoded(data)
    reject('preparation cannot freeze',lambda r,o,p:r.update(state='PREPARATION'))
    reject('pending contract',lambda r,o,p:r.update(source_id='PENDING_FINAL_SOURCE'))
    reject('stale assets',lambda r,o,p:r['assets'].update(full='version5.zip'))
    reject('wrong coordinate count',lambda r,o,p:r['expected'].update(variables=963))
    reject('missing replay checker',lambda r,o,p:o.pop('scripts/quartic962_checks.cjs'))
    reject('uncommitted descriptor',lambda r,o,p:o.update({'handoff/release.json':b'{}'}))
    reject('modified preserved artifact',lambda r,o,p:o.update({'quartic_4973.tex':b'changed'}))
    reject('unpinned research',lambda r,o,p:o.update({'research/version6/optimization/extra.md':b'new'}))
    reject('unpinned review',lambda r,o,p:o.update({'docs/quartic-962-validation/extra.json':b'{}'}))
    reject('extra package output',lambda r,o,p:o.update({'quartics/quartic-962/replay/out.json':b'{}'}))
    reject('modified polynomial',lambda r,o,p:o.update({'quartics/quartic-962/polynomial.json':b'changed'}))
    reject('failed replay',lambda r,o,p:change(o,p,'status','FAIL'),True)
    reject('stale replay package',lambda r,o,p:change(o,p,'packageManifestSha256','0'*64),True)
    reject('wrong regenerated polynomial',lambda r,o,p:change(o,p,'rebuiltPolynomialSha256','0'*64),True)
    reject('missing required checks',lambda r,o,p:change(o,p,'requiredChecks',[]),True)
    reject('missing completed checks',lambda r,o,p:change(o,p,'checks',[]),True)
    reject('nonidentical regenerated polynomial',lambda r,o,p:change(o,p,'byteIdentical',False),True)
    reject('wrong replay metrics',lambda r,o,p:change(o,p,'result',{}),True)
    reject('working research catalogue',lambda r,o,p:change(o,r['research_manifest'],'status','WORKING'),True)
    reject('missing research groups',lambda r,o,p:change(o,r['research_manifest'],'files',[]),True)
    reject('wrong manuscript version',lambda r,o,p:o.update({'quartic_962.tex':b'Version 5'}),True)
    reject('invalid PDF',lambda r,o,p:o.update({'quartic_962.pdf':b'plain text'}),True)
    reject('stale authored inventory pin',lambda r,o,p:r.update(inventory_input_sha256='0'*64),True)
    reject('stale inventory manuscript review',lambda r,o,p:change(o,r['review_files']['inventory'],'candidate_sha256','0'*64),True)
    reject('stale inventory register review',lambda r,o,p:change(o,r['review_files']['inventory'],'authored_register_sha256','0'*64),True)
    reject('stale assembly review',lambda r,o,p:change(o,r['assembly_receipt'],'candidate_sha256','0'*64),True)
    # The complete current-only extraction path uses a tiny payload. No release archive is built.
    from verify_handoff import extract_verified
    r,o,p=fixture(); baseline=baseline_for_release(r)
    assert baseline['sha256']=='8bca6f77f4721140c3d9db0d518595472a463a58f04f3efcf14173a9cf0ff236'
    assert baseline_for_release({'version':5})['sha256']=='827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b'
    helpers=('verify_handoff.py','release_config.py','legacy_verify_handoff_v2.py')
    for name in helpers:o['handoff/'+name]=('fixture '+name).encode()
    plan={'format':'quartic-handoff-plan/v2','snapshot_commit':'a'*40,'release':r,
        'verification_receipt':p,'baseline':baseline,
        'files':[{'kind':'git','path':name,'archive_path':'current/'+name,'git_blob':'b'*40,**record(raw)}
                 for name,raw in o.items()]}
    state=generated_state(plan,False)
    entries={'current/'+name:raw for name,raw in o.items()}
    entries.update({'PLAN.json':encoded(plan),'CURRENT_STATE.json':encoded(state),
                    'START_HERE.md':generated_start(plan,False)})
    entries.update({name:o['handoff/'+name] for name in helpers})
    manifest={'format':'quartic-public-handoff/v2','snapshot_commit':plan['snapshot_commit'],
        'current_files':list(o),'files':{name:record(raw) for name,raw in entries.items()},
        'baseline':{**baseline,'included':False,'archive_path':'baseline/'+baseline['filename']},
        'history_scope':state['selected_history']}
    with tempfile.TemporaryDirectory(prefix='v6-handoff-fixture-') as temporary:
        path=Path(temporary)/'current.zip'
        with zipfile.ZipFile(path,'w') as archive:
            for name,raw in entries.items():archive.writestr(name,raw)
            archive.writestr('MANIFEST.json',encoded(manifest))
        result=extract_verified(path,Path(temporary)/'extracted',
                                record(entries['PLAN.json'])['sha256'],record(path.read_bytes())['sha256'])
        assert result['status']=='PASS' and result['externally_bound_archive']
        assert (Path(temporary)/'extracted/current/quartic_962.tex').read_bytes()==b'Version 6'
    return cases


if __name__=='__main__':
    print(json.dumps({'status':'PASS','scope':'Artificial metadata and ZIP fixtures only','cases':run_tests()},indent=2))

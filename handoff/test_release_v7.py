"""Version 7 audit-coverage and historical-baseline rejection tests."""
from copy import deepcopy
from test_release_v6 import fixture as fixture6, encoded, record
from release_config import validate_current, baseline_for_release, generated_start

def fixture():
    release,objects,receipt=fixture6()
    release.update(version=7,release_tag='quartic-962-version-7',manuscript='manuscripts/quartic_v7.tex',pdf='manuscripts/quartic_v7.pdf',
        assets={'full':'z-in-q-version7-full-handoff.zip','current':'z-in-q-version7-current-handoff.zip'},
        revision_manifest='handoff/V7_AUDIT_MANIFEST.json')
    objects.pop('quartic_962.tex')
    objects['manuscripts/quartic_v7.tex']=b'Version 7'
    objects['manuscripts/quartic_v7.pdf']=objects.pop('quartic_962.pdf')
    selected={}
    audits={}
    for group in ('tail','weights','transference','patterns'):
        path='docs/quartic-962/evidence/gaussian-four-audit-20261106/'+group+'/AUDIT.md'
        objects[path]=group.encode();selected[path]=record(objects[path]);audits[group]=path
    path='research/version7/README.md';objects[path]=b'new audit guide';selected[path]=record(objects[path])
    release['revision_audits']=audits
    objects[release['revision_manifest']]=encoded({'schema':'quartic-v7-audit-selection-v1','files':selected})
    objects[release['assembly_receipt']]=encoded({'status':'accepted_assembly_fidelity','candidate_sha256':record(objects['manuscripts/quartic_v7.tex'])['sha256']})
    review=__import__('json').loads(objects[release['review_files']['inventory']])
    review['candidate_sha256']=record(objects['manuscripts/quartic_v7.tex'])['sha256']
    objects[release['review_files']['inventory']]=encoded(review)
    release['snapshot_pins']={name:record(raw) for name,raw in objects.items() if name not in ('quartic_4973.tex','handoff/release.json')}
    objects['handoff/release.json']=encoded(release)
    return release,objects,receipt

def run_tests():
    release,objects,receipt=fixture()
    validate_current(objects.__getitem__,set(objects),release,receipt)
    assert baseline_for_release(release)['sha256']=='93b53944ea93de08dc653beb70202797c1cbbdf19602ae583940bbf137dd43bc'
    cases=['Version 7 complete audit fixture','Version 7 immutable Version 6 baseline']
    for label,mutate in [
        ('missing audit scope',lambda r,o:r['revision_audits'].pop('tail')),
        ('changed audit bytes',lambda r,o:o.__setitem__(r['revision_audits']['weights'],b'changed')),
        ('unlisted audit file',lambda r,o:o.__setitem__('docs/quartic-962/evidence/gaussian-four-audit-20261106/extra.md',b'unpinned')),
        ('wrong revision manifest',lambda r,o:r.__setitem__('revision_manifest','handoff/other.json')),
    ]:
        r,o,p=fixture();mutate(r,o);o['handoff/release.json']=encoded(r)
        try:validate_current(o.__getitem__,set(o),r,p)
        except ValueError:cases.append('Version 7 rejects '+label)
        else:raise AssertionError('Accepted '+label)
    return cases

if __name__=='__main__':print(run_tests())

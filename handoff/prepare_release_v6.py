"""Populate final Version 6 file pins after explicit source/review freeze.

The template must be marked READY by the release owner before this is run.
This script does not decide whether the analytic replacement is proved.
"""
import argparse
import hashlib
import json
from pathlib import Path
from release_config import validate_current


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,required=True)
    parser.add_argument('--template',type=Path,required=True)
    parser.add_argument('--preserved',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--prepare-only',action='store_true',help='Check complete pins but keep PREPARATION until the release owner decides READY')
    args=parser.parse_args()
    repo=args.repo.resolve(); release=json.loads(args.template.read_bytes())
    if release.get('state')!='READY' and not (args.prepare_only and release.get('state')=='PREPARATION'):
        raise ValueError('Final source/review freeze is not declared READY')
    pins={}
    roots=('quartics/quartic-962','docs/quartic-962','docs/quartic-962-validation',
           'research/version6','handoff/releases/version6')
    for root in roots:
        directory=repo/root
        if not directory.is_dir():raise ValueError('Missing complete release directory: '+root)
        for path in sorted(directory.rglob('*')):
            if path.is_symlink():raise ValueError('Symlink in release')
            if path.is_file():
                raw=path.read_bytes(); name=path.relative_to(repo).as_posix()
                pins[name]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
    for name in (release['manuscript'],release['pdf'],release['research_manifest'],release['inventory_input'],release['assembly_receipt'],
                 release['verification_receipt'],*release['review_files'].values(),*release['support_files']):
        raw=(repo/name).read_bytes(); pins[name]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
    release['snapshot_pins']=pins
    release['preserved_pins']=json.loads(args.preserved.read_bytes())['files']
    release['polynomial_sha256']=pins[release['package']+'/'+release['polynomial']]['sha256']
    encoded=(json.dumps(release,sort_keys=True,indent=2)+'\n').encode()
    checked=dict(release)
    checked['state']='READY'
    checked_encoded=(json.dumps(checked,sort_keys=True,indent=2)+'\n').encode()
    def read(name):return checked_encoded if name=='handoff/release.json' else (repo/name).read_bytes()
    names={p.relative_to(repo).as_posix() for p in repo.rglob('*') if p.is_file()}
    validate_current(read,names,checked,release['verification_receipt'])
    args.output.write_bytes(encoded)
    print(json.dumps({'status':'DESCRIPTOR PREPARED; OWNER READY DECISION PENDING' if args.prepare_only else 'FINAL DESCRIPTOR PREPARED',
                      'state':release['state'],'files':len(pins),'sha256':hashlib.sha256(encoded).hexdigest()},indent=2))


if __name__=='__main__':main()

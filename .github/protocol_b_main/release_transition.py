"""Read an immutable merge's release transition; never dispatch or parse candidate code."""
import re
SHA=re.compile(r'[0-9a-f]{40}')

def _sha(value):
    if not isinstance(value,str) or SHA.fullmatch(value) is None:
        raise ValueError('invalid Git identity')
    return value

def _commit(api, sha):
    value=api.json('git/commits/'+_sha(sha))
    if not isinstance(value,dict) or value.get('sha')!=sha:
        raise ValueError('commit identity mismatch')
    _sha((value.get('tree') or {}).get('sha'))
    return value

def _entry(api, tree_sha, path):
    parts=path.split('/')
    for index,part in enumerate(parts):
        value=api.json('git/trees/'+_sha(tree_sha))
        if (not isinstance(value,dict) or value.get('sha')!=tree_sha
                or value.get('truncated') is not False or not isinstance(value.get('tree'),list)):
            raise ValueError('incomplete immutable tree')
        rows=value['tree']
        names=[row.get('path') if isinstance(row,dict) else None for row in rows]
        if any(not isinstance(name,str) or '/' in name for name in names) or len(set(names))!=len(names):
            raise ValueError('ambiguous immutable tree')
        matches=[row for row in rows if row['path']==part]
        if not matches:return None  # Actual complete Git tree proves path absence.
        row=matches[0];_sha(row.get('sha'))
        if index==len(parts)-1:
            if row.get('type')!='blob' or row.get('mode') not in ('100644','100755'):
                raise ValueError('manifest is not a regular file')
            return {'sha':row['sha'],'mode':row['mode']}
        if row.get('type')!='tree' or row.get('mode')!='040000':
            raise ValueError('manifest directory is not a tree')
        tree_sha=row['sha']
    raise AssertionError('empty path')

def release_transition(api, merge_sha):
    """Any manifest change requires exact-merge checks, including deletion.

    All API reads use immutable Git objects. Missing requests, 404s, truncated
    trees, symlinks and malformed objects propagate as unresolved evidence.
    A source-file or event claim that a change is not a release is not used.
    """
    merged=_commit(api,merge_sha)
    parents=merged.get('parents')
    if not isinstance(parents,list) or len(parents) not in (1,2):
        raise ValueError('ambiguous main parent')
    for parent in parents:_sha(parent.get('sha'))
    previous=_commit(api,parents[0]['sha'])
    path='docs/current-manuscript.json'
    before=_entry(api,previous['tree']['sha'],path)
    after=_entry(api,merged['tree']['sha'],path)
    return {'merge':merge_sha,'first_parent':parents[0]['sha'],'path':path,
        'before':before,'after':after,'exact_release_required':before!=after,
        'manifest_removed':before is not None and after is None,'dispatch_authorized':False}

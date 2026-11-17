"""Read-only discovery of authentic deferred-merge publications.

The injected API is scoped to one repository and exposes GET only.
Discovery produces evidence, not dispatch authorization.
"""
import re
from urllib.parse import urlparse
from deferred_artifact import MAX_ZIP, read_original_records
from deferred_source import validate_deferred_chain


def pages(api, path, key=None, *, max_pages=100, identity=None):
    rows, declared, seen = [], None, set()
    sep = '&' if '?' in path else '?'
    for page in range(1, max_pages + 1):
        value = api.json(f'{path}{sep}per_page=100&page={page}')
        chunk = value if key is None else value.get(key)
        if not isinstance(chunk, list) or len(chunk) > 100:
            raise ValueError('invalid page')
        if key is not None and 'total_count' in value:
            count = value['total_count']
            if type(count) is not int or count < 0 or declared is not None and count != declared:
                raise ValueError('collection changed during pagination')
            declared = count
        for row in chunk:
            if not isinstance(row, dict): raise ValueError('invalid row')
            if identity is not None:
                ident = row.get(identity)
                if type(ident) is not int or ident <= 0 or ident in seen:
                    raise ValueError('missing or duplicate identity')
                seen.add(ident)
        rows.extend(chunk)
        if len(chunk) < 100:
            if declared is not None and len(rows) != declared:
                raise ValueError('incomplete collection')
            return rows
    raise ValueError('pagination limit; collection incomplete')


def required_review_app(api):
    ids = set()
    for rule in pages(api, 'rules/branches/main'):
        if rule.get('type') != 'required_status_checks': continue
        checks = (rule.get('parameters') or {}).get('required_status_checks')
        if not isinstance(checks, list): raise ValueError('malformed required checks')
        for item in checks:
            if not isinstance(item, dict): raise ValueError('malformed required check')
            if item.get('context') != 'Protocol B / review': continue
            app = item.get('integration_id')
            if type(app) is not int or app <= 0 or app == 15368:
                raise ValueError('review check has no dedicated App pin')
            ids.add(app)
    if len(ids) != 1: raise ValueError('missing or conflicting required App pins')
    return ids.pop()


def publication(api, repo, repo_id, check):
    url = urlparse(check.get('details_url') or '')
    match = re.fullmatch('/' + re.escape(repo) + r'/actions/runs/([1-9][0-9]*)', url.path)
    if url.scheme != 'https' or url.netloc != 'github.com' or url.query or url.fragment or match is None:
        raise ValueError('publisher link')
    rid = int(match[1]); run = api.json(f'actions/runs/{rid}')
    if (run.get('id') != rid or (run.get('repository') or {}).get('full_name') != repo
            or run.get('path') != '.github/workflows/protocol-b.yml'
            or run.get('status') != 'completed'):
        raise ValueError('publisher is foreign, unexpected or still active')
    attempt = run.get('run_attempt')
    if type(attempt) is not int or attempt <= 0: raise ValueError('publisher attempt')
    artifacts = pages(api, f'actions/runs/{rid}/artifacts', 'artifacts', identity='id')
    candidates = []
    for artifact in artifacts:
        name = artifact.get('name')
        found = re.fullmatch(f'protocol-b-{rid}-([1-9][0-9]*)', name or '')
        if found:
            candidates.append((int(found[1]), artifact))
    if (not candidates or len(candidates) > 32
            or len({a for a, _ in candidates}) != len(candidates)):
        raise ValueError('missing, ambiguous or excessive original attempts')
    # App comments can retain an earlier publication after its workflow is
    # rerun. Locate the original attempt by the App check ID in its original
    # decision, never by whichever attempt happens to be latest now.
    total = 0
    matches = []
    for original_attempt, artifact in candidates:
        if original_attempt > attempt: raise ValueError('artifact from a future attempt')
        if artifact.get('expired') is not False: raise ValueError('expired original artifact')
        size = artifact.get('size_in_bytes')
        if type(size) is not int or not 0 < size <= MAX_ZIP:
            raise ValueError('declared archive too large or invalid')
        total += size
        if total > 4 * MAX_ZIP: raise ValueError('original attempt archives exceed discovery bound')
        original = run if original_attempt == attempt else api.json(f'actions/runs/{rid}/attempts/{original_attempt}')
        if (original.get('id') != rid or original.get('run_attempt') != original_attempt
                or original.get('status') != 'completed'
                or (original.get('repository') or {}).get('full_name') != repo
                or original.get('path') != '.github/workflows/protocol-b.yml'):
            raise ValueError('original attempt identity')
        raw = api.bytes(f"actions/artifacts/{artifact['id']}/zip")
        retained = read_original_records(raw, artifact, original, repo_id)
        records = retained['records']
        decision = records.get('decision.json')
        if not isinstance(decision, dict) or decision.get('check') != check['id']:
            continue
        if 'post-merge-manual.json' not in records:
            raise ValueError('no original deferred-merge record')
        matches.append({'check': check, 'publisher': original, 'decision': decision,
            'deferred': records['post-merge-manual.json'], 'auto_result': records.get('auto-merge-result.json'),
            'artifact_id': retained['artifact_id'], 'artifact_digest': retained['digest']})
    if len(matches) != 1: raise ValueError('missing or ambiguous original App publication')
    return matches[0]


def discover_deferred(api, repo, number):
    """Use real current rules and App checks, then both original publications.

    Caller must retain errors as unresolved, not interpret them as no prior
    dispatch. No branch file, issue body or workflow_run event is authority.
    """
    if type(number) is not int or number <= 0: raise ValueError('PR number')
    metadata = api.json('')
    if metadata.get('full_name') != repo or metadata.get('default_branch') != 'main':
        raise ValueError('repository/default branch')
    repo_id = metadata.get('id')
    if type(repo_id) is not int or repo_id <= 0: raise ValueError('repository identity')
    pr = api.json(f'pulls/{number}')
    if (pr.get('number') != number or pr.get('merged') is not True or pr.get('state') != 'closed'
            or (pr.get('base') or {}).get('ref') != 'main'
            or ((pr.get('base') or {}).get('repo') or {}).get('full_name') != repo
            or (pr.get('merged_by') or {}).get('login') != 'github-actions[bot]'
            or (pr.get('merged_by') or {}).get('type') != 'Bot'):
        raise ValueError('not a confirmed gate-actor merge')
    head = (pr.get('head') or {}).get('sha')
    merge = pr.get('merge_commit_sha')
    if any(not isinstance(s, str) or re.fullmatch(r'[0-9a-f]{40}', s) is None for s in (head, merge)):
        raise ValueError('commit identity')
    app = required_review_app(api)
    checks = pages(api, f'commits/{head}/check-runs?filter=all', 'check_runs', identity='id')
    checks = sorted((c for c in checks if c.get('name') == 'Protocol B / review'
                     and (c.get('app') or {}).get('id') == app), key=lambda c:c['id'], reverse=True)
    if (not checks or checks[0].get('head_sha') != head or checks[0].get('status') != 'completed'
            or checks[0].get('conclusion') != 'success'):
        raise ValueError('latest required App check is not exact-head acceptance')
    accepted = publication(api, repo, repo_id, checks[0])
    attempts = []
    for check in checks:
        if check.get('status') != 'completed' or check.get('conclusion') != 'success': continue
        try:
            requester = accepted if check['id'] == checks[0]['id'] else publication(api, repo, repo_id, check)
            result = validate_deferred_chain(repo, app, pr, accepted, requester)
            if not result['eligible']:
                attempts.append({'check':check['id'], 'reason':result['reason']}); continue
            return {'eligible':True, 'dispatch_authorized':False, 'pr':pr, 'required_app':app,
                    'accepted':accepted, 'requester':requester, 'result':result, 'examined':attempts}
        except (KeyError, TypeError, ValueError) as error:
            attempts.append({'check':check['id'], 'reason':str(error)})
    return {'eligible':False, 'dispatch_authorized':False, 'reason':'no authenticated original request', 'examined':attempts}

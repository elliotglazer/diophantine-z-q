"""Complete read-only recovery queue discovery, without a mutable-time watermark.

The caller must authenticate the deployment baseline and retained pending IDs.
This module never dispatches. Re-enumerating all PR numbers avoids losing an
old PR that merges later or whose updated_at moves between recovery runs.
"""
import datetime,re
from discover_deferred import pages

def _stamp(value):
    if not isinstance(value,str):raise ValueError('timestamp')
    parsed=datetime.datetime.fromisoformat(value.replace('Z','+00:00'))
    if parsed.utcoffset() is None:raise ValueError('timestamp timezone')
    return parsed

def discover_queue(api,repo,baseline,*,pending_numbers=()):
    if (not isinstance(baseline,dict) or baseline.get('schema')!='main-check-baseline/v1'
            or baseline.get('repository')!=repo
            or not isinstance(baseline.get('activation_commit'),str)
            or re.fullmatch('[0-9a-f]{40}',baseline['activation_commit']) is None):
        raise ValueError('untrusted or invalid deployment baseline')
    activated=_stamp(baseline.get('activated_at'))
    if any(type(n) is not int or n<=0 for n in pending_numbers):raise ValueError('invalid pending identity')
    metadata=api.json('')
    if metadata.get('full_name')!=repo or metadata.get('default_branch')!='main':raise ValueError('repository identity')
    # state=all keeps reopened and newly closed old PRs in the same enumeration.
    # No early stop at updated_at, last-N window, or persisted time cursor.
    listed=pages(api,'pulls?state=all&sort=created&direction=asc',identity='id')
    numbers=[]
    for row in listed:
        number=row.get('number')
        if type(number) is not int or number<=0 or number in numbers:raise ValueError('ambiguous PR identity')
        numbers.append(number)
    # Recover retained operations first even if their PR vanished from the list.
    pending=set(pending_numbers)
    order=sorted(pending)+[n for n in numbers if n not in pending]
    candidates=[];unresolved=[];dispositions=[]
    for number in order:
        try:
            pr=api.json('pulls/'+str(number))
            if (pr.get('number')!=number or ((pr.get('base') or {}).get('repo') or {}).get('full_name')!=repo):
                raise ValueError('PR identity mismatch')
            prior=number in pending
            if prior:
                candidates.append({'number':number,'source':'retained_pending','pr':pr})
                continue
            if pr.get('state') not in ('open','closed') or type(pr.get('merged')) is not bool:
                raise ValueError('incomplete PR state')
            if pr['state']!='closed' or not pr['merged']:
                dispositions.append({'number':number,'state':'not_merged'});continue
            merged_at=_stamp(pr.get('merged_at'))
            if merged_at<activated:
                dispositions.append({'number':number,'state':'before_deployment'});continue
            actor=pr.get('merged_by') or {}
            if (pr['base'].get('ref')!='main' or actor.get('login')!='github-actions[bot]' or actor.get('type')!='Bot'):
                dispositions.append({'number':number,'state':'not_gate_merge'});continue
            candidates.append({'number':number,'source':'post_deployment_gate_merge','pr':pr})
        except Exception as error:
            # A missing/failed record stays visible and is scanned on the next wake.
            # It is never classified as "no dispatch" or permission to retry.
            unresolved.append({'number':number,'error_type':type(error).__name__,'reason':str(error)[:1000]})
    return {'repository':repo,'baseline':dict(baseline),'enumerated':numbers,'candidates':candidates,
        'unresolved':unresolved,'dispositions':dispositions,'enumeration_complete':True,
        'dispatch_authorized':False,'scan_policy':'complete state=all; no time watermark'}

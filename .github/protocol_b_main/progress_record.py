"""Authenticate a compact recovery progress record before skipping old discovery.

A cursor records which history was enumerated, not which proof was accepted.
Every pending PR and original uncertain executor remains explicit. This record
cannot authorize a dispatch; the actual App, intent and workflow records still
have to be re-read. Incomplete or invalid discovery stops preparation. Only a complete search
back to the deployment baseline permits the initial state to be reconstructed.
"""
import datetime
import hashlib
import json
from urllib.parse import quote
from deferred_artifact import MAX_ZIP
from discover_deferred import pages
from discover_intents import JOB, DISPATCH, WORKFLOW, _ancestor, _record, require, SHA
from run_windows import stamp

NAME='protocol-b-main-progress'
PREPARE='Prepare main-check dispatch intents'
UPLOAD='Persist main-check recovery progress'


def checkpoint_name(started_at):
    day=datetime.datetime.fromtimestamp(stamp(started_at),datetime.timezone.utc).strftime('%Y%m%d')
    return NAME+'-'+day


def baseline_digest(baseline):
    return hashlib.sha256(json.dumps(baseline,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def validate_progress(value,repo,baseline,publisher,artifact):
    require(value.get('repository')==repo and value.get('baseline_sha256')==baseline_digest(baseline),
            'progress repository or deployment baseline')
    require(value.get('dispatch_authorized') is False,'progress is not dispatch authority')
    history=value.get('history')
    require(isinstance(history,dict) and history.get('schema')=='main-check-history/v1'
            and history.get('repository')==repo and history.get('activation_commit')==baseline['activation_commit'],
            'progress history binding')
    require(isinstance(history.get('frontier'),str) and SHA.fullmatch(history['frontier']),
            'progress history frontier')
    require((history.get('scan_head') is None)==(history.get('next_commit') is None),'partial progress history')
    if history.get('scan_head') is not None:
        require(all(isinstance(history.get(k),str) and SHA.fullmatch(history[k])
                    for k in ('scan_head','next_commit')),'progress history identities')
    pending=value.get('pending_prs')
    require(isinstance(pending,list) and len(pending)<=1000
            and all(type(n) is int and n>0 for n in pending) and len(pending)==len(set(pending)),
            'progress pending PR identities')
    executions=value.get('executions')
    require(isinstance(executions,list) and len(executions)<=1000,'progress execution count')
    identities=[]
    for entry in executions:
        require(isinstance(entry,dict) and set(entry)=={'run','attempt'}
                and type(entry['run']) is int and entry['run']>0
                and type(entry['attempt']) is int and 1<=entry['attempt']<=32,'progress executor identity')
        identities.append((entry['run'],entry['attempt']))
    require(len(identities)==len(set(identities)),'duplicate progress executor')
    # This upload precedes dispatch. The next wake must investigate this very
    # execution even if it dies after sending a request but before saving a result.
    require((publisher['id'],publisher['run_attempt']) in identities,'progress omitted its own unfinished execution')
    anchor=value.get('run_anchor')
    require(isinstance(anchor,dict) and set(anchor)=={'run','number'}
            and all(type(anchor[k]) is int and anchor[k]>0 for k in anchor)
            and anchor['number']>=publisher['run_number'],'progress workflow anchor')
    sequence=value.get('run_sequence')
    require(isinstance(sequence,dict) and type(sequence.get('frontier')) is int
            and baseline['workflow_run_number']<=sequence['frontier']<anchor['number'],
            'progress run-number frontier')
    partial=sequence.get('partial')
    if partial is not None:
        require(isinstance(partial,dict) and partial.get('frontier')==sequence['frontier']
                and type(partial.get('target')) is int
                and sequence['frontier']<=partial['target']<anchor['number']
                and type(partial.get('next_page')) is int and partial['next_page']>=1
                and isinstance(partial.get('records'),list) and len(partial['records'])<=10000,
                'partial run-number frontier')
    searches=value.get('existing_searches',{})
    require(isinstance(searches,dict) and len(searches)<=2000,'existing search count')
    from existing_search import validate_cursor
    from dispatch_intents import operation_key
    for key,search in searches.items():
        require(isinstance(search,dict) and isinstance(search.get('operation'),dict),'existing search record')
        operation=search['operation']
        require(operation.get('repository')==repo and operation.get('number') in pending
                and key==operation_key(operation),'existing search ownership')
        validate_cursor(search,operation,search.get('merged_at'),search.get('exact_release'),
                        search.get('workflow_id'),stamp(search.get('through')))
    return value


def read_progress(api,repo,artifact_id,baseline,current_main):
    require(type(artifact_id) is int and artifact_id>0,'progress artifact ID')
    metadata=api.json('')
    require(metadata.get('full_name')==repo and metadata.get('default_branch')=='main'
            and type(metadata.get('id')) is int and metadata['id']>0,'progress repository identity')
    artifact=api.json('actions/artifacts/'+str(artifact_id))
    require(artifact.get('id')==artifact_id and isinstance(artifact.get('name'),str) and artifact['name'].startswith(NAME+'-')
            and artifact.get('expired') is False,'progress artifact identity or expiry')
    require(type(artifact.get('size_in_bytes')) is int and 0<artifact['size_in_bytes']<=MAX_ZIP,
            'progress artifact size')
    binding=artifact.get('workflow_run') or {};rid=binding.get('id')
    require(type(rid) is int and rid>0,'progress publisher ID')
    latest=api.json('actions/runs/'+str(rid))
    require(latest.get('id')==rid and type(latest.get('run_attempt')) is int
            and latest['run_attempt']>=1,'progress latest run identity')
    # Recovery dispatch is first-attempt-only. A rerun cannot create a new
    # effect behind an old created-at cursor. Preserve the original attempt.
    original=latest if latest['run_attempt']==1 else api.json(f'actions/runs/{rid}/attempts/1')
    require(original.get('id')==rid and original.get('run_attempt')==1
            and type(original.get('workflow_id')) is int and original['workflow_id']>0
            and type(original.get('run_number')) is int and original['run_number']>0
            and (original.get('repository') or {}).get('full_name')==repo
            and (original.get('repository') or {}).get('id')==metadata['id']
            and (original.get('head_repository') or {}).get('id')==metadata['id']
            and original.get('head_branch')=='main' and original.get('path')==WORKFLOW
            and original.get('event') in ('schedule','workflow_run'),'untrusted progress publisher')
    _ancestor(api,baseline['activation_commit'],original.get('head_sha'))
    _ancestor(api,original['head_sha'],current_main)
    jobs=pages(api,f'actions/runs/{rid}/attempts/1/jobs','jobs',identity='id')
    found=[j for j in jobs if j.get('name')==JOB]
    require(len(found)==1,'progress recovery job')
    job=found[0]
    require(job.get('run_id')==rid and job.get('run_attempt')==1 and job.get('status')=='completed',
            'progress executor is not terminal')
    started=stamp(job.get('started_at'));completed=stamp(job.get('completed_at'))
    require(started<=stamp(artifact.get('created_at'))<=completed,'progress upload outside original job')
    require(artifact['name']==checkpoint_name(job['started_at']),'progress job-date bucket')
    steps=job.get('steps');require(isinstance(steps,list),'progress job steps')
    selected=[]
    for name in (PREPARE,UPLOAD,DISPATCH):
        matches=[s for s in steps if s.get('name')==name]
        require(len(matches)==1 and type(matches[0].get('number')) is int,'progress step identity')
        selected.append(matches[0])
    prepared,uploaded,dispatch=selected
    require(all(s.get('status')=='completed' and s.get('conclusion')=='success' for s in (prepared,uploaded))
            and prepared['number']<uploaded['number']<dispatch['number'],'progress was not uploaded before dispatch')
    record=_record(api.bytes(f'actions/artifacts/{artifact_id}/zip'),artifact,original,metadata['id'],
                   'progress',expected_name=artifact['name'])
    validate_progress(record,repo,baseline,original,artifact)
    anchor=record['run_anchor'];actual_anchor=api.json('actions/runs/'+str(anchor['run']))
    require(actual_anchor.get('id')==anchor['run'] and actual_anchor.get('run_number')==anchor['number']
            and actual_anchor.get('workflow_id')==original['workflow_id']
            and (actual_anchor.get('repository') or {}).get('id')==metadata['id']
            and (actual_anchor.get('repository') or {}).get('full_name')==repo
            and stamp(actual_anchor.get('created_at'))<=started,'progress workflow anchor binding')
    return {'record':record,'publisher':original,'job':job,
            'artifact':{'id':artifact_id,'digest':artifact['digest'],'name':artifact['name'],
                        'created_at':artifact['created_at']},'dispatch_authorized':False}


def latest_progress(api,repo,baseline,current_main,*,current_job,candidate_limit=3,max_days=14,max_pages=3):
    """Find progress by actual execution date, never artifact ID or run number.

    The serialized job uploads once, before dispatch. Its original start date
    determines the name. A complete date bucket is sorted by GitHub's upload
    timestamp; original job times authenticate that ordering. Equal timestamps,
    incomplete pages, failed authentication and bounded-out searches stop the
    preparation rather than silently resetting the retained queue.
    """
    require(type(candidate_limit) is int and 1<=candidate_limit<=20,'progress candidate bound')
    require(type(max_days) is int and 1<=max_days<=14,'progress date bound')
    require(type(max_pages) is int and 1<=max_pages<=3,'progress page bound')
    current_start=stamp(current_job.get('started_at'))
    day=datetime.datetime.fromtimestamp(current_start,datetime.timezone.utc).date()
    activated=datetime.datetime.fromisoformat(baseline['activated_at'].replace('Z','+00:00'))
    require(activated.utcoffset() is not None,'progress baseline date timezone')
    first_day=activated.astimezone(datetime.timezone.utc).date()
    require(first_day<=day,'progress baseline is after executor start')
    searched=[]
    def result(progress=None,reason=None):
        return {'progress':progress,'discovery_complete':reason is None,
                'unresolved':[] if reason is None else [{'reason':reason}],
                'searched_buckets':searched,'dispatch_authorized':False}
    try:
        for offset in range(max_days):
            current_day=day-datetime.timedelta(days=offset)
            name=NAME+'-'+current_day.strftime('%Y%m%d');searched.append(name)
            listed=[];seen=set();total=None
            for page in range(1,max_pages+1):
                value=api.json('actions/artifacts?name='+quote(name)+'&per_page=100&page='+str(page))
                chunk=value.get('artifacts');count=value.get('total_count')
                require(type(count) is int and count>=0 and isinstance(chunk,list),'progress bucket response')
                require(total is None or count==total,'progress bucket changed during pagination')
                total=count
                require(total<=100*max_pages,'progress bucket exceeds page bound')
                require(len(chunk)==min(100,max(0,total-100*(page-1))),'incomplete progress bucket page')
                for artifact in chunk:
                    require(isinstance(artifact,dict) and type(artifact.get('id')) is int
                            and artifact['id']>0 and artifact['id'] not in seen
                            and artifact.get('name')==name,'progress bucket artifact identity')
                    stamp(artifact.get('created_at'))
                    seen.add(artifact['id']);listed.append(artifact)
                if len(listed)==total:break
            require(len(listed)==total,'incomplete progress bucket enumeration')
            if listed:
                latest=max(stamp(a['created_at']) for a in listed)
                tied=[a for a in listed if stamp(a['created_at'])==latest]
                require(len(tied)<=candidate_limit,'progress timestamp tie exceeds authentication bound')
                candidates=[]
                for artifact in tied:
                    loaded=read_progress(api,repo,artifact['id'],baseline,current_main)
                    require(loaded['artifact']['name']==name
                            and loaded['artifact']['created_at']==artifact['created_at'],
                            'progress ordering metadata changed')
                    job=loaded['job']
                    require(stamp(job['completed_at'])<=current_start,'progress executor overlaps current job')
                    candidates.append(loaded)
                require(len(candidates)==1,'ambiguous same-second progress uploads; retain original executions')
                return result(candidates[0])
            if current_day==first_day:
                value=result();value['fallback']='Complete empty discovery since deployment; reconstruct the baseline.'
                return value
        return result(reason='Progress discovery exceeded the date bound; retained state was not reset.')
    except Exception as error:
        return result(reason=type(error).__name__+': '+str(error)[:1000])

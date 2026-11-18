"""Dispatch only from an authenticated, already-uploaded intent; no write retries.

The API transport must implement post_once with
no automatic retry. persist must durably replace the local results file; the
workflow uploads that file in a final step even when this function fails.
"""
import copy
import datetime
from discover_intents import discover_recovery_intents, require, DISPATCH, _ancestor, SHA
from prepare_recovery import main_tip, existing_evidence
from revalidate_operations import revalidate_operations
from read_budget import BoundedReads
from github_api import GitHubResponseError
from discover_deferred import discover_deferred
from release_transition import release_transition


def dispatch_recovery(api, repo, baseline, *, program_commit, recovery_run, recovery_attempt, persist):
    require(type(recovery_attempt) is int and recovery_attempt==1, 'recovery dispatch is first-attempt-only')
    api=BoundedReads(api,60)
    main=main_tip(api)
    original=discover_recovery_intents(api,repo,recovery_run,recovery_attempt,
        activation_commit=baseline['activation_commit'],current_main=main)
    publisher=original['publisher'];job=original['job']
    require(publisher['head_sha']==program_commit and publisher.get('status')=='in_progress'
            and job.get('status')=='in_progress','not the current running recovery execution')
    steps=[s for s in job.get('steps',[]) if s.get('name')==DISPATCH]
    require(len(steps)==1 and steps[0].get('status')=='in_progress','dispatcher step is not active')
    require(not original['artifacts'].get('results') and
            all(x['receipt'] is None for x in original['operations'].values()),'execution already has results; reconcile, never replay')
    repository_id=original['plan']['repository_id']
    require(type(repository_id) is int and repository_id>0,'original repository identity')
    result={'schema':'main-check-results/v1','repository':repo,'repository_id':repository_id,
        'recovery_run':recovery_run,'recovery_attempt':recovery_attempt,'program_commit':program_commit,
        'created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'receipts':[]}
    for key,item in original['operations'].items():
        op=item['intent']['operation']
        result['receipts'].append({'schema':'main-check-receipt/v1','operation_key':key,
            'recovery_run':recovery_run,'recovery_attempt':recovery_attempt,'status':'not_sent',
            'request_sent':False,'merge_commit_sha':op['merge'],'workflow':op['workflow'],
            'reason':'Fresh validation has not reached a request boundary'})
    def save():persist(copy.deepcopy(result))
    # Preserve known absence before bounded reads. A validation failure or cap
    # must not leave a started dispatcher with no account of its unsent intents.
    save()
    try:
        fresh=revalidate_operations(api,repo,baseline,original,program_commit=program_commit,
            recovery_run=recovery_run,recovery_attempt=recovery_attempt)
        require(fresh['repository']==repo and fresh['repository_id']==repository_id
                and fresh['recovery_run']==recovery_run and fresh['recovery_attempt']==recovery_attempt
                and fresh['program_commit']==program_commit,'fresh plan identity')
    except Exception as error:
        for receipt in result['receipts']:
            receipt['reason']='Fresh validation failed before any request: '+str(error)[:850]
        save()
        raise
    allowed={x['operation_key']:x for x in fresh['operations']}
    for (key,item),receipt in zip(original['operations'].items(),result['receipts']):
        intent=item['intent'];op=intent['operation']
        receipt.pop('reason',None)
        # Everything before the send boundary is read-only and can report known absence.
        try:
            api.fresh()  # Live readiness is re-read for each one-shot dispatch.
            require(key in allowed,'not in the freshly reconciled plan')
            current=allowed[key]
            require(current['operation']==op and intent.get('source')==current['source'] and intent.get('exact_release')==current['exact_release'],
                    'source acceptance or release classification changed')
            source=discover_deferred(api,repo,op['number']);pr=source['pr']
            require(source.get('eligible') is True and pr.get('merged') is True and pr.get('state')=='closed'
                    and pr['merge_commit_sha']==op['merge'] and pr['head']['sha']==op['head']
                    and (pr.get('merged_by') or {}).get('login')=='github-actions[bot]'
                    and (pr.get('merged_by') or {}).get('type')=='Bot','deferred merge is no longer bound')
            require(source['accepted']['check']['id']==intent['source']['accepted_check']
                    and source['accepted']['publisher']['id']==intent['source']['accepted_run']
                    and source['requester']['publisher']['id']==intent['source']['requester_run'],
                    'changed accepted/requesting execution')
            tip=main_tip(api);_ancestor(api,op['merge'],tip)
            transition=release_transition(api,op['merge'])
            require(transition['exact_release_required']==intent['exact_release'],'changed release transition')
            existing=existing_evidence(api,op,pr['merged_at'],tip,intent['exact_release'],
                cursor=fresh.get('existing_searches',{}).get(key))
            receipt['observed_main']=tip;receipt['existing']=existing['classification']
            require(existing['classification']['state']=='no_confirmed_run_check_intents','actual main checks already exist or need attention')
            require(not intent['exact_release'] or tip==op['merge'],'exact release commit is no longer main')
            # The response still needs its actual run and possibly a new main
            # ancestry read. Do not send when our own cap would prevent those.
            require(api.remaining>=2,'Insufficient read budget to verify the response; retain this operation')
        except Exception as error:
            receipt['reason']=str(error)[:1000];save();continue
        # Persist the uncertain boundary BEFORE the only POST. If the process or
        # network dies, neither this code nor a later recovery guesses absence.
        receipt.update(status='sending',request_sent=None)
        save()
        try:
            response=api.post_once('actions/workflows/'+op['workflow']+'/dispatches',
                                   {'ref':'main','return_run_details':True})
            receipt.update(status='response_received',request_sent=True,response=response)
            ident=(response or {}).get('workflow_run_id')
            if type(ident) is int and ident>0:receipt['workflow_run_id']=ident
            save()
            require(type(ident) is int and ident>0,'dispatch response has no run ID; do not retry')
            run=api.json('actions/runs/'+str(ident))
            receipt['run']={k:run.get(k) for k in ('id','head_sha','head_branch','event','path','html_url','status','conclusion')}
            sha=run.get('head_sha')
            require(run.get('id')==ident and run.get('event')=='workflow_dispatch'
                    and run.get('head_branch')=='main'
                    and run.get('path') in ('.github/workflows/'+op['workflow'],'.github/workflows/'+op['workflow']+'@main')
                    and (run.get('repository') or {}).get('full_name')==repo
                    and (run.get('head_repository') or {}).get('full_name')==repo
                    and isinstance(sha,str) and SHA.fullmatch(sha),'returned run identity mismatch; do not retry')
            _ancestor(api,op['merge'],sha)
            receipt.update(status='run_confirmed',head_sha=sha,head_differs_from_merge=sha!=op['merge'],
                           exact_release_covered=(not intent['exact_release'] or sha==op['merge']))
            if intent['exact_release'] and sha!=op['merge']:
                receipt['attention']='Main advanced during dispatch; this run does not verify the exact release commit.'
        except Exception as error:
            receipt.update(status='effect_needs_reconciliation',error=str(error)[:1000])
            if isinstance(error, GitHubResponseError):
                receipt['response_evidence'] = error.response_evidence
            # Even a 4xx response is not reclassified as known absence here.
            # No automatic retry can be justified merely by an error status.
        save()
    return result

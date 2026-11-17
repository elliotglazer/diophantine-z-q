"""Read-only preparation of deferred main checks, with every prior effect reconciled."""
import datetime
from urllib.parse import quote
from discover_deferred import pages, discover_deferred
from discover_queue import discover_queue
from enumerate_intents import enumerate_recovery_intents
from dispatch_intents import operation_key, reconcile_intent
from existing_runs import classify_existing_runs
from release_transition import release_transition
from discover_intents import require, SHA, _ancestor

WORKFLOWS=('research-checks.yml','kernel-lean.yml')


def main_tip(api):
    ref=api.json('git/ref/heads/main')
    sha=(ref.get('object') or {}).get('sha')
    require(ref.get('ref')=='refs/heads/main' and (ref.get('object') or {}).get('type')=='commit'
            and isinstance(sha,str) and SHA.fullmatch(sha), 'main commit identity')
    return sha


def existing_evidence(api, operation, merged_at, observed_main, exact_release):
    path='actions/workflows/'+operation['workflow']+'/runs?branch=main&created='+quote('>='+merged_at,safe='')
    runs=pages(api,path,'workflow_runs',identity='id')
    comparisons={}
    for run in runs:
        head=run.get('head_sha')
        if isinstance(head,str) and SHA.fullmatch(head) and head!=operation['merge'] and not exact_release:
            comparisons[head]=api.json(f"compare/{operation['merge']}...{head}")
    state=classify_existing_runs(operation,runs,comparisons,merged_at=merged_at,
        observed_main=observed_main,exact_release=exact_release,enumeration_complete=True)
    return {'classification':state,'runs':runs}


def prepare_recovery(api, repo, baseline, *, program_commit, recovery_run, recovery_attempt, limit=100):
    """Produce only a plan. A successful artifact upload and fresh checks precede writes."""
    require(isinstance(program_commit,str) and SHA.fullmatch(program_commit), 'program commit')
    require(type(recovery_run) is int and recovery_run>0 and type(recovery_attempt) is int and recovery_attempt>0,
            'recovery execution identity')
    require(type(limit) is int and 1<=limit<=100,'operation bound')
    observed=main_tip(api)
    previous=enumerate_recovery_intents(api,repo,baseline,observed,
        current_execution=(recovery_run,recovery_attempt))
    queue=discover_queue(api,repo,baseline,pending_numbers=previous['pending_numbers'])
    prior={}
    for execution in previous['executions']:
        for key,item in execution['operations'].items():
            prior.setdefault(key,[]).append((execution,item))
    plans=[];states=[];unresolved=list(queue['unresolved'])
    for candidate in queue['candidates']:
        pr=candidate['pr']; number=candidate['number']
        try:
            require(pr.get('merged') is True and pr.get('state')=='closed'
                    and (pr.get('base') or {}).get('ref')=='main', 'retained PR is not a confirmed merge')
            merge=pr.get('merge_commit_sha');head=(pr.get('head') or {}).get('sha')
            require(all(isinstance(s,str) and SHA.fullmatch(s) for s in (merge,head)), 'merged PR commit identity')
            _ancestor(api,merge,observed)
            transition=release_transition(api,merge)
            for workflow in WORKFLOWS:
                operation={'repository':repo,'number':number,'head':head,'merge':merge,'workflow':workflow,'ref':'main'}
                key=operation_key(operation)
                try:
                    evidence=existing_evidence(api,operation,pr['merged_at'],observed,transition['exact_release_required'])
                    classified=evidence['classification']
                    state={'operation':operation,'operation_key':key,'existing':classified,
                           'release_transition':transition,'prior_executions':[]}
                    states.append(state)
                    if classified['state']!='no_confirmed_run_check_intents':
                        continue
                    if previous['unlocated_effects']:
                        state['blocked']='unlocated_prior_dispatch_effect';continue
                    for execution,item in prior.get(key,[]):
                        result=reconcile_intent(operation,item['intent'],item['receipt'],execution['job'],
                            dispatch_step=execution['dispatch_step'],current_runs=evidence['runs'],enumeration_complete=True,
                            results_persisted_after_dispatch=execution.get('results_persisted_after_dispatch',False))
                        state['prior_executions'].append(result)
                    if any(not result['safe_absence'] for result in state['prior_executions']):
                        state['blocked']='prior_dispatch_not_proved_absent';continue
                    # Re-read actual PR/App publications; file contents and event payloads are not authority.
                    source=discover_deferred(api,repo,number)
                    require(source.get('eligible') is True,'no authenticated deferred merge')
                    actual=source['pr']
                    require(actual.get('merge_commit_sha')==merge and actual['head']['sha']==head,'merge changed during preparation')
                    require((actual.get('merged_by') or {}).get('login')=='github-actions[bot]'
                            and (actual.get('merged_by') or {}).get('type')=='Bot','not a gate merge')
                    if len(plans)>=limit:
                        state['blocked']='next_batch';continue
                    intent={'schema':'main-check-intent/v1','operation_key':key,'operation':operation,
                        'request':{'ref':'main','return_run_details':True},'recovery_run':recovery_run,
                        'recovery_attempt':recovery_attempt,'planned_main':observed,
                        'exact_release':transition['exact_release_required'],
                        'source':{'accepted_check':source['accepted']['check']['id'],
                                  'accepted_run':source['accepted']['publisher']['id'],
                                  'requester_run':source['requester']['publisher']['id']}}
                    plans.append(intent);state['planned']=True
                except Exception as error:
                    unresolved.append({'number':number,'workflow':workflow,'error_type':type(error).__name__,'reason':str(error)[:1000]})
        except Exception as error:
            unresolved.append({'number':number,'error_type':type(error).__name__,'reason':str(error)[:1000]})
    metadata=api.json('')
    require(metadata.get('full_name')==repo and type(metadata.get('id')) is int,'repository identity')
    return {'schema':'main-check-intents/v1','repository_id':metadata['id'],'repository':repo,
        'recovery_run':recovery_run,'recovery_attempt':recovery_attempt,'program_commit':program_commit,
        'observed_main':observed,'created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'operations':plans,'observations':states,'unresolved':unresolved,
        'prior_execution_errors':previous['unresolved'],'dispatch_authorized':False}

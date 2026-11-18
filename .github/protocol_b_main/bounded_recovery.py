"""Resumable read-only preparation. Progress never substitutes for acceptance."""
import datetime
import copy
from discover_intents import require,WORKFLOW
from enumerate_intents import enumerate_recovery_intents
from dispatch_intents import confirmed_inert_execution
from history_queue import discover_main_history
from progress_record import latest_progress,baseline_digest
from read_budget import BoundedReads,ReadBudgetExceeded
from run_sequence import scan_run_sequence


def prepare_bounded(raw_api,repo,baseline,*,program_commit,recovery_run,recovery_attempt,limit=4,now=None):
    from prepare_recovery import main_tip,plan_recovery
    require(recovery_attempt==1,'bounded recovery is first-attempt-only')
    api=BoundedReads(raw_api,60)
    observed=main_tip(api);metadata=api.json('')
    require(metadata.get('full_name')==repo and type(metadata.get('id')) is int,'repository identity')
    loaded=latest_progress(api,repo,baseline,observed,candidate_limit=3)
    old=loaded['progress']['record'] if loaded['progress'] else None
    order=list(old['pending_prs'] if old else [])
    pending=set(order)
    execution_order=[item['run'] for item in old['executions']] if old else []
    execution_ids=set(execution_order)
    errors=[]
    # Do not discover work faster than a bounded wake can reconcile it.
    if old and len(pending)>=40:
        history={'cursor':old['history'],'candidates':[],'unresolved':[],
                 'enumeration_complete':False}
    else:
        history=discover_main_history(api,repo,baseline['activation_commit'],observed,
                cursor=old['history'] if old else None,max_commits=4)
    for candidate in history['candidates']:
        if candidate['number'] not in pending:order.append(candidate['number'])
        pending.add(candidate['number'])
    errors.extend(history['unresolved'])
    workflow=api.json('actions/workflows/protocol-b.yml')
    require(workflow.get('path')==WORKFLOW and type(workflow.get('id')) is int,'recovery workflow identity')
    anchor=api.json('actions/runs/'+str(baseline['workflow_run_id']))
    require(anchor.get('id')==baseline['workflow_run_id']
            and anchor.get('workflow_id')==workflow['id']
            and anchor.get('run_number')==baseline['workflow_run_number']
            and (anchor.get('repository') or {}).get('full_name')==repo,'workflow sequence baseline')
    actual=api.json('actions/runs/'+str(recovery_run))
    require(actual.get('id')==recovery_run and actual.get('run_attempt')==1
            and actual.get('head_sha')==program_commit and actual.get('head_branch')=='main'
            and actual.get('workflow_id')==workflow['id'] and actual.get('path')==WORKFLOW
            and (actual.get('repository') or {}).get('full_name')==repo
            and (actual.get('repository') or {}).get('id')==metadata['id']
            and (actual.get('head_repository') or {}).get('id')==metadata['id']
            and actual.get('event') in ('schedule','workflow_run')
            and type(actual.get('run_number')) is int and actual['run_number']>baseline['workflow_run_number'],
            'current recovery sequence identity')
    sequence=old['run_sequence'] if old else {'frontier':baseline['workflow_run_number'],'partial':None}
    partial=sequence['partial']
    target=partial['target'] if partial else actual['run_number']-1
    if len(execution_ids)>=40:
        scan={'runs':[],'new_runs':[],'enumeration_complete':False,
              'partial':partial,'unresolved':[]}
    else:
        scan=scan_run_sequence(api,workflow['id'],sequence['frontier'],target,partial=partial,max_pages=3)
    errors.extend(scan['unresolved'])
    for run in scan.get('new_runs',scan['runs']):
        if run.get('event') in ('schedule','workflow_run') and run.get('head_branch')=='main':
            if run['id'] not in execution_ids:execution_order.append(run['id'])
            execution_ids.add(run['id'])
    new_frontier=target if scan['enumeration_complete'] else sequence['frontier']
    # The current execution must never be confused with an earlier dispatcher.
    execution_ids.discard(recovery_run)
    execution_order=[rid for rid in execution_order if rid!=recovery_run]
    selected_executions=execution_order[:8]
    deferred_executions=execution_order[8:]
    previous=enumerate_recovery_intents(api,repo,baseline,observed,
        current_execution=(recovery_run,recovery_attempt),run_ids=selected_executions)
    for number in previous['pending_numbers']:
        if number not in pending:order.append(number)
        pending.add(number)
    # Retain every unresolved executor, even when it has no readable intent.
    retained_exec=set(deferred_executions)|{item['run'] for item in previous['unresolved']}
    for execution in previous['executions']:retained_exec.add(execution['publisher']['id'])
    incomplete=(not scan['enumeration_complete'] or new_frontier!=actual['run_number']-1
                or bool(previous['unresolved']) or bool(deferred_executions))
    if incomplete:previous['unlocated_effects']=True
    candidates=[]
    attempted=[]
    for number in order:
        if len(candidates)>=2 or api.remaining<12:break
        attempted.append(number)
        try:
            pr=api.json('pulls/'+str(number))
            require(pr.get('number')==number and ((pr.get('base') or {}).get('repo') or {}).get('full_name')==repo,
                    'retained PR identity')
            candidates.append({'number':number,'pr':pr})
        except Exception as error:
            errors.append({'number':number,'reason':str(error)[:1000],'error_type':type(error).__name__})
    queue={'candidates':candidates,'unresolved':errors}
    plan=plan_recovery(api,repo,baseline,program_commit=program_commit,recovery_run=recovery_run,
        recovery_attempt=recovery_attempt,observed=observed,previous=previous,queue=queue,limit=limit,
        searches=copy.deepcopy(old.get('existing_searches',{})) if old else {})
    observations=plan['observations']
    for candidate in candidates:
        number=candidate['number'];states=[x for x in observations if x['operation']['number']==number]
        if len(states)==2 and all(x['existing']['state']=='verification_passed' for x in states):
            pending.discard(number)
    # Retire a run only after every original attempt is accounted for. One
    # inert attempt must not erase another attempt's missing receipt. An
    # authenticated all-not-sent result can retire its executor while the PR
    # remains queued, avoiding repeated reads of known-absent effects.
    unresolved_ids={item['run'] for item in previous['unresolved']}
    by_run={}
    for execution in previous['executions']:
        by_run.setdefault(execution['publisher']['id'],[]).append(execution)
    for rid,executions in by_run.items():
        if rid in unresolved_ids:continue
        removable=True
        for execution in executions:
            numbers={item['intent']['operation']['number'] for item in execution['operations'].values()}
            if not (execution['executor_terminal'] and
                    (numbers.isdisjoint(pending) or confirmed_inert_execution(execution))):
                removable=False
        if removable:retained_exec.discard(rid)
    retained_exec.add(recovery_run)
    # Rotate unresolved executors too; one lost receipt must not prevent the
    # remaining original processes from being investigated.
    retained_order=[rid for rid in deferred_executions+selected_executions if rid in retained_exec]
    retained_order += sorted(retained_exec-set(retained_order)-{recovery_run})
    retained_order.append(recovery_run)
    progress={'schema':'main-check-progress/v1','repository':repo,'repository_id':metadata['id'],
        'recovery_run':recovery_run,'recovery_attempt':recovery_attempt,'program_commit':program_commit,
        'baseline_sha256':baseline_digest(baseline),'dispatch_authorized':False,
        'history':history['cursor'],'pending_prs':[n for n in order if n in pending and n not in attempted]+[n for n in attempted if n in pending],
        'executions':[{'run':rid,'attempt':1} for rid in retained_order],
        'run_sequence':{'frontier':new_frontier,'partial':scan['partial']},
        'existing_searches':{key:value for key,value in plan.get('existing_searches',{}).items()
                             if value['operation']['number'] in pending}}
    plan['progress']=progress
    plan['discovery']={'reads':api.count,'read_limit':api.limit,
        'progress_artifact':loaded['progress']['artifact'] if loaded['progress'] else None,
        'progress_errors':loaded['unresolved'],'history_complete':history['enumeration_complete'],
        'run_sequence_complete':not incomplete,'retained_executions':retained_order,
        'deferred_executions':deferred_executions}
    return plan

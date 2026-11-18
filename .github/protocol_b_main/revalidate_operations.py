"""Recheck the uploaded operation set without scanning all repository history."""
import copy
from discover_intents import require
from enumerate_intents import enumerate_recovery_intents
from dispatch_intents import reconcile_intent


def revalidate_operations(api,repo,baseline,original,*,program_commit,recovery_run,recovery_attempt):
    from prepare_recovery import main_tip,existing_evidence
    plan=original['plan'];discovery=plan.get('discovery') or {}
    require(plan.get('repository')==repo and plan.get('recovery_run')==recovery_run
            and plan.get('recovery_attempt')==recovery_attempt and plan.get('program_commit')==program_commit,
            'uploaded plan execution identity')
    require(discovery.get('run_sequence_complete') is True,'uploaded plan has incomplete recovery discovery')
    prior_ids=discovery.get('retained_executions')
    require(isinstance(prior_ids,list) and len(prior_ids)<=1000
            and all(type(rid) is int and rid>0 for rid in prior_ids), 'uploaded prior execution identities')
    prior_ids=[rid for rid in prior_ids if rid!=recovery_run]
    tip=main_tip(api)
    previous=enumerate_recovery_intents(api,repo,baseline,tip,
        current_execution=(recovery_run,recovery_attempt),run_ids=prior_ids)
    require(not previous['unresolved'] and not previous['unlocated_effects'],
            'earlier recovery effect still unresolved')
    searches=copy.deepcopy(plan.get('existing_searches',{}))
    allowed=[]
    for key,item in original['operations'].items():
        intent=item['intent'];op=intent['operation']
        pr=api.json('pulls/'+str(op['number']))
        require(pr.get('number')==op['number'] and pr.get('merge_commit_sha')==op['merge']
                and (pr.get('head') or {}).get('sha')==op['head'],'planned PR identity changed')
        evidence=existing_evidence(api,op,pr['merged_at'],tip,intent['exact_release'],cursor=searches.get(key))
        if 'search' in evidence:searches[key]=evidence['search']
        if evidence['classification']['state']!='no_confirmed_run_check_intents':continue
        safe=True
        for execution in previous['executions']:
            prior=execution['operations'].get(key)
            if prior is None:continue
            result=reconcile_intent(op,prior['intent'],prior['receipt'],execution['job'],
                dispatch_step=execution['dispatch_step'],current_runs=evidence['runs'],enumeration_complete=True,
                results_persisted_after_dispatch=execution.get('results_persisted_after_dispatch',False))
            if not result['safe_absence']:safe=False
        if safe:allowed.append(intent)
    return {'repository':repo,'repository_id':plan['repository_id'],'recovery_run':recovery_run,
            'recovery_attempt':recovery_attempt,'program_commit':program_commit,'operations':allowed,
            'existing_searches':searches}

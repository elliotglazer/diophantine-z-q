"""Enumerate original recovery executions without guessing that missing means absent.

This GET-only module feeds authenticated intents to the planner; it
cannot dispatch. Unlocated effects are retained as global unresolved evidence.
"""
from urllib.parse import quote
from discover_deferred import pages
from discover_intents import JOB, DISPATCH, WORKFLOW, discover_recovery_intents, require
from discover_queue import _stamp


def enumerate_recovery_intents(api, repo, baseline, current_main, *, current_execution=None):
    require(isinstance(baseline,dict) and baseline.get('schema')=='main-check-baseline/v1'
            and baseline.get('repository')==repo, 'deployment baseline')
    activated=_stamp(baseline.get('activated_at'))
    anchor=baseline.get('activation_commit')
    workflow=api.json('actions/workflows/protocol-b.yml')
    require(type(workflow.get('id')) is int and workflow['id']>0
            and workflow.get('path')==WORKFLOW, 'recovery workflow identity')
    path=f"actions/workflows/{workflow['id']}/runs?branch=main&created="+quote('>='+baseline['activated_at'],safe='')
    runs=pages(api,path,'workflow_runs',identity='id')
    recovered=[];unresolved=[];excluded=[]
    for listed in runs:
        rid=listed['id']
        try:
            run=api.json(f'actions/runs/{rid}')
            require(run.get('id')==rid and run.get('workflow_id')==workflow['id']
                    and (run.get('repository') or {}).get('full_name')==repo
                    and run.get('path')==WORKFLOW, 'listed recovery run identity')
            if run.get('head_branch')!='main' or run.get('event') not in ('schedule','workflow_run'):
                excluded.append({'run':rid,'reason':'not_a_recovery_trigger'});continue
            if _stamp(run.get('created_at'))<activated:
                excluded.append({'run':rid,'reason':'before_deployment_time'});continue
            latest=run.get('run_attempt')
            require(type(latest) is int and 1<=latest<=32, 'original recovery attempt bound')
            artifacts=pages(api,f'actions/runs/{rid}/artifacts','artifacts',identity='id')
            for attempt in range(1,latest+1):
                if current_execution==(rid,attempt):
                    excluded.append({'run':rid,'attempt':attempt,'reason':'current_preparation'});continue
                try:
                    original=run if attempt==latest else api.json(f'actions/runs/{rid}/attempts/{attempt}')
                    require(original.get('id')==rid and original.get('run_attempt')==attempt,'original attempt identity')
                    jobs=pages(api,f'actions/runs/{rid}/attempts/{attempt}/jobs','jobs',identity='id')
                    candidates=[j for j in jobs if j.get('name')==JOB]
                    matching=[a for a in artifacts if a.get('name') in
                        (f'protocol-b-main-intents-{rid}-{attempt}',f'protocol-b-main-results-{rid}-{attempt}')]
                    require(len(candidates)<=1,'ambiguous original recovery job')
                    if not candidates:
                        require(original.get('status')=='completed','recovery executor still active; jobs not final')
                        require(not matching,'recovery artifacts without their executor')
                        # Older approved versions of the gate had no recovery job.
                        # This is absence of this dispatcher, not proof that an
                        # inline gate publication never dispatched its own checks.
                        excluded.append({'run':rid,'attempt':attempt,'reason':'no_recovery_job'});continue
                    job=candidates[0]
                    require(job.get('run_id')==rid and job.get('run_attempt')==attempt,'original job identity')
                    if job.get('status')=='completed' and job.get('conclusion')=='skipped' and not matching:
                        excluded.append({'run':rid,'attempt':attempt,'reason':'recovery_job_skipped'});continue
                    if not matching:
                        steps=job.get('steps') or []
                        dispatch=[s for s in steps if s.get('name')==DISPATCH]
                        if (job.get('status')=='completed' and len(dispatch)==1
                                and dispatch[0].get('status')=='completed' and dispatch[0].get('conclusion')=='skipped'
                                and 'started_at' in dispatch[0] and dispatch[0]['started_at'] is None):
                            excluded.append({'run':rid,'attempt':attempt,'reason':'dispatcher_explicitly_never_started'});continue
                        raise ValueError('missing durable records; dispatch effect unlocated')
                    recovered.append(discover_recovery_intents(api,repo,rid,attempt,
                        activation_commit=anchor,current_main=current_main))
                except Exception as error:
                    unresolved.append({'run':rid,'attempt':attempt,'error_type':type(error).__name__,'reason':str(error)[:1000]})
        except Exception as error:
            unresolved.append({'run':rid,'error_type':type(error).__name__,'reason':str(error)[:1000]})
    numbers=set()
    for execution in recovered:
        numbers.update(item['intent']['operation']['number'] for item in execution['operations'].values())
    return {'executions':recovered,'unresolved':unresolved,'excluded':excluded,'enumeration_complete':True,
            'pending_numbers':sorted(numbers),'unlocated_effects':bool(unresolved),'dispatch_authorized':False}

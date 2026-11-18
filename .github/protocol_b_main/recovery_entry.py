"""Trusted-main recovery entry point. The triggering event payload is not read."""
import argparse
import html
import json
import os
from pathlib import Path
import re
import tempfile
from deferred_artifact import MAX_RECORD
from prepare_recovery import prepare_recovery
from dispatch_recovery import dispatch_recovery
from github_api import API


def persist(path,value):
    raw=(json.dumps(value,indent=2,sort_keys=True)+'\n').encode()
    if len(raw)>MAX_RECORD:raise ValueError('Recovery record exceeds the authenticated read bound')
    path.parent.mkdir(parents=True,exist_ok=True)
    fd,temp=tempfile.mkstemp(prefix=path.name+'.',dir=path.parent)
    try:
        with os.fdopen(fd,'wb') as stream:
            stream.write(raw);stream.flush();os.fsync(stream.fileno())
        os.replace(temp,path)
    finally:
        if os.path.exists(temp):os.unlink(temp)


def publish_summary(stage, value):
    """Expose pending and uncertain work without sending repeated issue comments."""
    path = os.environ.get('GITHUB_STEP_SUMMARY')
    if not path:
        return
    rows = []
    if stage == 'prepare':
        rows.append({'planned_operations': len(value.get('operations', [])),
                     'unresolved_reads': len(value.get('unresolved', [])),
                     'prior_execution_errors': len(value.get('prior_execution_errors', []))})
        for observation in value.get('observations', []):
            operation = observation.get('operation', {})
            status = observation.get('existing', {})
            rows.append({'pr': operation.get('number'), 'workflow': operation.get('workflow'),
                         'existing': status.get('state'), 'run_ids': status.get('run_ids', []),
                         'blocked': observation.get('blocked'), 'planned': observation.get('planned', False)})
        rows.extend(value.get('unresolved', []))
        rows.extend(value.get('prior_execution_errors', []))
    else:
        for receipt in value.get('receipts', []):
            rows.append({k: receipt.get(k) for k in ('operation_key', 'status', 'workflow_run_id',
                'head_sha', 'head_differs_from_merge', 'exact_release_covered', 'attention', 'reason', 'error',
                'response_evidence')})
    display = html.escape(json.dumps(rows[:100], indent=2, ensure_ascii=True))
    body = ('## Main-check recovery '+stage+'\n\n'
            'Dispatch confirmation is not verification success. Pending, failed and uncertain runs remain visible. '
            'The original intent and result artifacts contain the complete records.\n\n<pre>'+display+'</pre>\n')
    if len(rows) > 100:
        body += '\nShowing 100 of '+str(len(rows))+' records; see the artifact for the remainder.\n'
    with open(path, 'a', encoding='utf-8') as output:
        output.write(body)


def run(argv=None):
    parser=argparse.ArgumentParser()
    parser.add_argument('stage',choices=['prepare','dispatch'])
    parser.add_argument('--baseline',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    repo=os.environ['GITHUB_REPOSITORY'];program=os.environ['GITHUB_SHA']
    run_id=int(os.environ['GITHUB_RUN_ID']);attempt=int(os.environ['GITHUB_RUN_ATTEMPT'])
    if not re.fullmatch(r'[0-9a-f]{40}',program) or run_id<=0 or attempt!=1:
        raise ValueError('Recovery runs only on the first attempt of a new workflow execution')
    if os.environ.get('GITHUB_EVENT_NAME') not in ('schedule','workflow_run'):
        raise ValueError('Recovery does not run for PR or comment events')
    baseline=json.loads(args.baseline.read_text(encoding='utf-8'))
    api=API(repo)
    api.require_rate_reserve()
    if args.stage=='prepare':
        target=args.output/'intents.json'
        if target.exists():raise ValueError('This execution already prepared; reconcile before restarting')
        plan=prepare_recovery(api,repo,baseline,program_commit=program,recovery_run=run_id,recovery_attempt=attempt)
        persist(target,plan)
        if 'progress' in plan:
            persist(args.output/'progress.json',plan['progress'])
        if os.environ.get('GITHUB_OUTPUT'):
            with open(os.environ['GITHUB_OUTPUT'],'a',encoding='utf-8') as output:
                output.write('has_operations='+str(bool(plan['operations'])).lower()+'\n')
        publish_summary('prepare',plan)
        print('Prepared '+str(len(plan['operations']))+' operations; no dispatch has been made.')
    else:
        target=args.output/'results.json'
        if target.exists():raise ValueError('This execution already entered dispatch; never replay it')
        result=dispatch_recovery(api,repo,baseline,program_commit=program,recovery_run=run_id,
            recovery_attempt=attempt,persist=lambda value:persist(target,value))
        publish_summary('dispatch',result)
        attention=[r for r in result['receipts'] if r['status']=='effect_needs_reconciliation' or r.get('attention')]
        print('Recorded '+str(len(result['receipts']))+' operation outcomes; '+str(len(attention))+' need reconciliation.')
    return 0


if __name__=='__main__':raise SystemExit(run())

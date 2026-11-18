"""Resume immutable run discovery; success always needs a fresh positive witness.

Only authenticated progress from the trusted recovery program may be supplied
as a cursor. Saved run identities and commit ancestry are not saved run outcomes.
A partial search can prove that a run exists, never that a dispatch is absent.
"""
import copy
import datetime
from discover_intents import require, SHA
from dispatch_intents import operation_key
from existing_runs import classify_existing_runs
from run_windows import scan_run_windows, stamp, printed


def identity(run):
    require(isinstance(run, dict) and type(run.get('id')) is int and run['id'] > 0,
            'existing run identity')
    stamp(run.get('created_at'))
    require(type(run.get('workflow_id')) is int and run['workflow_id']>0
            and isinstance(run.get('head_sha'),str) and SHA.fullmatch(run['head_sha'])
            and all(isinstance(run.get(k),str) and run[k] for k in ('head_branch','event','path'))
            and all(isinstance(run.get(k),dict) and isinstance(run[k].get('full_name'),str)
                    and '/' in run[k]['full_name'] for k in ('repository','head_repository')),
            'incomplete existing run identity')
    return {key: copy.deepcopy(run.get(key)) for key in
            ('id', 'workflow_id', 'created_at', 'head_sha', 'head_branch', 'event', 'path')} | {
        'repository': {'full_name': (run.get('repository') or {}).get('full_name')},
        'head_repository': {'full_name': (run.get('head_repository') or {}).get('full_name')}}


def validate_cursor(value, operation, merged_at, exact_release, workflow_id, now):
    require(isinstance(value, dict) and value.get('schema') == 'main-run-search/v1'
            and value.get('operation') == operation and value.get('operation_key') == operation_key(operation)
            and value.get('merged_at') == merged_at and value.get('exact_release') is exact_release
            and value.get('workflow_id') == workflow_id, 'existing search binding')
    require(type(exact_release) is bool and type(workflow_id) is int and workflow_id>0, 'existing search parameter types')
    merged=datetime.datetime.fromisoformat(merged_at.replace('Z', '+00:00'))
    require(merged.utcoffset() is not None, 'existing merge timezone')
    start = int(merged.timestamp())
    through = stamp(value.get('through'))
    require(start <= through <= now, 'existing search time range')
    windows = value.get('pending_windows')
    require(isinstance(windows, list) and len(windows) <= 10000, 'existing search windows')
    end = start - 1
    for window in windows:
        require(isinstance(window, dict) and set(window) == {'start', 'end'}, 'existing window shape')
        lo, hi = stamp(window['start']), stamp(window['end'])
        require(end < lo <= hi <= through, 'existing search window ordering'); end = hi
    records = value.get('identities')
    require(isinstance(records, list) and len(records) <= 10000, 'existing search identity bound')
    seen = set()
    for row in records:
        require(row == identity(row) and row['workflow_id']==workflow_id and row['id'] not in seen
                and start <= stamp(row['created_at']) <= through, 'existing search record')
        seen.add(row['id'])
    classified = value.get('classified')
    require(isinstance(classified, dict) and all(isinstance(k,str) and k.isascii() and k.isdigit() and k==str(int(k)) and int(k) in seen and v is True
            for k, v in classified.items()), 'existing search classification')
    comparisons = value.get('comparisons')
    require(isinstance(comparisons, dict) and len(comparisons) <= 10000
            and all(isinstance(k, str) and SHA.fullmatch(k) and isinstance(v, dict)
                    for k, v in comparisons.items()), 'existing immutable comparisons')
    require(type(value.get('next_refresh')) is int and value['next_refresh'] >= 0,
            'existing refresh cursor')
    return value


def search_existing(api, operation, merged_at, observed_main, exact_release, *, cursor=None,
                    now=None, max_requests=10, max_compares=4, max_refresh=2):
    now = int(datetime.datetime.now(datetime.timezone.utc).timestamp()) if now is None else now
    require(type(now) is int and type(exact_release) is bool, 'existing search parameters')
    start = int(datetime.datetime.fromisoformat(merged_at.replace('Z', '+00:00')).timestamp())
    require(start <= now, 'merge timestamp is in the future')
    metadata = api.json('actions/workflows/' + operation['workflow'])
    wid = metadata.get('id')
    require(type(wid) is int and wid > 0 and metadata.get('path') == '.github/workflows/' + operation['workflow'],
            'existing workflow identity')
    if cursor is None:
        state = {'schema': 'main-run-search/v1', 'operation_key': operation_key(operation),
                 'operation': copy.deepcopy(operation), 'merged_at': merged_at, 'exact_release': exact_release,
                 'workflow_id': wid, 'through': printed(now), 'pending_windows': [],
                 'identities': [], 'classified': {}, 'comparisons': {}, 'next_refresh': 0}
        windows = [{'start': printed(start), 'end': printed(now)}]
    else:
        state = copy.deepcopy(validate_cursor(cursor, operation, merged_at, exact_release, wid, now))
        windows = state['pending_windows']
        through = stamp(state['through'])
        # Re-read the boundary second, including requests created after the
        # previous snapshot in that same second. Newer time is never skipped.
        if windows and stamp(windows[-1]['end']) == through:
            windows[-1]['end'] = printed(now)
        else:
            windows.append({'start': printed(through), 'end': printed(now)})
    scanned = scan_run_windows(api, wid, windows, max_requests=max_requests)
    old = {row['id']: row for row in state['identities']}
    for run in scanned['runs']:
        row = identity(run)
        require(row['workflow_id']==wid,'listed existing run workflow mismatch')
        require(row['id'] not in old or old[row['id']] == row, 'existing run immutable identity changed')
        old[row['id']] = row
    require(len(old) <= 10000, 'existing identity inventory exceeded bound; needs investigation')
    state.update(through=printed(now), pending_windows=scanned['pending_windows'],
                 identities=sorted(old.values(), key=lambda row: row['id']))
    errors=list(scanned['unresolved']);compares=0
    def eligible(row):
        return (row['repository']['full_name'] == operation['repository']
                and row['head_repository']['full_name'] == operation['repository']
                and row['head_branch'] == 'main' and row['event'] in ('push','workflow_dispatch')
                and row['path'] in ('.github/workflows/'+operation['workflow'],
                                    '.github/workflows/'+operation['workflow']+'@main')
                and stamp(row['created_at']) >= start)
    for row in state['identities']:
        key=str(row['id'])
        if key in state['classified']: continue
        try:
            if not eligible(row): state['classified'][key]=False;continue
            head=row['head_sha'];require(isinstance(head,str) and SHA.fullmatch(head),'existing run head')
            if exact_release and head != operation['merge']:
                state['classified'][key]=False;continue
            comparisons=copy.deepcopy(state['comparisons'])
            if head != operation['merge'] and head not in comparisons:
                if compares >= max_compares: break
                compares+=1
                value=api.json(f"compare/{operation['merge']}...{head}")
                # Retain only fields used to verify this immutable comparison.
                comparisons[head]={k:copy.deepcopy(value.get(k)) for k in
                    ('base_commit','status','behind_by')}
                comparisons[head]['commits']=copy.deepcopy(value.get('commits',[])[-1:])
            comparison=comparisons.get(head,{})
            if (head != operation['merge'] and
                    (comparison.get('base_commit') or {}).get('sha')==operation['merge'] and
                    type(comparison.get('behind_by')) is int and comparison['behind_by']>0 and
                    comparison.get('status') in ('behind','diverged')):
                state['comparisons']=comparisons
                state['classified'][key]=False
                continue
            probe=dict(row,status='queued',conclusion=None)
            result=classify_existing_runs(operation,[probe],comparisons,merged_at=merged_at,
                observed_main=observed_main,exact_release=exact_release,enumeration_complete=True)
            require(result['state'] in ('existing_run_in_progress','no_confirmed_run_check_intents',
                                       'missing_exact_release_run'), 'existing run ancestry or identity unresolved')
            state['comparisons']=comparisons
            state['classified'][key]=result['state']=='existing_run_in_progress'
        except Exception as error:
            errors.append({'run':row['id'],'error_type':type(error).__name__,'reason':str(error)[:1000]})
            break
    # A fully inspected window remains covered after identities proven
    # immutably irrelevant to this operation are discarded. Retain candidates
    # and unclassified rows, never their mutable status or conclusion.
    state['identities']=[row for row in state['identities']
                         if state['classified'].get(str(row['id'])) is not False]
    kept={str(row['id']) for row in state['identities']}
    state['classified']={k:v for k,v in state['classified'].items() if k in kept}
    heads={row['head_sha'] for row in state['identities']}
    state['comparisons']={k:v for k,v in state['comparisons'].items() if k in heads}
    matches=sorted((int(k) for k,v in state['classified'].items() if v),reverse=True)
    complete=not state['pending_windows'] and len(state['classified'])==len(state['identities']) and not errors
    fresh=[];outcomes=[]
    if matches:
        offset=state['next_refresh'] % len(matches)
        selected=(matches[offset:]+matches[:offset])[:max_refresh]
        for rid in selected:
            state['next_refresh']=(matches.index(rid)+1) % len(matches)
            try:
                run=api.json('actions/runs/'+str(rid))
                require(identity(run)==old[rid], 'fresh existing run changed identity')
                result=classify_existing_runs(operation,[run],state['comparisons'],merged_at=merged_at,
                    observed_main=observed_main,exact_release=exact_release,enumeration_complete=True)
                fresh.append(run);outcomes.append(result)
                if result['state']=='verification_passed':
                    # This is positive evidence of one covering successful run,
                    # not a claim that all other runs passed or were inspected.
                    result.update(verification_witness=rid,known_matching_run_ids=matches,
                                  other_runs_not_rechecked=[r for r in matches if r not in {x['id'] for x in fresh}],
                                  enumeration_complete=complete)
                    return {'classification':result,'runs':fresh,'search':state,'observations':outcomes,'unresolved':errors}
            except Exception as error:
                errors.append({'run':rid,'error_type':type(error).__name__,'reason':str(error)[:1000]})
        classification={'state':'existing_runs_need_attention' if errors or any(r['needs_attention'] for r in outcomes)
                                else 'existing_run_in_progress',
                        'run_ids':matches,'needs_attention':bool(errors) or any(r['needs_attention'] for r in outcomes),
                        'dispatch_authorized':False,'enumeration_complete':complete}
    else:
        classification=classify_existing_runs(operation,[],{},merged_at=merged_at,
            observed_main=observed_main,exact_release=exact_release,enumeration_complete=complete)
    return {'classification':classification,'runs':fresh,'search':state,'observations':outcomes,'unresolved':errors}

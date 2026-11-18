"""Read unfiltered workflow history and require contiguous run-number coverage.

A time window is insufficient evidence that an earlier recovery execution does
not exist. A missing number keeps discovery incomplete. The caller persists
partial records and the next page in authenticated progress; it must retain the
original executions separately until their effects are reconciled.
"""
from discover_intents import require
from run_windows import stamp


def scan_run_sequence(api,workflow_id,frontier,target_number,*,partial=None,max_pages=3):
    require(type(workflow_id) is int and workflow_id>0,'workflow sequence identity')
    require(type(frontier) is int and type(target_number) is int and 0<=frontier<=target_number,
            'workflow sequence range')
    require(type(max_pages) is int and 1<=max_pages<=10,'workflow sequence page budget')
    partial=partial or {'frontier':frontier,'target':target_number,'next_page':1,'records':[]}
    require(partial.get('frontier')==frontier and partial.get('target')==target_number,
            'workflow sequence partial binding')
    page=partial.get('next_page');records=partial.get('records')
    require(type(page) is int and page>=1 and isinstance(records,list) and len(records)<=10000,
            'workflow sequence partial shape')
    known={};ids={};errors=[];reads=0
    def retain(row):
        require(isinstance(row,dict) and row.get('workflow_id')==workflow_id,'workflow sequence row identity')
        number=row.get('run_number');rid=row.get('id')
        require(type(number) is int and number>0 and type(rid) is int and rid>0,'workflow run number and ID')
        if number<=frontier or number>target_number:return
        require(all(isinstance(row.get(key),str) and row[key] for key in ('event','head_branch')),
                'missing workflow discovery identity')
        stamp(row.get('created_at'))
        require(number not in known or known[number]['id']==rid,'duplicate run number with different IDs')
        require(rid not in ids or ids[rid]==number,'duplicate run ID with different numbers')
        # Status may change between partial scans. Event, branch and creation
        # time select possible dispatchers and must not change or be absent.
        selected={k:row[k] for k in ('id','workflow_id','run_number','event','head_branch','created_at')}
        require(number not in known or known[number]==selected,'workflow discovery identity changed')
        known[number]=selected
        ids[rid]=number
    for row in records:retain(row)
    previous_ids=set(ids)
    # Always overlap the preceding page when resuming, because new workflow runs
    # can move a boundary. Missing coverage is detected rather than inferred.
    page=max(1,page-1) if page>1 else 1
    end_reached=False
    while len(known)<target_number-frontier and reads<max_pages:
        value=api.json(f'actions/workflows/{workflow_id}/runs?per_page=100&page={page}')
        reads+=1
        chunk=value.get('workflow_runs')
        require(isinstance(chunk,list) and len(chunk)<=100,'workflow sequence page')
        for row in chunk:retain(row)
        if len(chunk)<100 or any(row.get('run_number',target_number)>0 and row.get('run_number',target_number)<=frontier for row in chunk):
            end_reached=True;break
        page+=1
    require(len(known)<=10000,'workflow discovery retention bound')
    complete=len(known)==target_number-frontier
    if end_reached and not complete:
        missing=[n for n in range(frontier+1,target_number+1) if n not in known]
        errors.append({'reason':'Missing workflow run numbers; absence is not established.',
                       'missing_numbers':missing[:100],'missing_count':len(missing)})
        page=1  # Recheck actual state next wake; do not advance past a gap.
    ordered=[known[n] for n in sorted(known)]
    return {'runs':ordered,'new_runs':[row for row in ordered if row['id'] not in previous_ids],
        'enumeration_complete':complete,'requests':reads,'unresolved':errors,
        'partial':None if complete else {'frontier':frontier,'target':target_number,'next_page':page,'records':ordered},
        'dispatch_authorized':False}

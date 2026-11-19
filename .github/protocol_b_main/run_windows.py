"""Bounded complete run enumeration despite GitHub's filtered 1,000-run cap.

Only complete non-overlapping time windows are returned. The caller retains
unvisited windows in its authenticated progress record and must never infer
absence while any requested window remains unvisited. No writes occur here.
"""
import datetime
from urllib.parse import quote
from discover_intents import require

UTC=datetime.timezone.utc


def stamp(value):
    require(isinstance(value,str),'run-window timestamp')
    result=datetime.datetime.fromisoformat(value.replace('Z','+00:00'))
    require(result.utcoffset() is not None and result.microsecond==0,
            'run-window timestamps require whole seconds and a timezone')
    return int(result.timestamp())


def printed(value):
    return datetime.datetime.fromtimestamp(value,UTC).strftime('%Y-%m-%dT%H:%M:%SZ')


def scan_run_windows(api, workflow_id, windows, *, max_requests=20):
    require(type(workflow_id) is int and workflow_id>0,'workflow ID')
    require(type(max_requests) is int and 1<=max_requests<=100,'run discovery request budget')
    require(isinstance(windows,list) and len(windows)<=10000,'run-window count')
    queue=[]
    for window in windows:
        require(isinstance(window,dict) and set(window)=={'start','end'},'run-window shape')
        lo,hi=stamp(window['start']),stamp(window['end'])
        require(lo<=hi,'reversed run window');queue.append((lo,hi))
    queue.sort()
    require(all(a[1]<b[0] for a,b in zip(queue,queue[1:])),'overlapping run windows')
    count=0;rows=[];completed=[];unresolved=[]
    def request(lo,hi,page):
        nonlocal count
        require(count<max_requests,'run discovery budget exhausted')
        count+=1
        query=quote(printed(lo)+'..'+printed(hi),safe='')
        value=api.json(f'actions/workflows/{workflow_id}/runs?branch=main&created={query}&per_page=100&page={page}')
        require(isinstance(value,dict) and type(value.get('total_count')) is int
                and value['total_count']>=0 and isinstance(value.get('workflow_runs'),list),
                'invalid run-window response')
        return value
    while queue and count<max_requests:
        lo,hi=queue[0]
        try:
            first=request(lo,hi,1);total=first['total_count']
            if total>=1000:
                require(lo<hi,'1,000 or more filtered runs in one second; cannot prove completeness')
                # Treat an exactly capped count as ambiguous too; the API
                # documentation does not promise an uncapped total_count.
                middle=(lo+hi)//2
                queue[:1]=[(lo,middle),(middle+1,hi)]
                continue
            pages=max(1,(total+99)//100)
            if pages-1>max_requests-count:
                # A later wake starts with a fresh budget; partial pages do
                # not become evidence of absence or an advanced cursor.
                break
            selected=[];seen=set()
            for page in range(1,pages+1):
                value=first if page==1 else request(lo,hi,page)
                require(value['total_count']==total,'run collection changed during pagination')
                chunk=value['workflow_runs'];expected=min(100,max(0,total-(page-1)*100))
                require(len(chunk)==expected,'incomplete run-window page')
                for row in chunk:
                    require(isinstance(row,dict) and type(row.get('id')) is int
                            and row['id']>0 and row['id'] not in seen,'ambiguous run-window identity')
                    created=stamp(row.get('created_at'))
                    require(lo<=created<=hi,'run outside requested window')
                    seen.add(row['id']);selected.append(row)
            require(len(selected)==total,'incomplete run window')
            rows.extend(selected);completed.append({'start':printed(lo),'end':printed(hi)})
            queue.pop(0)
        except Exception as error:
            unresolved.append({'window':{'start':printed(lo),'end':printed(hi)},
                'error_type':type(error).__name__,'reason':str(error)[:1000]})
            break
    require(len({row['id'] for row in rows})==len(rows),'duplicate run across completed windows')
    pending=[{'start':printed(lo),'end':printed(hi)} for lo,hi in queue]
    return {'runs':rows,'completed_windows':completed,'pending_windows':pending,
            'requests':count,'unresolved':unresolved,'enumeration_complete':not pending,
            'dispatch_authorized':False}

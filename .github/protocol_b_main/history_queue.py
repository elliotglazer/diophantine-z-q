"""Bounded, resumable discovery along main's first-parent history.

The caller must authenticate the progress record before passing it here. This
module only reads GitHub records. Its cursor records enumeration, not review
acceptance, successful checks or permission to dispatch. Pending operations and
uncertain executions belong in the caller's authenticated progress record.
"""
from discover_deferred import pages
from discover_intents import SHA, _ancestor, require


def discover_main_history(api, repo, activation_commit, observed_main, *, cursor=None,
                          max_commits=20):
    require(isinstance(repo,str) and type(max_commits) is int and 1<=max_commits<=100,
            'history discovery arguments')
    require(all(isinstance(x,str) and SHA.fullmatch(x) for x in (activation_commit,observed_main)),
            'history commit identities')
    if cursor is None:
        cursor={'schema':'main-check-history/v1','repository':repo,
                'activation_commit':activation_commit,'frontier':activation_commit,
                'scan_head':None,'next_commit':None}
    require(isinstance(cursor,dict) and cursor.get('schema')=='main-check-history/v1'
            and cursor.get('repository')==repo and cursor.get('activation_commit')==activation_commit,
            'history cursor binding')
    frontier=cursor.get('frontier');head=cursor.get('scan_head');current=cursor.get('next_commit')
    require(isinstance(frontier,str) and SHA.fullmatch(frontier),'history frontier')
    require((head is None)==(current is None),'partial history cursor')
    _ancestor(api,activation_commit,frontier)
    _ancestor(api,frontier,observed_main)
    if head is None:
        head=current=observed_main
    else:
        require(all(isinstance(x,str) and SHA.fullmatch(x) for x in (head,current)),
                'partial history identities')
        _ancestor(api,frontier,current)
        _ancestor(api,current,head)
        _ancestor(api,head,observed_main)
    walked=[];candidates={};excluded=[];unresolved=[]
    while current!=frontier and len(walked)<max_commits:
        try:
            commit=api.json('git/commits/'+current)
            require(commit.get('sha')==current,'history commit response identity')
            parents=commit.get('parents')
            require(isinstance(parents,list) and parents,'activation frontier not reached before root')
            parent=parents[0].get('sha')
            require(isinstance(parent,str) and SHA.fullmatch(parent) and parent!=current,
                    'history first parent')
            require(parent not in walked,'cyclic history response')
            associated=pages(api,'commits/'+current+'/pulls',identity='id',max_pages=10)
            selected=[]
            for listed in associated:
                number=listed.get('number')
                require(type(number) is int and number>0,'associated PR number')
                # A PR associated with an earlier commit may merge later. Its
                # merge commit is the only discovery point that can select it.
                pr=api.json('pulls/'+str(number))
                require(pr.get('number')==number and
                    ((pr.get('base') or {}).get('repo') or {}).get('full_name')==repo,
                    'associated PR repository identity')
                require(type(pr.get('merged')) is bool and pr.get('state') in ('open','closed'),
                    'associated PR state')
                if not pr['merged'] or pr['state']!='closed' or pr.get('merge_commit_sha')!=current:
                    excluded.append({'number':number,'commit':current,'reason':'not_this_confirmed_merge'})
                    continue
                actor=pr.get('merged_by') or {}
                if (pr['base'].get('ref')!='main' or actor.get('login')!='github-actions[bot]'
                        or actor.get('type')!='Bot'):
                    excluded.append({'number':number,'commit':current,'reason':'not_gate_main_merge'})
                    continue
                selected.append((number,pr))
            # Commit the cursor only after every association for this commit
            # was read. A failed later page cannot silently lose an older PR.
            for number,pr in selected:
                if number in candidates:
                    require(candidates[number]['merge_commit_sha']==pr['merge_commit_sha'],
                            'conflicting PR merge identity')
                candidates[number]=pr
            walked.append(current);current=parent
        except Exception as error:
            unresolved.append({'commit':current,'error_type':type(error).__name__,
                               'reason':str(error)[:1000]})
            break
    complete=current==frontier
    updated={'schema':'main-check-history/v1','repository':repo,'activation_commit':activation_commit,
             'frontier':head if complete else frontier,
             'scan_head':None if complete else head,'next_commit':None if complete else current}
    return {'cursor':updated,'walked':walked,'candidates':list(candidates.values()),
            'excluded':excluded,'unresolved':unresolved,'enumeration_complete':complete,
            'dispatch_authorized':False}

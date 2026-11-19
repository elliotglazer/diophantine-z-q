"""Classify existing main runs without authorizing a new dispatch.

The caller supplies current authenticated API
records and complete enumeration. Durable-intent reconciliation is still needed
before any write, even when this reports no confirmed run.
"""
import datetime
import re

SHA = re.compile(r'[0-9a-f]{40}')


def classify_existing_runs(operation, runs, comparisons, *, merged_at, observed_main,
                           exact_release, enumeration_complete):
    def result(state, ids=(), attention=False):
        return {'state':state, 'run_ids':list(ids), 'needs_attention':attention,
                'dispatch_authorized':False}
    if not enumeration_complete:
        return result('incomplete_enumeration', attention=True)
    try:
        repo, workflow, merge = [operation[k] for k in ('repository','workflow','merge')]
        if (not isinstance(repo,str) or workflow not in {'research-checks.yml','kernel-lean.yml'}
                or not isinstance(merge,str) or SHA.fullmatch(merge) is None
                or not isinstance(observed_main,str) or SHA.fullmatch(observed_main) is None
                or type(exact_release) is not bool):
            return result('invalid_operation', attention=True)
        merged = datetime.datetime.fromisoformat(merged_at.replace('Z','+00:00'))
        if merged.utcoffset() is None: return result('invalid_operation', attention=True)
        matched=[]
        seen={}
        for run in runs:
            identity=run.get('id')
            if type(identity) is not int or identity <= 0: return result('invalid_run', attention=True)
            if identity in seen:
                if seen[identity] != run: return result('conflicting_run_records', attention=True)
                continue
            seen[identity]=run
            if ((run.get('repository') or {}).get('full_name') != repo
                    or (run.get('head_repository') or {}).get('full_name') != repo
                    or run.get('path') not in ('.github/workflows/'+workflow,'.github/workflows/'+workflow+'@main')
                    or run.get('head_branch') != 'main'
                    or run.get('event') not in {'push','workflow_dispatch'}):
                continue
            head=run.get('head_sha')
            if not isinstance(head,str) or SHA.fullmatch(head) is None:
                return result('invalid_run', attention=True)
            created=datetime.datetime.fromisoformat(run['created_at'].replace('Z','+00:00'))
            if created.utcoffset() is None: return result('invalid_run', attention=True)
            if created < merged: continue
            if head != merge:
                if exact_release: continue
                comparison=comparisons.get(head)
                if (not isinstance(comparison,dict)
                        or (comparison.get('base_commit') or {}).get('sha') != merge
                        or not isinstance(comparison.get('commits'), list) or not comparison['commits']):
                    return result('missing_ancestry', attention=True)
                # Require the requested comparison's actual last commit, not a
                # boolean asserted by a candidate record.
                if comparison['commits'][-1].get('sha') != head:
                    return result('missing_ancestry', attention=True)
                if type(comparison.get('behind_by')) is not int:
                    return result('missing_ancestry', attention=True)
                if comparison['behind_by'] != 0 or comparison.get('status') != 'ahead': continue
            if run.get('status') == 'completed':
                outcome=run.get('conclusion')
                if outcome == 'success': state='verification_passed'
                elif outcome in {'failure','cancelled','timed_out','startup_failure','action_required','stale','neutral','skipped'}:
                    state='terminal_run_needs_attention'
                else: return result('invalid_run', attention=True)
            elif run.get('status') in {'queued','pending','waiting','requested','in_progress'}:
                state='existing_run_in_progress'
            else: return result('invalid_run', attention=True)
            matched.append((identity,state))
        if matched:
            # Every actual attempt remains visible. One success does not erase
            # an unexplained failed attempt or authorize another automatic run.
            attention=any(state=='terminal_run_needs_attention' for _,state in matched)
            state='existing_runs_need_attention' if attention else (
                'existing_run_in_progress' if any(s=='existing_run_in_progress' for _,s in matched) else 'verification_passed')
            return result(state, sorted(i for i,_ in matched), attention)
        if exact_release and observed_main != merge:
            return result('missing_exact_release_run', attention=True)
        return result('no_confirmed_run_check_intents')
    except (KeyError, TypeError, ValueError, AttributeError):
        return result('malformed_evidence', attention=True)

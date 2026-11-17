"""Pure reconciliation of an already-persisted dispatch intent.

The I/O layer must authenticate the original recovery
run, artifact digest and current API job/run records before calling this code.
A missing response never establishes that the request had no effect.
"""
import hashlib
import json
import re

FIELDS = ('repository', 'number', 'head', 'merge', 'workflow', 'ref')
SHA = re.compile(r'[0-9a-f]{40}')


def operation_key(operation):
    value = {k: operation[k] for k in FIELDS}
    if (not isinstance(value['repository'], str)
            or re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', value['repository']) is None
            or type(value['number']) is not int or value['number'] <= 0
            or any(not isinstance(value[k], str) or SHA.fullmatch(value[k]) is None for k in ('head', 'merge'))
            or value['workflow'] not in ('research-checks.yml', 'kernel-lean.yml')
            or value['ref'] != 'main'):
        raise ValueError('invalid operation')
    raw = json.dumps(value, sort_keys=True, separators=(',', ':')).encode()
    return hashlib.sha256(raw).hexdigest()


def reconcile_intent(operation, intent, receipt, job, *, dispatch_step, current_runs, enumeration_complete,
                     results_persisted_after_dispatch=False):
    """Classify one authenticated previous intent, without issuing permission.

    `safe_absence` means that this particular old execution did not dispatch;
    it does not satisfy fresh readiness, global concurrency or run enumeration.
    Actual API runs can reconcile a lost response, but conflicting identities
    and uncertain effects remain visible and never trigger retries here.
    """
    def result(state, run_id=None, safe_absence=False):
        return {'state': state, 'run_id': run_id, 'safe_absence': safe_absence,
                'dispatch_authorized': False}
    try:
        key = operation_key(operation)
        if not enumeration_complete:
            return result('incomplete_run_enumeration')
        if (not isinstance(intent, dict) or intent.get('schema') != 'main-check-intent/v1'
                or intent.get('operation_key') != key
                or operation_key(intent['operation']) != key
                or intent.get('request') != {'ref': 'main', 'return_run_details': True}
                or type(intent.get('recovery_run')) is not int or intent['recovery_run'] <= 0
                or type(intent.get('recovery_attempt')) is not int or intent['recovery_attempt'] <= 0):
            return result('invalid_intent')
        if (not isinstance(job, dict) or job.get('run_id') != intent['recovery_run']
                or job.get('run_attempt') != intent['recovery_attempt']):
            return result('wrong_executor')
        if job.get('status') != 'completed':
            return result('executor_not_terminal')
        steps = [s for s in job.get('steps', []) if s.get('name') == dispatch_step]
        if len(steps) != 1:
            return result('ambiguous_dispatch_step')
        step = steps[0]
        if receipt is not None:
            if (not isinstance(receipt, dict) or receipt.get('schema') != 'main-check-receipt/v1'
                    or receipt.get('operation_key') != key
                    or receipt.get('recovery_run') != intent['recovery_run']
                    or receipt.get('recovery_attempt') != intent['recovery_attempt']):
                return result('invalid_receipt')
            if (results_persisted_after_dispatch and receipt.get('status') == 'not_sent'
                    and receipt.get('request_sent') is False and 'response' not in receipt
                    and 'workflow_run_id' not in receipt and step.get('status') == 'completed'):
                return result('authenticated_result_confirms_not_sent', safe_absence=True)
            run_id = receipt.get('workflow_run_id')
            if type(run_id) is int and run_id > 0:
                matches = [r for r in current_runs if r.get('id') == run_id]
                if len(matches) != 1:
                    return result('returned_run_not_reconciled', run_id)
                run = matches[0]
                if ((run.get('repository') or {}).get('full_name') != operation['repository']
                        or (run.get('head_repository') or {}).get('full_name') != operation['repository']
                        or run.get('path') not in ('.github/workflows/' + operation['workflow'],
                                                 '.github/workflows/' + operation['workflow'] + '@main')
                        or run.get('head_branch') != 'main' or run.get('event') != 'workflow_dispatch'
                        or not isinstance(run.get('head_sha'), str) or SHA.fullmatch(run['head_sha']) is None):
                    return result('returned_run_identity_mismatch', run_id)
                # Ancestry and outcome are classified by existing_runs.py. A
                # valid returned run proves a dispatch happened, not success.
                return result('response_and_actual_run_confirmed', run_id)
            return result('receipt_has_no_confirmed_run')
        # Missing or incomplete step reporting after a runner crash is not proof
        # of no effect. Accept only an explicit completed/skipped step with no
        # recorded start, on a terminal original executor.
        if (step.get('status') == 'completed' and step.get('conclusion') == 'skipped'
                and 'started_at' in step and step['started_at'] is None):
            return result('dispatcher_explicitly_not_started', safe_absence=True)
        return result('effect_uncertain_no_retry')
    except (KeyError, TypeError, ValueError, AttributeError):
        return result('malformed_evidence')

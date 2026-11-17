"""Authenticate original recovery intents before interpreting their effects.

All transport methods used here are GET-only. This module neither
executes artifact contents nor grants permission to dispatch a workflow.
"""
import hashlib
import io
import json
import re
import stat
import zipfile
from deferred_artifact import MAX_ZIP, MAX_RECORD
from discover_deferred import pages
from dispatch_intents import operation_key

WORKFLOW = '.github/workflows/protocol-b.yml'
JOB = 'Recover deferred main checks'
UPLOAD = 'Persist main-check dispatch intents'
DISPATCH = 'Dispatch confirmed main checks'
RESULTS_UPLOAD = 'Persist main-check dispatch results'
SHA = re.compile(r'[0-9a-f]{40}')


def require(value, message):
    if not value:
        raise ValueError(message)


def _record(raw, artifact, publisher, repo_id, kind):
    run, attempt = publisher['id'], publisher['run_attempt']
    require(isinstance(raw, bytes) and 0 < len(raw) <= MAX_ZIP, 'archive size')
    require(artifact.get('name') == f'protocol-b-main-{kind}-{run}-{attempt}'
            and artifact.get('expired') is False, 'archive name, attempt or expiry')
    binding = artifact.get('workflow_run') or {}
    require(binding.get('id') == run and binding.get('repository_id') == repo_id
            and binding.get('head_sha') == publisher['head_sha'], 'archive source binding')
    require(type(artifact.get('size_in_bytes')) is int
            and 0 < artifact['size_in_bytes'] <= MAX_ZIP, 'declared archive size')
    require(artifact.get('digest') == 'sha256:' + hashlib.sha256(raw).hexdigest(), 'archive digest')
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        names = archive.namelist()
        expected = kind + '.json'
        require(names == [expected], 'unexpected or duplicate recovery archive members')
        item = archive.getinfo(expected)
        require(not item.is_dir() and not stat.S_ISLNK(item.external_attr >> 16)
                and not item.flag_bits & 1 and 0 < item.file_size <= MAX_RECORD,
                'non-regular, encrypted or oversized recovery record')
        with archive.open(item) as stream:
            content = stream.read(MAX_RECORD + 1)
        require(len(content) == item.file_size and len(content) <= MAX_RECORD, 'record read size')
        record = json.loads(content.decode('utf-8'))
    require(isinstance(record, dict) and record.get('schema') == f'main-check-{kind}/v1', 'record schema')
    require(record.get('repository_id') == repo_id and record.get('recovery_run') == run
            and record.get('recovery_attempt') == attempt
            and record.get('program_commit') == publisher['head_sha'], 'record execution binding')
    return record


def _ancestor(api, older, newer):
    require(isinstance(older, str) and SHA.fullmatch(older)
            and isinstance(newer, str) and SHA.fullmatch(newer), 'Git identity')
    comparison = api.json(f'compare/{older}...{newer}')
    require((comparison.get('base_commit') or {}).get('sha') == older
            and (comparison.get('merge_base_commit') or {}).get('sha') == older
            and type(comparison.get('behind_by')) is int and comparison['behind_by'] == 0
            and comparison.get('status') in ('ahead', 'identical'), 'untrusted recovery program ancestry')


def discover_recovery_intents(api, repo, run_id, attempt, *, activation_commit, current_main):
    """Read one original execution, including earlier attempts of rerun workflows.

    Enumeration of all historical recovery executions remains the caller's
    responsibility. An error here is unresolved evidence, never proof that no
    request was made. Returned records still need actual-run reconciliation.
    """
    require(type(run_id) is int and run_id > 0 and type(attempt) is int and attempt > 0,
            'execution identity')
    metadata = api.json('')
    require(metadata.get('full_name') == repo and metadata.get('default_branch') == 'main', 'repository identity')
    repo_id = metadata.get('id')
    require(type(repo_id) is int and repo_id > 0, 'repository ID')
    latest = api.json(f'actions/runs/{run_id}')
    require(latest.get('id') == run_id and type(latest.get('run_attempt')) is int
            and attempt <= latest['run_attempt'], 'run attempt identity')
    original = latest if attempt == latest['run_attempt'] else api.json(f'actions/runs/{run_id}/attempts/{attempt}')
    require(original.get('id') == run_id and original.get('run_attempt') == attempt
            and (original.get('repository') or {}).get('id') == repo_id
            and (original.get('repository') or {}).get('full_name') == repo
            and (original.get('head_repository') or {}).get('id') == repo_id
            and original.get('path') == WORKFLOW and original.get('head_branch') == 'main'
            and original.get('event') in ('schedule', 'workflow_run'), 'untrusted recovery executor')
    _ancestor(api, activation_commit, original.get('head_sha'))
    _ancestor(api, original['head_sha'], current_main)
    jobs = pages(api, f'actions/runs/{run_id}/attempts/{attempt}/jobs', 'jobs', identity='id')
    candidates = [job for job in jobs if job.get('name') == JOB]
    require(len(candidates) == 1, 'missing or ambiguous recovery job')
    job = candidates[0]
    require(job.get('run_id') == run_id and job.get('run_attempt') == attempt, 'recovery job identity')
    steps = job.get('steps') or []
    uploads = [step for step in steps if step.get('name') == UPLOAD]
    dispatches = [step for step in steps if step.get('name') == DISPATCH]
    require(len(uploads) == 1 and len(dispatches) == 1, 'missing or ambiguous dispatch steps')
    uploaded, dispatched = uploads[0], dispatches[0]
    require(uploaded.get('status') == 'completed' and uploaded.get('conclusion') == 'success'
            and type(uploaded.get('number')) is int and type(dispatched.get('number')) is int
            and uploaded['number'] < dispatched['number'], 'intent was not durably uploaded first')
    artifacts = pages(api, f'actions/runs/{run_id}/artifacts', 'artifacts', identity='id')
    records, provenance = {}, {}
    for kind in ('intents', 'results'):
        matches = [a for a in artifacts if a.get('name') == f'protocol-b-main-{kind}-{run_id}-{attempt}']
        require(len(matches) <= 1, 'ambiguous recovery artifact')
        if not matches:
            require(kind == 'results', 'missing durable intent artifact')
            records[kind] = None
            continue
        artifact = matches[0]
        require(artifact.get('expired') is False, 'expired recovery artifact')
        size = artifact.get('size_in_bytes')
        require(type(size) is int and 0 < size <= MAX_ZIP, 'declared archive size')
        records[kind] = _record(api.bytes(f"actions/artifacts/{artifact['id']}/zip"), artifact, original, repo_id, kind)
        provenance[kind] = {'id': artifact['id'], 'digest': artifact['digest']}
    intents = records['intents'].get('operations')
    require(isinstance(intents, list) and len(intents) <= 100, 'intent operation bound')
    selected = {}
    for intent in intents:
        require(isinstance(intent, dict) and intent.get('schema') == 'main-check-intent/v1', 'intent schema')
        operation = intent.get('operation')
        key = operation_key(operation)
        require(operation['repository'] == repo and intent.get('operation_key') == key
                and intent.get('request') == {'ref': 'main', 'return_run_details': True}
                and intent.get('recovery_run') == run_id and intent.get('recovery_attempt') == attempt,
                'intent operation binding')
        require(key not in selected, 'duplicate operation intent')
        selected[key] = {'intent': intent, 'receipt': None}
    results_persisted = False
    if records['results'] is not None:
        final_uploads = [step for step in steps if step.get('name') == RESULTS_UPLOAD]
        require(len(final_uploads) == 1 and final_uploads[0].get('status') == 'completed'
                and final_uploads[0].get('conclusion') == 'success'
                and type(final_uploads[0].get('number')) is int
                and final_uploads[0]['number'] > dispatched['number']
                and dispatched.get('status') == 'completed', 'results not uploaded after dispatcher finished')
        results_persisted = True
        receipts = records['results'].get('receipts')
        require(isinstance(receipts, list) and len(receipts) <= 100, 'receipt operation bound')
        for receipt in receipts:
            require(isinstance(receipt, dict) and receipt.get('schema') == 'main-check-receipt/v1', 'receipt schema')
            key = receipt.get('operation_key')
            require(key in selected and selected[key]['receipt'] is None
                    and receipt.get('recovery_run') == run_id and receipt.get('recovery_attempt') == attempt,
                    'orphan, duplicate or misbound receipt')
            selected[key]['receipt'] = receipt
    return {'publisher': original, 'job': job, 'operations': selected, 'artifacts': provenance,
            'dispatch_step': DISPATCH, 'dispatch_authorized': False,
            'executor_terminal': job.get('status') == 'completed',
            'results_persisted_after_dispatch': results_persisted}

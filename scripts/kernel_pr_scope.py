#!/usr/bin/env python3
"""Conservative PR-only kernel skip decision; embedded before checkout in CI.

No candidate source is executed. Unknown inputs, malformed API responses and
incomplete/racing diffs all request the full build. See docs/kernel-ci-scope.md.
"""
import base64
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import urllib.parse
import urllib.request
import zipfile


def api(repo, path):
    req = urllib.request.Request('https://api.github.com/repos/' + repo + path,
        headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                 'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'})
    with urllib.request.urlopen(req, timeout=30) as response:
        return json.load(response)


def valid_path(path):
    return (isinstance(path, str) and bool(path) and not path.startswith('/')
            and '\\' not in path and ':' not in path
            and all(p not in {'', '.', '..'} for p in path.split('/')))


def contract_paths(repo, sha):
    value = api(repo, '/contents/KERNEL_CONTRACT.json?ref=' + sha)
    if value.get('type') != 'file' or value.get('encoding') != 'base64':
        raise ValueError('Kernel contract is not an inline regular file')
    contract = json.loads(base64.b64decode(value['content']))
    files = contract['files']
    if contract.get('schema') != 'kernel-contract/v1' or not isinstance(files, dict) or not files:
        raise ValueError('Missing or unknown kernel contract')
    if not all(valid_path(p) and isinstance(h, str) and re.fullmatch(r'[0-9a-f]{64}', h)
               for p, h in files.items()):
        raise ValueError('Malformed kernel contract entries')
    return set(files)


def affects_kernel(path, locked):
    if not valid_path(path):
        return True
    name = PurePosixPath(path).name
    # validate() scans ALL tracked Lean sources and lakefiles for bypass options.
    if (path in locked or path.endswith('.lean')
            or name in {'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'KERNEL_CONTRACT.json'}
            or path.startswith(('ZInQKernel/', 'ThirdParty/', 'lean/', 'scripts/', '.lake/', 'build/kernel-ci/'))
            or path in {'.gitattributes', '.gitmodules', '.github/workflows/kernel-lean.yml'}):
        return True
    # These independent review-gate sources/tests do not feed the kernel job.
    if path in {'.github/workflows/protocol-b.yml', '.github/protocol-b-reviewer.md'}:
        return False
    if path.startswith('tests/protocol_b/') and path.endswith('.py'):
        return False
    if path.startswith(('.github/', 'tests/', 'build/')):
        return True
    # Only ordinary documentation formats qualify for the remaining skip path.
    # Data, archives, executables and any unrecognized extension run the build.
    return PurePosixPath(path).suffix.lower() not in {'.md', '.tex', '.bib', '.pdf'}


WORKFLOW = '.github/workflows/kernel-lean.yml'
JOB = 'Complete kernel build and exact-target audit'


def sha(value):
    if not isinstance(value, str) or not re.fullmatch('[0-9a-f]{40}', value):
        raise ValueError('Invalid Git object identity')
    return value


def commit(repo, ident):
    value = api(repo, '/git/commits/' + sha(ident))
    if value.get('sha') != ident:
        raise ValueError('Commit identity mismatch')
    sha(value['tree']['sha'])
    for parent in value['parents']:
        sha(parent['sha'])
    return value


def input_manifest(repo, ident):
    """Re-derive the entire conservative input set, including modes and deletions."""
    source = commit(repo, ident)
    tree_id = source['tree']['sha']
    tree = api(repo, '/git/trees/' + tree_id + '?recursive=1')
    if tree.get('sha') != tree_id or tree.get('truncated') is not False:
        raise ValueError('Incomplete Git tree')
    locked = contract_paths(repo, ident)
    entries, seen = [], set()
    for row in tree['tree']:
        path = row['path']
        if not valid_path(path) or path in seen:
            raise ValueError('Malformed or duplicate tree path')
        seen.add(path)
        sha(row['sha'])
        if row['type'] == 'tree' and row['mode'] == '040000':
            continue
        # Do not reason through symlinks or submodules, even at documentation paths.
        if row['type'] != 'blob' or row['mode'] not in {'100644', '100755'}:
            raise ValueError('Unsupported tree entry')
        if affects_kernel(path, locked):
            entries.append([path, row['mode'], row['type'], row['sha']])
    if not locked <= seen or not any(r[0] == WORKFLOW for r in entries):
        raise ValueError('Kernel inputs are missing')
    entries.sort()
    digest = hashlib.sha256(json.dumps(entries, separators=(',', ':'), ensure_ascii=True).encode()).hexdigest()
    return {'schema': 'kernel-inputs/v1', 'digest': digest, 'entries': entries}


def source_bytes(repo, path, ident):
    value = api(repo, '/contents/' + path + '?ref=' + sha(ident))
    if value.get('type') != 'file' or value.get('encoding') != 'base64':
        raise ValueError('Source is not an inline regular file')
    return base64.b64decode(value['content'])


def artifact_bytes(repo, ident):
    # Artifact downloads redirect to object storage. Do not forward the token.
    class NoAuthRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, req, fp, code, msg, headers, newurl):
            new = super().redirect_request(req, fp, code, msg, headers, newurl)
            if new is not None:
                new.remove_header('Authorization')
            return new
    request = urllib.request.Request(f'https://api.github.com/repos/{repo}/actions/artifacts/{ident}/zip',
        headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                 'Accept': 'application/vnd.github+json'})
    with urllib.request.build_opener(NoAuthRedirect()).open(request, timeout=60) as response:
        data = response.read(100_000_001)
    if len(data) > 100_000_000:
        raise ValueError('Artifact too large')
    return data


def read_artifact(repo, artifact, run, filename, limit):
    if (artifact.get('workflow_run', {}).get('id') != run['id']
            or artifact['workflow_run'].get('head_sha') != run['head_sha']
            or not run['run_started_at'] <= artifact['created_at'] <= run['updated_at']):
        raise ValueError('Artifact does not bind the current run attempt')
    data = artifact_bytes(repo, artifact['id'])
    if (artifact.get('digest') != 'sha256:' + hashlib.sha256(data).hexdigest()
            or artifact['size_in_bytes'] != len(data)):
        raise ValueError('Artifact digest or size mismatch')
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        if archive.namelist().count(filename) != 1 or archive.getinfo(filename).file_size > limit:
            raise ValueError('Missing or oversized artifact record')
        return json.loads(archive.read(filename))


def full_run_audit(repo, run, producer):
    """Authenticate a full execution; a reuse/skip run is never a supplier."""
    if (run.get('event') != 'pull_request' or run.get('status') != 'completed'
            or run.get('conclusion') != 'success' or run.get('path') != WORKFLOW
            or run.get('repository', {}).get('full_name') != repo):
        raise ValueError('Not a successful PR kernel run in this repository')
    head = sha(run['head_sha'])
    if source_bytes(repo, WORKFLOW, head) != producer:
        raise ValueError('Different workflow producer')
    attempt = run['run_attempt']
    if type(attempt) is not int or attempt < 1:
        raise ValueError('Invalid run attempt')
    jobs = api(repo, f'/actions/runs/{run["id"]}/attempts/{attempt}/jobs?per_page=100')
    if jobs['total_count'] != len(jobs['jobs']):
        raise ValueError('Incomplete jobs')
    candidates = [j for j in jobs['jobs'] if j['name'] == JOB]
    if len(candidates) != 1 or candidates[0]['conclusion'] != 'success':
        raise ValueError('Missing successful kernel job')
    steps = candidates[0]['steps']
    def step(name, conclusion):
        found = [s for s in steps if s['name'] == name]
        return len(found) == 1 and found[0]['status'] == 'completed' and found[0]['conclusion'] == conclusion
    for name in ['Preserve kernel scope decision', 'Validate source contract', 'Test rejection of invalid proofs',
                 'Build all modules and replay kernel proofs', 'Upload proof-status evidence']:
        if not step(name, 'success'):
            raise ValueError('Supplier did not perform every required full-build step')
    for name in ['Restore project build outputs', 'Save successful main build outputs']:
        if not step(name, 'skipped'):
            raise ValueError('Supplier used project cache or ambiguous cache provenance')
    listing = api(repo, f'/actions/runs/{run["id"]}/artifacts?per_page=100')
    if listing['total_count'] != len(listing['artifacts']):
        raise ValueError('Incomplete artifacts')
    def unique(name):
        matches = [a for a in listing['artifacts'] if a['name'] == name and not a['expired']]
        if len(matches) != 1:
            raise ValueError('Missing unique unexpired artifact')
        return matches[0]
    artifact = unique('kernel-audit')
    scope_artifact = unique('kernel-scope-' + str(attempt))
    uploads = [s for s in steps if s['name'] == 'Preserve kernel scope decision']
    checkouts = [s for s in steps if s['name'] == 'Check out candidate']
    if len(checkouts) != 1:
        raise ValueError('Missing unique checkout step')
    upload, checkout = uploads[0], checkouts[0]
    # A replacement uploaded by candidate code has a later creation time and a
    # new immutable artifact ID. Ambiguous same-second timing does not qualify.
    if (upload['number'] >= checkout['number']
            or not upload['started_at'] <= scope_artifact['created_at'] <= upload['completed_at']
            or not scope_artifact['created_at'] < checkout['started_at']
            or upload['completed_at'] > checkout['started_at']):
        raise ValueError('Scope artifact was not preserved before candidate checkout')
    before = read_artifact(repo, scope_artifact, run, 'kernel-scope.json', 100_000)
    provenance = before.get('execution') or {}
    if (before.get('full_build') is not True or before.get('reused') is not None
            or provenance.get('schema') != 'kernel-execution/v1'
            or provenance.get('run') != run['id'] or provenance.get('attempt') != attempt
            or provenance.get('head') != head
            or provenance.get('workflow_sha256') != hashlib.sha256(producer).hexdigest()):
        raise ValueError('Invalid pre-checkout execution record')
    executed = sha(provenance['execution_sha'])
    actual, original = commit(repo, executed), commit(repo, head)
    if ([p['sha'] for p in actual['parents']] != [provenance['base'], head]
            or actual['tree'] != original['tree']):
        raise ValueError('Prior head was not the complete tree that was built')
    if input_manifest(repo, executed)['digest'] != provenance.get('input_digest'):
        raise ValueError('Pre-checkout input digest does not match Git objects')
    if source_bytes(repo, WORKFLOW, executed) != producer:
        raise ValueError('Execution used a different workflow producer')
    audit = read_artifact(repo, artifact, run, 'audit.json', 20_000_000)
    if audit.get('schema') != 'kernel-audit/v1' or audit.get('status') != 'passed':
        raise ValueError('Audit did not pass')
    if audit.get('head_sha') != executed:
        raise ValueError('Audit commit differs from the pre-checkout execution record')
    if hashlib.sha256(source_bytes(repo, 'KERNEL_CONTRACT.json', executed)).hexdigest() != audit['contract_sha256']:
        raise ValueError('Audit contract mismatch')
    return {'run': run['id'], 'attempt': attempt, 'run_head': head, 'execution_sha': executed,
            'artifact': artifact['id'], 'artifact_digest': artifact['digest'],
            'scope_artifact': scope_artifact['id'], 'scope_digest': scope_artifact['digest']}


def execution_provenance(repo, event, execution, run, attempt):
    pr = event['pull_request']
    base, head = sha(pr['base']['sha']), sha(pr['head']['sha'])
    merge = commit(repo, execution)
    if [p['sha'] for p in merge['parents']] != [base, head]:
        raise ValueError('Current execution is not the event merge commit')
    return {'schema': 'kernel-execution/v1', 'run': run, 'attempt': attempt,
            'execution_sha': execution, 'head': head, 'base': base,
            'workflow_sha256': hashlib.sha256(source_bytes(repo, WORKFLOW, execution)).hexdigest(),
            'input_digest': input_manifest(repo, execution)['digest']}


def reusable_run(repo, event, execution, current_run):
    """Return a same-history, equal-input full run, or conservatively build."""
    pr = event['pull_request']
    base, head = sha(pr['base']['sha']), sha(pr['head']['sha'])
    merge = commit(repo, execution)
    if [p['sha'] for p in merge['parents']] != [base, head]:
        raise ValueError('Current execution is not the event merge commit')
    producer = source_bytes(repo, WORKFLOW, execution)
    if producer != source_bytes(repo, WORKFLOW, base):
        return None  # A changed producer earns fresh evidence before any reuse.
    manifest = input_manifest(repo, execution)
    listing = api(repo, '/actions/workflows/kernel-lean.yml/runs?event=pull_request&status=success&per_page=20')
    for item in listing['workflow_runs']:
        if item['id'] == current_run:
            continue
        run = api(repo, '/actions/runs/' + str(item['id']))
        old_head = sha(run['head_sha'])
        comparison = api(repo, '/compare/' + old_head + '...' + head)
        if (comparison.get('behind_by') != 0
                or comparison.get('merge_base_commit', {}).get('sha') != old_head):
            continue
        if source_bytes(repo, WORKFLOW, old_head) != producer:
            continue
        if input_manifest(repo, old_head) != manifest:
            continue
        evidence = full_run_audit(repo, run, producer)
        latest = api(repo, '/actions/runs/' + str(run['id']))
        if (latest['run_attempt'] != run['run_attempt'] or latest['status'] != 'completed'
                or latest['conclusion'] != 'success'):
            raise ValueError('Supplier run changed during validation')
        # Recheck live PR identity before declaring a successful skip.
        current = api(repo, '/pulls/' + str(pr['number']))
        if current['head']['sha'] != head or current['base']['sha'] != base:
            raise ValueError('PR changed during evidence validation')
        return {**evidence, 'current_execution_sha': execution,
                'current_head': head, 'current_base': base, 'input_digest': manifest['digest']}
    return None


def decide(event_name, event, repo):
    if event_name != 'pull_request':
        return True, 'Pushes and manual runs always perform the full kernel build.', []
    pr = event['pull_request']
    number, base, head = pr['number'], pr['base']['sha'], pr['head']['sha']
    if type(number) is not int or number < 1 or not all(re.fullmatch(r'[0-9a-f]{40}', s) for s in [base, head]):
        raise ValueError('Invalid PR identity')
    if not re.fullmatch(r'[\w.-]+/[\w.-]+', repo):
        raise ValueError('Invalid repository')
    current = api(repo, f'/pulls/{number}')
    def same_revision(value):
        return value['base']['sha'] == base and value['head']['sha'] == head
    if not same_revision(current):
        raise ValueError('PR base or head changed')
    count = current['changed_files']
    if type(count) is not int or not 1 <= count <= 3000:
        raise ValueError('Unavailable or oversized changed-file list')
    rows = []
    for page in range(1, (count + 99) // 100 + 1):
        batch = api(repo, f'/pulls/{number}/files?per_page=100&page={page}')
        if not isinstance(batch, list):
            raise ValueError('Invalid changed-file page')
        rows.extend(batch)
    if len(rows) != count or len({r['filename'] for r in rows}) != count:
        raise ValueError('Incomplete or duplicate changed-file list')
    paths = set()
    for row in rows:
        if row.get('status') not in {'added', 'removed', 'modified', 'renamed', 'copied', 'changed'}:
            raise ValueError('Ambiguous change status')
        paths.add(row['filename'])
        if row['status'] == 'renamed':
            paths.add(row['previous_filename'])
    if not all(valid_path(p) for p in paths):
        raise ValueError('Invalid changed path')
    locked = contract_paths(repo, base) | contract_paths(repo, head)
    if not same_revision(api(repo, f'/pulls/{number}')):
        raise ValueError('PR changed during classification')
    affected = sorted(p for p in paths if affects_kernel(p, locked))
    if affected:
        return True, 'Kernel inputs or unclassified files changed: ' + ', '.join(affected[:10]), sorted(paths)
    return False, 'Only documentation or independent Protocol B files changed; no kernel build or audit input changed.', sorted(paths)


def main():
    reused = None
    execution = None
    try:
        event_name = os.environ.get('GITHUB_EVENT_NAME', '')
        event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text()) if event_name == 'pull_request' else {}
        full, reason, paths = decide(event_name, event, os.environ.get('GITHUB_REPOSITORY', ''))
        if full and event_name == 'pull_request':
            execution = execution_provenance(os.environ['GITHUB_REPOSITORY'], event,
                sha(os.environ['GITHUB_SHA']), int(os.environ['GITHUB_RUN_ID']), int(os.environ['GITHUB_RUN_ATTEMPT']))
            reused = reusable_run(os.environ['GITHUB_REPOSITORY'], event,
                                  sha(os.environ['GITHUB_SHA']), int(os.environ['GITHUB_RUN_ID']))
            if reused:
                full = False
                reason = (f"Reused full kernel run {reused['run']} attempt {reused['attempt']}; "
                          f"input digest {reused['input_digest']}. Original execution "
                          f"{reused['execution_sha']}; current execution {reused['current_execution_sha']}. "
                          'No build outputs were restored. Any original base progress comparison is historical.')
    except Exception as error:
        detail = str(error).replace('\n', ' ').replace('\r', ' ')[:500]
        full, reason, paths = True, ('Could not safely classify the PR; performing the full build ('
                                     + type(error).__name__ + ': ' + detail + ').'), []
        reused = None
    record = {'full_build': full, 'reason': reason, 'changed_paths': paths, 'reused': reused, 'execution': execution}
    print(json.dumps(record))
    Path(os.environ['RUNNER_TEMP'], 'kernel-scope.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    with open(os.environ['GITHUB_OUTPUT'], 'a', encoding='utf-8') as out:
        out.write('full_build=' + str(full).lower() + '\n')
    with open(os.environ['GITHUB_STEP_SUMMARY'], 'a', encoding='utf-8') as summary:
        summary.write(('Full kernel build required. ' if full else 'Kernel build skipped. ') + reason + '\n')


if __name__ == '__main__':
    main()

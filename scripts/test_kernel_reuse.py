"""Offline regression cases for authenticated kernel evidence reuse."""
import base64
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import kernel_pr_scope as scope

OLD, BASE, HEAD, EXEC, OLD_EXEC = [c * 40 for c in 'abcde']
TREE = 'f' * 40
REPO = 'owner/project'


class ReuseTests(unittest.TestCase):
    def setUp(self):
        self.producer = b'fixed reviewed producer'
        self.contract = json.dumps({'schema': 'kernel-contract/v1',
            'files': {'ZInQKernel.lean': '0' * 64}}).encode()
        self.event = {'pull_request': {'number': 12, 'base': {'sha': BASE}, 'head': {'sha': HEAD}}}
        self.run = {'id': 20, 'event': 'pull_request', 'status': 'completed', 'conclusion': 'success',
            'path': scope.WORKFLOW, 'repository': {'full_name': REPO}, 'head_sha': OLD,
            'run_attempt': 1, 'run_started_at': '2026-11-16T00:00:00Z', 'updated_at': '2026-11-16T02:00:00Z'}
        self.audit = {'schema': 'kernel-audit/v1', 'status': 'passed', 'head_sha': OLD_EXEC,
                      'contract_sha256': hashlib.sha256(self.contract).hexdigest()}
        self.steps = [{'name': name, 'status': 'completed', 'conclusion': 'success'} for name in
            ['Validate source contract', 'Test rejection of invalid proofs',
             'Build all modules and replay kernel proofs', 'Upload proof-status evidence']]
        self.steps += [{'name': name, 'status': 'completed', 'conclusion': 'skipped'} for name in
                      ['Restore project build outputs', 'Save successful main build outputs']]
        self.steps += [{'name': 'Preserve kernel scope decision', 'status': 'completed', 'conclusion': 'success',
                        'number': 3, 'started_at': '2026-11-16T00:00:01Z', 'completed_at': '2026-11-16T00:00:03Z'},
                       {'name': 'Check out candidate', 'status': 'completed', 'conclusion': 'success',
                        'number': 5, 'started_at': '2026-11-16T00:00:04Z', 'completed_at': '2026-11-16T00:00:15Z'}]
        self.tree = [{'path': scope.WORKFLOW, 'mode': '100644', 'type': 'blob', 'sha': '1' * 40},
                     {'path': 'ZInQKernel.lean', 'mode': '100644', 'type': 'blob', 'sha': '2' * 40},
                     {'path': 'KERNEL_CONTRACT.json', 'mode': '100644', 'type': 'blob', 'sha': '3' * 40},
                     {'path': 'README.md', 'mode': '100644', 'type': 'blob', 'sha': '4' * 40}]
        self.overrides = {}
        self.pack()
        with patch.object(scope, 'api', side_effect=self.api):
            digest = scope.input_manifest(REPO, OLD_EXEC)['digest']
        self.scope_record = {'full_build': True, 'reused': None, 'execution': {
            'schema': 'kernel-execution/v1', 'run': 20, 'attempt': 1, 'head': OLD,
            'base': BASE, 'execution_sha': OLD_EXEC, 'input_digest': digest,
            'workflow_sha256': hashlib.sha256(self.producer).hexdigest()}}
        self.pack_scope()

    def pack(self):
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as archive:
            archive.writestr('audit.json', json.dumps(self.audit))
        self.blob = stream.getvalue()
        self.artifact = {'id': 30, 'name': 'kernel-audit', 'expired': False,
            'workflow_run': {'id': 20, 'head_sha': OLD}, 'created_at': '2026-11-16T01:59:00Z',
            'size_in_bytes': len(self.blob), 'digest': 'sha256:' + hashlib.sha256(self.blob).hexdigest()}

    def pack_scope(self):
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as archive:
            archive.writestr('kernel-scope.json', json.dumps(self.scope_record))
        self.scope_blob = stream.getvalue()
        self.scope_artifact = {'id': 31, 'name': 'kernel-scope-1', 'expired': False,
            'workflow_run': {'id': 20, 'head_sha': OLD}, 'created_at': '2026-11-16T00:00:02Z',
            'size_in_bytes': len(self.scope_blob), 'digest': 'sha256:' + hashlib.sha256(self.scope_blob).hexdigest()}

    def api(self, repo, path):
        self.assertEqual(repo, REPO)
        if path in self.overrides:
            value = self.overrides[path]
            if isinstance(value, Exception):
                raise value
            return copy.deepcopy(value)
        if path.startswith('/git/commits/'):
            ident = path.rsplit('/', 1)[1]
            parents = [BASE, HEAD] if ident == EXEC else [BASE, OLD] if ident == OLD_EXEC else []
            return {'sha': ident, 'tree': {'sha': TREE}, 'parents': [{'sha': p} for p in parents]}
        if path.startswith('/git/trees/'):
            return {'sha': TREE, 'truncated': False, 'tree': copy.deepcopy(self.tree)}
        if path.startswith('/contents/'):
            data = self.contract if 'KERNEL_CONTRACT.json' in path else self.producer
            return {'type': 'file', 'encoding': 'base64', 'content': base64.b64encode(data).decode()}
        if path.startswith('/actions/workflows/'):
            return {'workflow_runs': [copy.deepcopy(self.run)]}
        if path == '/actions/runs/20':
            return copy.deepcopy(self.run)
        if path.startswith('/actions/runs/20/attempts/'):
            return {'total_count': 1, 'jobs': [{'name': scope.JOB, 'conclusion': 'success', 'steps': self.steps}]}
        if path == '/actions/runs/20/artifacts?per_page=100':
            return {'total_count': 2, 'artifacts': [copy.deepcopy(self.artifact), copy.deepcopy(self.scope_artifact)]}
        if path.startswith('/compare/'):
            return {'behind_by': 0, 'merge_base_commit': {'sha': OLD}}
        if path == '/pulls/12':
            return copy.deepcopy(self.event['pull_request'])
        raise AssertionError(path)

    def reuse(self):
        with patch.object(scope, 'api', side_effect=self.api), patch.object(scope, 'artifact_bytes',
                side_effect=lambda repo, ident: self.blob if ident == 30 else self.scope_blob):
            return scope.reusable_run(REPO, self.event, EXEC, 99)

    def test_equal_inputs_reuse_full_run_with_original_and_current_commits(self):
        result = self.reuse()
        self.assertEqual((result['run'], result['execution_sha'], result['current_execution_sha']), (20, OLD_EXEC, EXEC))

    def test_document_changes_do_not_change_input_digest(self):
        with patch.object(scope, 'api', side_effect=self.api):
            before = scope.input_manifest(REPO, EXEC)
            self.tree[-1]['sha'] = '9' * 40
            self.assertEqual(before, scope.input_manifest(REPO, EXEC))

    def test_changed_added_removed_or_mode_changed_input_changes_digest(self):
        with patch.object(scope, 'api', side_effect=self.api):
            before = scope.input_manifest(REPO, EXEC)
            original = copy.deepcopy(self.tree)
            for variant in ('change', 'add', 'remove', 'mode'):
                self.tree = copy.deepcopy(original)
                if variant == 'change': self.tree[1]['sha'] = '9' * 40
                if variant == 'mode': self.tree[1]['mode'] = '100755'
                if variant == 'add': self.tree.append({'path': 'new.dat', 'mode': '100644', 'type': 'blob', 'sha': '9' * 40})
                if variant == 'remove': self.tree.pop(1)
                with self.subTest(variant=variant):
                    if variant == 'remove':
                        with self.assertRaises(ValueError): scope.input_manifest(REPO, EXEC)
                    else: self.assertNotEqual(before, scope.input_manifest(REPO, EXEC))

    def test_missing_or_truncated_tree_never_reuses(self):
        self.overrides['/git/trees/' + TREE + '?recursive=1'] = {'sha': TREE, 'truncated': True, 'tree': self.tree}
        with self.assertRaises(ValueError): self.reuse()

    def test_symlink_even_at_documentation_path_never_reuses(self):
        self.tree[-1]['mode'] = '120000'
        with self.assertRaises(ValueError): self.reuse()

    def test_changed_producer_and_unrelated_history_do_not_reuse(self):
        self.overrides['/contents/' + scope.WORKFLOW + '?ref=' + BASE] = {
            'type': 'file', 'encoding': 'base64', 'content': base64.b64encode(b'older').decode()}
        self.assertIsNone(self.reuse())
        self.overrides.clear()
        self.overrides['/compare/' + OLD + '...' + HEAD] = {'behind_by': 1, 'merge_base_commit': {'sha': BASE}}
        self.assertIsNone(self.reuse())

    def test_fabricated_execution_commit_and_nonmatching_merge_tree_rejected(self):
        self.audit['head_sha'] = '8' * 40
        self.pack()
        with self.assertRaises(ValueError): self.reuse()
        self.audit['head_sha'] = OLD_EXEC
        self.pack()
        self.overrides['/git/commits/' + OLD_EXEC] = {'sha': OLD_EXEC, 'tree': {'sha': '8' * 40},
            'parents': [{'sha': BASE}, {'sha': OLD}]}
        with self.assertRaises(ValueError): self.reuse()

    def test_forged_digest_old_attempt_and_wrong_repository_rejected(self):
        for field, value in [('digest', 'sha256:wrong'), ('created_at', '2026-11-15T00:00:00Z')]:
            self.pack()
            self.artifact[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): self.reuse()
        self.pack()
        self.run['repository']['full_name'] = 'outsider/fork'
        with self.assertRaises(ValueError): self.reuse()

    def test_expired_original_record_and_replacement_after_checkout_rejected(self):
        self.scope_artifact['expired'] = True
        with self.assertRaises(ValueError): self.reuse()
        self.scope_artifact['expired'] = False
        self.scope_artifact['created_at'] = '2026-11-16T00:00:05Z'
        with self.assertRaises(ValueError): self.reuse()

    def test_equal_second_is_rejected_and_separated_upload_is_accepted(self):
        checkout = next(s for s in self.steps if s['name'] == 'Check out candidate')
        self.assertEqual(self.reuse()['run'], 20)
        self.scope_artifact['created_at'] = checkout['started_at']
        with self.assertRaisesRegex(ValueError, 'before candidate checkout'): self.reuse()
        self.scope_artifact['created_at'] = '2026-11-16T00:00:02Z'
        self.assertEqual(self.reuse()['run'], 20)

    def test_forged_audit_cannot_replace_precheckout_commit(self):
        # An API-resolvable crafted commit may have the correct parents/tree.
        # It still was not the commit saved by the trusted pre-checkout step.
        crafted = '8' * 40
        self.overrides['/git/commits/' + crafted] = {'sha': crafted, 'tree': {'sha': TREE},
            'parents': [{'sha': BASE}, {'sha': OLD}]}
        self.audit['head_sha'] = crafted
        self.pack()
        with self.assertRaisesRegex(ValueError, 'pre-checkout execution record'): self.reuse()

    def test_repeated_documentation_advances_reuse_original_full_run(self):
        for head in [HEAD, '7' * 40]:
            self.event['pull_request']['head']['sha'] = head
            self.overrides['/git/commits/' + EXEC] = {'sha': EXEC, 'tree': {'sha': TREE},
                'parents': [{'sha': BASE}, {'sha': head}]}
            self.assertEqual(self.reuse()['run'], 20)

    def test_failed_or_reuse_only_job_and_project_cache_rejected(self):
        for name, conclusion in [('Build all modules and replay kernel proofs', 'skipped'),
                                 ('Validate source contract', 'failure'),
                                 ('Restore project build outputs', 'success')]:
            old = copy.deepcopy(self.steps)
            next(s for s in self.steps if s['name'] == name)['conclusion'] = conclusion
            with self.subTest(name=name), self.assertRaises(ValueError): self.reuse()
            self.steps = old

    def test_error_and_unexpected_current_merge_fail_closed(self):
        self.overrides['/pulls/12'] = OSError('API unavailable')
        with self.assertRaises(OSError): self.reuse()
        self.overrides.clear()
        self.overrides['/git/commits/' + EXEC] = {'sha': EXEC, 'tree': {'sha': TREE}, 'parents': []}
        with self.assertRaises(ValueError): self.reuse()

    def test_main_push_and_manual_never_attempt_reuse(self):
        with tempfile.TemporaryDirectory() as directory:
            env = {'RUNNER_TEMP': directory, 'GITHUB_OUTPUT': str(Path(directory)/'output'),
                   'GITHUB_STEP_SUMMARY': str(Path(directory)/'summary')}
            for event in ('push', 'workflow_dispatch'):
                with patch.dict(os.environ, {**env, 'GITHUB_EVENT_NAME': event}), patch.object(scope, 'reusable_run') as reuse:
                    scope.main()
                    reuse.assert_not_called()
                    self.assertTrue(json.loads((Path(directory)/'kernel-scope.json').read_text())['full_build'])

    def test_unavailable_reuse_evidence_falls_back_to_a_full_build(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'event.json').write_text(json.dumps(self.event))
            env = {'RUNNER_TEMP': directory, 'GITHUB_OUTPUT': str(root/'output'),
                'GITHUB_STEP_SUMMARY': str(root/'summary'), 'GITHUB_EVENT_NAME': 'pull_request',
                'GITHUB_EVENT_PATH': str(root/'event.json'), 'GITHUB_REPOSITORY': REPO,
                'GITHUB_SHA': EXEC, 'GITHUB_RUN_ID': '99', 'GITHUB_RUN_ATTEMPT': '1'}
            with patch.dict(os.environ, env), patch.object(scope, 'decide', return_value=(True, 'source change', ['ZInQKernel.lean'])), \
                    patch.object(scope, 'execution_provenance', return_value={}), \
                    patch.object(scope, 'reusable_run', side_effect=OSError('expired or unavailable')):
                scope.main()
            self.assertEqual((root/'output').read_text(), 'full_build=true\n')
            self.assertIsNone(json.loads((root/'kernel-scope.json').read_text())['reused'])


if __name__ == '__main__':
    unittest.main()

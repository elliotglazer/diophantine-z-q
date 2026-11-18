"""Execute the exact trusted-code bootstrap with a fake GitHub read transport."""
import base64
import copy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import textwrap
import unittest
from unittest.mock import patch

REPOSITORY = Path(__file__).parents[3]
ROOT = REPOSITORY/'.github/protocol_b_main'
WORKFLOW = (REPOSITORY/'.github/workflows/protocol-b.yml').read_text()
FRAGMENT = WORKFLOW[WORKFLOW.index('\n  recover_main_checks:\n'):]
CODE = textwrap.dedent(FRAGMENT.split("python3 - <<'PY'\n", 1)[1].split('          PY\n', 1)[0])
REPO = 'elliotglazer/diophantine-z-q'
SHA = 'a'*40


class WorkflowBootstrap(unittest.TestCase):
    def fixture(self):
        manifest = json.loads((ROOT/'code-manifest.json').read_text())
        files = {name: (ROOT/name).read_bytes() for name in manifest['files']}
        actual = {'id': 17, 'run_attempt': 1, 'repository': {'full_name': REPO},
                  'head_repository': {'full_name': REPO}, 'head_branch': 'main', 'head_sha': SHA,
                  'path': '.github/workflows/protocol-b.yml', 'event': 'workflow_run'}
        return actual, manifest, files

    def execute(self, root, actual, manifest, files, *, overrides=None, alter=None):
        calls = []
        def output(args):
            self.assertEqual(args[:2], ['gh', 'api'])
            self.assertEqual(len(args), 3, 'Bootstrap only uses GET requests')
            path = args[2]
            calls.append(path)
            prefix = 'repos/'+REPO+'/'
            self.assertTrue(path.startswith(prefix))
            path = path[len(prefix):]
            if path == 'actions/runs/17':
                return json.dumps(actual).encode()
            content_prefix = 'contents/.github/protocol_b_main/'
            self.assertTrue(path.startswith(content_prefix))
            name, query = path[len(content_prefix):].split('?')
            self.assertEqual(query, 'ref='+SHA)
            raw = json.dumps(manifest).encode() if name == 'code-manifest.json' else files[name]
            value = {'encoding': 'base64', 'content': base64.b64encode(raw).decode()}
            if alter: value = alter(name, value)
            return json.dumps(value).encode()
        env = {'GITHUB_REPOSITORY': REPO, 'GITHUB_SHA': SHA, 'GITHUB_RUN_ID': '17',
               'GITHUB_RUN_ATTEMPT': '1', 'RUNNER_TEMP': str(root),
               'GITHUB_EVENT_PATH': str(root/'untrusted-event.json')}
        env.update(overrides or {})
        with patch.dict(os.environ, env), patch('subprocess.check_output', side_effect=output):
            exec(compile(CODE, '<actual-workflow-bootstrap>', 'exec'), {})
        return calls

    def test_progress_precedes_dispatch_and_empty_plans_do_not_upload_intents(self):
        progress=FRAGMENT.index('- name: Persist main-check recovery progress')
        intents=FRAGMENT.index('- name: Persist main-check dispatch intents')
        dispatch=FRAGMENT.index('- name: Dispatch confirmed main checks')
        self.assertLess(progress,intents);self.assertLess(intents,dispatch)
        self.assertIn("if: steps.recovery_prepare.outputs.has_operations == 'true'",FRAGMENT[intents:dispatch])
        self.assertIn("if: steps.recovery_prepare.outputs.has_operations == 'true'",FRAGMENT[dispatch:])
    def test_rerun_is_refused_before_any_bootstrap_read(self):
        with tempfile.TemporaryDirectory() as temp:
            actual,manifest,files=self.fixture();actual['run_attempt']=2
            with self.assertRaises(AssertionError):
                self.execute(Path(temp),actual,manifest,files,overrides={'GITHUB_RUN_ATTEMPT':'2'})
            self.assertFalse((Path(temp)/'protocol-b-main-code').exists())
        self.assertIn('github.run_attempt == 1',FRAGMENT)

    def test_downloads_only_exact_manifest_files_from_actual_main_sha(self):
        actual, manifest, files = self.fixture()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            calls = self.execute(root, actual, manifest, files)
            destination = root/'protocol-b-main-code'
            self.assertEqual({p.name for p in destination.iterdir()}, set(files))
            self.assertEqual(len(calls), 2+len(files))
            for name, raw in files.items():
                self.assertEqual((destination/name).read_bytes(), raw)
                self.assertEqual(hashlib.sha256(raw).hexdigest(), manifest['files'][name])

    def test_fork_branch_wrong_commit_workflow_event_and_attempt_are_refused(self):
        for change in ({'head_repository': {'full_name': 'attacker/fork'}},
                       {'repository': {'full_name': 'attacker/fork'}},
                       {'head_branch': 'contributor-branch'}, {'head_sha': 'b'*40},
                       {'path': '.github/workflows/candidate.yml'}, {'event': 'pull_request'},
                       {'run_attempt': 2}, {'id': 18}):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temp:
                actual, manifest, files = self.fixture()
                actual.update(change)
                with self.assertRaises(AssertionError):
                    self.execute(Path(temp), actual, manifest, files)
                self.assertFalse((Path(temp)/'protocol-b-main-code').exists())

    def test_wrong_environment_repository_sha_and_attempt_are_refused(self):
        for change in ({'GITHUB_REPOSITORY': 'attacker/fork'}, {'GITHUB_SHA': 'main'},
                       {'GITHUB_RUN_ATTEMPT': 'not-a-number'}, {'GITHUB_RUN_ID': '17/../../contents'}):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temp:
                with self.assertRaises(AssertionError):
                    self.execute(Path(temp), *self.fixture(), overrides=change)

    def test_untrusted_trigger_title_and_branch_are_never_read(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'untrusted-event.json').write_text(json.dumps({'workflow_run': {
                'head_branch': '../../attacker', 'head_sha': 'b'*40,
                'display_title': '$(exfiltrate secrets)', 'repository': {'full_name': 'attacker/fork'}}}))
            self.execute(root, *self.fixture())
            self.assertTrue((root/'protocol-b-main-code/recovery_entry.py').exists())

    def test_extra_missing_traversal_and_wrong_schema_manifests_are_refused(self):
        for change in ('extra', 'missing', 'traversal', 'schema'):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temp:
                actual, manifest, files = self.fixture()
                if change == 'extra': manifest['files']['unreviewed.py'] = '0'*64
                elif change == 'missing': manifest['files'].pop('recovery_entry.py')
                elif change == 'traversal': manifest['files']['../recovery_entry.py'] = manifest['files'].pop('recovery_entry.py')
                else: manifest['schema'] = 'unreviewed'
                with self.assertRaises(AssertionError):
                    self.execute(Path(temp), actual, manifest, files)
                self.assertFalse((Path(temp)/'protocol-b-main-code').exists())

    def test_hash_mismatch_stops_before_writing_the_changed_file(self):
        with tempfile.TemporaryDirectory() as temp:
            actual, manifest, files = self.fixture()
            files['dispatch_recovery.py'] += b'\nraise Exception("candidate")\n'
            with self.assertRaises(AssertionError):
                self.execute(Path(temp), actual, manifest, files)
            self.assertFalse((Path(temp)/'protocol-b-main-code/dispatch_recovery.py').exists())

    def test_preexisting_code_directory_is_not_reused(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'protocol-b-main-code').mkdir()
            sentinel = root/'protocol-b-main-code/recovery_entry.py'
            sentinel.write_text('untrusted earlier file')
            with self.assertRaises(FileExistsError):
                self.execute(root, *self.fixture())
            self.assertEqual(sentinel.read_text(), 'untrusted earlier file')

    def test_wrong_content_encoding_is_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(AssertionError):
                self.execute(Path(temp), *self.fixture(), alter=lambda name, value: {**value, 'encoding': 'none'})

    def test_job_has_no_environment_or_provider_secrets_and_upload_precedes_dispatch(self):
        self.assertNotIn('environment:', FRAGMENT)
        self.assertNotIn('secrets.', FRAGMENT)
        for token in ('contents: read', 'pull-requests: read', 'issues: read', 'checks: read',
                      'actions: write', 'cancel-in-progress: false'):
            self.assertIn(token, FRAGMENT)
        prepare = FRAGMENT.index('- name: Prepare main-check dispatch intents')
        upload = FRAGMENT.index('- name: Persist main-check dispatch intents')
        dispatch = FRAGMENT.index('- name: Dispatch confirmed main checks')
        results = FRAGMENT.index('- name: Persist main-check dispatch results')
        self.assertLess(prepare, upload)
        self.assertLess(upload, dispatch)
        self.assertLess(dispatch, results)
        self.assertIn('if-no-files-found: error', FRAGMENT[upload:dispatch])
        self.assertNotIn('if: always()', FRAGMENT[dispatch:results])
        self.assertIn('if: always()', FRAGMENT[results:])

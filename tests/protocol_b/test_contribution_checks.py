"""Offline checks of the exact-head contribution-checker dispatch; no API or candidate code runs."""
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import parse_qs, urlsplit

from test_gate import gate, FakeGH, HEAD, BASE, ROOT, changed

PACKAGE = 'example_20261127'
ENTRY = 'research/contributions/'+PACKAGE+'/check_all.py'
WORKFLOW_TEXT = (ROOT / '.github/workflows/contribution-checks.yml').read_text(encoding='utf-8')


def staging_program():
    """The staging program exactly as the workflow writes it to disk."""
    body = WORKFLOW_TEXT.split("<<'STAGE_PY'\n", 1)[1].split('\n          STAGE_PY\n', 1)[0]
    return '\n'.join(line[10:] if line.startswith(' ' * 10) else line for line in body.split('\n')) + '\n'


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), '-c', 'user.name=t', '-c', 'user.email=t@example.invalid',
                           '-c', 'core.autocrlf=false', *args], check=True, capture_output=True).stdout


class ChecksGH(FakeGH):
    def __init__(self):
        super().__init__()
        self.paths = ['research/contributions/'+PACKAGE+'/table.json', ENTRY]
        self.present = {ENTRY}
        self.workflow_text = WORKFLOW_TEXT
        self.refs, self.runs, self.dispatches, self.writes, self.deletions = {}, [], [], [], []
        self.finish = 'success'
        self.pr['changed_files'] = len(self.paths)

    def pages(self, path):
        if path.endswith('/files'):
            return [changed(p) for p in self.paths]
        return super().pages(path)

    def text(self, path, ref):
        if path == gate.CHECKS_WORKFLOW:
            if self.workflow_text is None:
                raise ValueError('File was not found at commit (HTTP 404)')
            return self.workflow_text
        return super().text(path, ref)

    def blob(self, path, ref):
        if path not in self.present:
            raise ValueError('File was not found at commit (HTTP 404)')
        return b'print("ok")\n'

    def run(self, ident, package, **extra):
        return {'id': ident, 'run_attempt': 1, 'event': 'workflow_dispatch', 'head_sha': HEAD,
                'head_branch': 'codex/protocol-b-checks/1/'+HEAD, 'path': gate.CHECKS_WORKFLOW,
                'display_title': gate.contribution_check_title(package),
                'repository': {'full_name': self.repo}, 'head_repository': {'full_name': self.repo},
                'status': 'completed', 'conclusion': 'success',
                'html_url': f'https://github.com/{self.repo}/actions/runs/{ident}', **extra}

    def call(self, path, method='GET', data=None):
        if path.startswith('/git/matching-refs/'):
            return list(self.refs.values())
        if path.startswith('/git/ref/'):
            ref = 'refs/' + path.removeprefix('/git/ref/')
            if ref not in self.refs:
                raise gate.RequestError({'status': 404})
            return copy.deepcopy(self.refs[ref])
        if path == '/git/refs' and method == 'POST':
            self.writes.append(data)
            self.refs[data['ref']] = {'ref': data['ref'], 'object': {'type': 'commit', 'sha': data['sha']}}
            return copy.deepcopy(self.refs[data['ref']])
        if path.startswith('/git/refs/') and method == 'DELETE':
            ref = 'refs/' + path.removeprefix('/git/refs/')
            self.deletions.append(ref)
            del self.refs[ref]
            return None
        if path.startswith('/actions/workflows/contribution-checks.yml/runs?'):
            query = parse_qs(urlsplit(path).query)
            rows = [r for r in self.runs if
                    ('head_sha' not in query or r['head_sha'] == query['head_sha'][0]) and
                    ('branch' not in query or r['head_branch'] == query['branch'][0])]
            # A queued run is finished the next time it is read.
            for run in self.runs:
                if run['status'] != 'completed' and self.finish:
                    run.update(status='completed', conclusion=self.finish)
            page = int(query.get('page', ['1'])[0])
            return {'total_count': len(rows), 'workflow_runs': copy.deepcopy(rows[(page-1)*100:page*100])}
        return super().call(path, method, data)

    def dispatch_workflow(self, name, ref, inputs=None):
        self.dispatches.append((name, ref, inputs))
        ident = 100 + len(self.dispatches)
        self.runs.append(self.run(ident, inputs['package'], head_branch=ref, status='queued', conclusion=None))
        return {'workflow_run_id': ident}


class ContributionChecks(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.patch = patch.object(gate, 'OUT', Path(self.tmp.name))
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.tmp.cleanup()

    def prepare(self, gh, event=None, mode='live'):
        event_path = Path(self.tmp.name)/'event.json'
        event_path.write_text(json.dumps(event or {'pull_request': {'number': 1}}))
        env = {'MODE': mode, 'TEST_PR': '1', 'GITHUB_EVENT_PATH': str(event_path),
               'GITHUB_REPOSITORY': 'x/y', 'GITHUB_REF': 'refs/heads/main', 'GH_TOKEN': 'fake'}
        with patch.dict(os.environ, env), patch.object(gate, 'GitHub', return_value=gh), \
             patch.object(gate.time, 'sleep'), patch.object(gate, 'outside_receipt') as receipt:
            gate.prepare_checks()
        self.receipt = receipt
        return json.loads((Path(self.tmp.name)/'contribution-checks.json').read_text())

    def test_gate_pin_matches_the_workflow(self):
        self.assertEqual(gate.CHECKS_WORKFLOW_SHA256, hashlib.sha256(WORKFLOW_TEXT.encode()).hexdigest())

    def test_workflow_has_no_secret_write_permission_or_repository_script(self):
        self.assertIn('permissions:\n  contents: read\n', WORKFLOW_TEXT)
        self.assertNotIn('secrets.', WORKFLOW_TEXT)
        self.assertNotIn('environment:', WORKFLOW_TEXT)
        self.assertNotIn('github.token', WORKFLOW_TEXT)
        self.assertIn('persist-credentials: false', WORKFLOW_TEXT)
        self.assertEqual(re.findall(r'uses: (\S+)', WORKFLOW_TEXT),
                         ['actions/checkout@11bd71901bbe5b1630ceea73d27597364c9af683'])
        for flag in ('--unshare-all', '--clearenv', '--cap-drop ALL', '--uid 65534', '--ro-bind "$root" /repo'):
            self.assertIn(flag, WORKFLOW_TEXT)
        # The only program taken from the commit under test is the package's own entry point.
        self.assertEqual(re.findall(r'python3 -B (\S+)', WORKFLOW_TEXT), ['check_all.py'])
        self.assertNotIn('scripts/', WORKFLOW_TEXT)
        # The pull-request trigger exists only to test the sandbox on a fixture.
        self.assertIn("paths:\n      - '.github/workflows/contribution-checks.yml'", WORKFLOW_TEXT)

    def test_staging_never_applies_the_commits_own_attributes(self):
        # Round 1, Astra C1 and Fable F1: export-subst and export-ignore in a package's
        # .gitattributes changed what git archive produced. The staging program must
        # write the committed blobs byte for byte whatever attributes the commit sets.
        self.assertNotIn('git archive', WORKFLOW_TEXT)
        self.assertNotIn('archive --format', WORKFLOW_TEXT)
        self.assertNotIn('tar -x', WORKFLOW_TEXT)
        self.assertIn('python3 -I -B "$RUNNER_TEMP/stage.py" "$source" "$root"', WORKFLOW_TEXT)
        if shutil.which('git') is None:
            self.skipTest('git is not available')
        work = Path(self.tmp.name)
        repo, staged, program = work/'repo', work/'staged', work/'stage.py'
        package = repo/'research/contributions/pkg'
        package.mkdir(parents=True)
        program.write_text(staging_program(), encoding='utf-8')
        compile(program.read_text(encoding='utf-8'), str(program), 'exec')
        committed = {
            'research/contributions/pkg/.gitattributes':
                b'check_all.py export-subst\ndata.txt export-subst ident text eol=crlf\nomitted.txt export-ignore\n',
            'research/contributions/pkg/check_all.py': b'assert "$Format:%H$" == "$" + "Format:%H$"\n',
            'research/contributions/pkg/data.txt': b'hash $Format:%H$ id $Id$\nsecond line\n',
            'research/contributions/pkg/omitted.txt': b'present\n',
            'research/contributions/pkg/sub/binary.bin': bytes(range(256)),
            'top.txt': b'top\n',
        }
        git(work, 'init', '-q', str(repo))
        for name, data in committed.items():
            (repo/name).parent.mkdir(parents=True, exist_ok=True)
            (repo/name).write_bytes(data)
        git(repo, 'add', '-A')
        git(repo, 'commit', '-q', '-m', 'fixture $Format:%H$')
        # Control: the archive route really does change these bytes, so the test bites.
        archive = git(repo, 'archive', '--format=tar', 'HEAD')
        self.assertNotIn(b'present' + bytes([10]), archive)
        self.assertNotIn(b'hash $Format:%H$', archive)
        staged.mkdir()
        result = subprocess.run([sys.executable, '-I', '-B', str(program), str(repo), str(staged)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Staged 6 files', result.stdout)
        found = {str(f.relative_to(staged)).replace(os.sep, '/'): f.read_bytes()
                 for f in staged.rglob('*') if f.is_file()}
        self.assertEqual(found, committed)
        self.assertFalse((staged/'.git').exists())
        # Staging into a folder that already holds a file of the same name fails, never overwrites.
        again = subprocess.run([sys.executable, '-I', '-B', str(program), str(repo), str(staged)],
                               capture_output=True, text=True)
        self.assertNotEqual(again.returncode, 0)

    def link_case(self, committed, sub='case'):
        if shutil.which('git') is None:
            self.skipTest('git is not available')
        work = Path(self.tmp.name)/sub
        work.mkdir()
        repo, staged, outside, program = work/'repo', work/'staged', work/'outside', work/'stage.py'
        (repo/committed).parent.mkdir(parents=True)
        (repo/committed).write_bytes(b'x')
        program.write_text(staging_program(), encoding='utf-8')
        git(work, 'init', '-q', str(repo))
        git(repo, 'add', '-A')
        git(repo, 'commit', '-q', '-m', 'fixture')
        staged.mkdir()
        outside.mkdir()
        return repo, staged, outside, program

    def stage(self, program, repo, staged):
        return subprocess.run([sys.executable, '-I', '-B', str(program), str(repo), str(staged)],
                              capture_output=True, text=True)

    def test_staging_refuses_to_write_through_a_symbolic_link(self):
        # Round 2 of the checker change, Fable N1: safety must not rest on the host refusing
        # malformed trees. Round 1 of the hardening change, Astra F1: nor may a folder be
        # created through the link before the path is refused.
        for index, committed in enumerate(('research/file.txt', 'research/newdir/file.txt',
                                           'research/a/b/c/file.txt')):
            with self.subTest(committed=committed):
                repo, staged, outside, program = self.link_case(committed, 'case%d' % index)
                try:
                    os.symlink(outside, staged/'research', target_is_directory=True)
                except (OSError, NotImplementedError):
                    self.skipTest('symbolic links are not available here')
                result = self.stage(program, repo, staged)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('passes through a symbolic link', result.stderr + result.stdout)
                self.assertEqual(list(outside.iterdir()), [])

    def test_staging_refuses_a_file_where_a_folder_is_needed(self):
        # Runs everywhere, links or not: the same walk that refuses a link refuses a file.
        repo, staged, outside, program = self.link_case('research/newdir/file.txt')
        (staged/'research').write_bytes(b'')
        result = self.stage(program, repo, staged)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('passes through a symbolic link or a file', result.stderr + result.stdout)
        self.assertEqual(list(staged.iterdir()), [staged/'research'])

    def test_staging_creates_nested_folders_under_the_root_only(self):
        repo, staged, outside, program = self.link_case('research/a/b/file.txt')
        result = self.stage(program, repo, staged)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((staged/'research/a/b/file.txt').read_bytes(), b'x')
        self.assertEqual(list(outside.iterdir()), [])

    def test_self_test_fixture_sets_the_attribute_traps(self):
        for needle in ('check_all.py export-subst', 'data.txt export-subst ident text eol=crlf',
                       'omitted.txt export-ignore', "'export-subst rewrote the checker'",
                       "'export-ignore dropped a file'", "'data rewritten'"):
            self.assertIn(needle, WORKFLOW_TEXT)

    def test_fork_head_gets_one_dispatch_on_a_reserved_ref_and_waits(self):
        gh = ChecksGH()
        gh.pr['head']['repo'] = {'full_name': 'fork/project'}
        state = self.prepare(gh)
        ref = 'codex/protocol-b-checks/1/'+HEAD
        self.assertEqual(gh.writes, [{'ref': 'refs/heads/'+ref, 'sha': HEAD}])
        self.assertEqual(gh.dispatches, [('contribution-checks.yml', ref, {'package': PACKAGE})])
        self.assertEqual(state['packages'], [PACKAGE])
        self.assertEqual(state['runs'][PACKAGE]['conclusion'], 'success')
        self.assertNotIn('error', state)
        # The run is the kind of evidence read_ci_job accepts.
        run = gh.runs[0]
        self.assertEqual((run['event'], run['head_sha'], run['repository']['full_name']),
                         ('workflow_dispatch', HEAD, gh.repo))

    def test_existing_run_is_not_dispatched_again(self):
        gh = ChecksGH()
        gh.runs.append(gh.run(7, PACKAGE))
        state = self.prepare(gh)
        self.assertEqual((gh.dispatches, gh.writes), ([], []))
        self.assertEqual(state['runs'][PACKAGE]['id'], 7)
        state = self.prepare(gh)
        self.assertEqual(gh.dispatches, [])

    def test_failed_checker_is_recorded_and_never_raises(self):
        gh = ChecksGH()
        gh.finish = 'failure'
        state = self.prepare(gh)
        self.assertEqual(state['runs'][PACKAGE]['conclusion'], 'failure')
        self.assertNotIn('error', state)

    def test_unfinished_run_times_out_without_blocking(self):
        gh = ChecksGH()
        gh.finish = None
        clock = iter(range(0, 10**9, 3600))
        with patch.object(gate.time, 'monotonic', lambda: next(clock)):
            state = self.prepare(gh)
        self.assertIn('did not finish within 80 minutes', state['error'])
        self.assertEqual(len(gh.dispatches), 1)

    def test_unapproved_or_missing_workflow_at_head_runs_nothing(self):
        for text in (WORKFLOW_TEXT.replace('--unshare-all', ''), WORKFLOW_TEXT+'\n', None):
            with self.subTest(text=(text or '')[-20:]):
                gh = ChecksGH()
                gh.workflow_text = text
                state = self.prepare(gh)
                self.assertTrue(state['error'])
                self.assertEqual((gh.dispatches, gh.writes), ([], []))

    def test_only_touched_packages_with_a_checker_are_run(self):
        gh = ChecksGH()
        gh.paths = ['research/contributions/no_checker/notes.md', 'research/quartic214/x.md', 'README.md']
        gh.pr['changed_files'] = 3
        state = self.prepare(gh)
        self.assertEqual((state['packages'], gh.dispatches, gh.writes), ([], [], []))
        gh = ChecksGH()
        gh.paths = ['research/contributions/'+name+'/data.json' for name in ('b', 'a', 'none')]
        gh.present = {'research/contributions/a/check_all.py', 'research/contributions/b/check_all.py'}
        gh.pr['changed_files'] = 3
        state = self.prepare(gh)
        self.assertEqual(state['packages'], ['a', 'b'])
        self.assertEqual([d[2]['package'] for d in gh.dispatches], ['a', 'b'])
        self.assertEqual(len(gh.writes), 1)

    def test_package_names_cannot_escape_or_inject(self):
        gh = ChecksGH()
        for path in ('research/contributions/../scripts/check_all.py', 'research/contributions/a b/x',
                     'research/contributions/$(id)/x', 'research/contributions/-rf/x',
                     'research/contributions/'+'a'*101+'/x', 'research/contributions/check_all.py',
                     'Research/contributions/a/x'):
            gh.paths = [path]
            self.assertEqual(gate.contribution_packages(gh, gh.pr, gh.pages('/pulls/1/files')), [], path)

    def test_renamed_file_counts_for_both_packages(self):
        gh = ChecksGH()
        gh.present = {'research/contributions/old/check_all.py', 'research/contributions/new/check_all.py'}
        files = [changed('research/contributions/new/t.json', previous_filename='research/contributions/old/t.json')]
        self.assertEqual(gate.contribution_packages(gh, gh.pr, files), ['new', 'old'])

    def test_more_packages_than_the_limit_runs_none(self):
        gh = ChecksGH()
        names = ['p'+str(i) for i in range(gate.CHECKS_LIMIT+1)]
        gh.paths = ['research/contributions/'+n+'/check_all.py' for n in names]
        gh.present = set(gh.paths)
        gh.pr['changed_files'] = len(names)
        state = self.prepare(gh)
        self.assertIn('none was run', state['error'])
        self.assertEqual((gh.dispatches, gh.writes), ([], []))

    def test_moved_reserved_ref_is_never_used(self):
        gh = ChecksGH()
        ref = gate.CHECKS_REF_PREFIX+'1/'+HEAD
        gh.refs[ref] = {'ref': ref, 'object': {'sha': BASE}}
        state = self.prepare(gh)
        self.assertIn('unexpected contents', state['error'])
        self.assertEqual((gh.dispatches, gh.writes), ([], []))

    def test_changed_pull_request_creates_nothing(self):
        gh = ChecksGH()
        gh.race = True
        state = self.prepare(gh)
        self.assertIn('PR changed', state['error'])
        self.assertEqual((gh.dispatches, gh.writes), ([], []))

    def test_draft_closed_and_decision_comments_run_nothing(self):
        for change in ({'draft': True}, {'state': 'closed'}):
            gh = ChecksGH()
            gh.pr.update(change)
            self.assertEqual(self.prepare(gh)['packages'], [])
            self.assertEqual(gh.dispatches, [])
        for body in ('/protocol-b override '+HEAD+' scope-1-1-astra reason', '/protocol-b merge '+HEAD, 'hello'):
            gh = ChecksGH()
            gh.permission = 'admin'
            user = {'login': 'collaborator', 'type': 'User'}
            event = {'issue': {'number': 1}, 'comment': {'body': body, 'user': user}, 'sender': {'login': 'collaborator'}}
            self.assertEqual(self.prepare(gh, event)['packages'], [])
            self.assertEqual(gh.dispatches, [])

    def test_review_command_needs_a_collaborator(self):
        user = {'login': 'collaborator', 'type': 'User'}
        event = {'issue': {'number': 1}, 'comment': {'body': '/protocol-b review', 'user': user},
                 'sender': {'login': 'collaborator'}}
        gh = ChecksGH()
        gh.permission = 'read'
        self.assertEqual(self.prepare(gh, event)['packages'], [])
        gh = ChecksGH()
        gh.permission = 'write'
        self.assertEqual(self.prepare(gh, event)['packages'], [PACKAGE])
        self.receipt.assert_not_called()

    def test_outside_author_needs_this_runs_admission_receipt(self):
        gh = ChecksGH()
        gh.author_permission = 'read'
        self.prepare(gh)
        self.receipt.assert_called_once()
        gh = ChecksGH()
        self.prepare(gh)
        self.receipt.assert_not_called()

    def test_off_mode_and_other_test_pull_requests_do_nothing(self):
        gh = ChecksGH()
        self.assertEqual(self.prepare(gh, mode='off')['packages'], [])
        gh.pr['number'] = 2
        self.assertEqual(self.prepare(gh, {'pull_request': {'number': 2}}, mode='test')['packages'], [])
        self.assertEqual(gh.dispatches, [])

    def test_run_identity_excludes_pull_request_fork_and_other_workflow_runs(self):
        gh = ChecksGH()
        good = gh.run(1, PACKAGE)
        self.assertTrue(gate.direct_check_run(gh, HEAD, good))
        for change in ({'event': 'pull_request'}, {'event': 'push'}, {'head_sha': BASE},
                       {'path': gate.LEAN_WORKFLOW}, {'head_repository': {'full_name': 'fork/project'}},
                       {'repository': {'full_name': 'fork/project'}}):
            self.assertFalse(gate.direct_check_run(gh, HEAD, {**good, **change}), change)

    def test_cleanup_deletes_only_unmoved_refs_of_closed_pull_requests_with_finished_runs(self):
        gh = ChecksGH()
        ref = gate.CHECKS_REF_PREFIX+'1/'+HEAD
        gh.refs[ref] = {'ref': ref, 'object': {'sha': HEAD}}
        other = 'refs/heads/codex/protocol-b-checks/unrelated'
        gh.refs[other] = {'ref': other, 'object': {'sha': HEAD}}
        self.assertEqual(gate.cleanup_check_refs(gh), [])
        gh.pr['state'] = 'closed'
        gh.runs.append(gh.run(5, PACKAGE, status='in_progress', conclusion=None))
        gh.finish = None
        self.assertEqual(gate.cleanup_check_refs(gh)[0]['retained'], 'A run is active')
        gh.runs[0].update(status='completed', conclusion='failure')
        self.assertTrue(gate.cleanup_check_refs(gh)[0]['deleted'])
        self.assertEqual(gh.deletions, [ref])
        self.assertIn(other, gh.refs)

    def test_cleanup_never_deletes_a_moved_ref(self):
        gh = ChecksGH()
        ref = gate.CHECKS_REF_PREFIX+'1/'+HEAD
        gh.refs[ref] = {'ref': ref, 'object': {'sha': BASE}}
        gh.pr['state'] = 'closed'
        self.assertEqual(gate.cleanup_check_refs(gh), [])
        self.assertEqual(gh.deletions, [])

    def test_gate_job_runs_the_step_without_review_secrets(self):
        text = (ROOT / '.github/workflows/protocol-b.yml').read_text(encoding='utf-8')
        job = text.split('\n  kernel_preflight:\n', 1)[1].split('\n  run_reviewers:\n', 1)[0]
        self.assertIn('protocol-b.py" prepare-checks', job)
        self.assertNotIn('secrets.', job)
        self.assertNotIn('environment:', job)


if __name__ == '__main__':
    unittest.main()

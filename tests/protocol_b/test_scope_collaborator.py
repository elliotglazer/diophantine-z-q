"""A collaborator other than the author may accept itemized incomplete coverage, and nothing else."""
import copy
import unittest
from unittest.mock import patch

from test_gate import (gate, FakeGH, FakeApp, HEAD, BASE, APP_ID, changed, envelope, report, comment,
                       report_comment, run_pipeline)

NOTE = 'research/contributions/example/README.md'
UNREAD = ['The application of Theorem 3 on p. 14 was not reviewed.']


class ResearchGH(FakeGH):
    paths = (NOTE,)
    committers = (('author', 'web-flow'),)
    listed = None  # What the mutable pull-request file listing shows, if different.

    def pages(self, path):
        if path.endswith('/files'):
            return [changed(p) for p in (self.listed or self.paths)]
        return super().pages(path)

    stale_paths = None  # The diff from the pull request's recorded, possibly old, base.
    behind, merge_base = 0, None
    branch_tip = None    # What the qualified branch ref returns; defaults to main_sha.
    later_paths = None   # The diff from a default-branch tip the branch ref did not show.

    def __init__(self):
        super().__init__()
        # Every other required check has passed on the head.
        self.check_runs = [{'id': i, 'name': name, 'head_sha': HEAD, 'status': 'completed',
                            'conclusion': 'success', 'app': {'id': 15368}}
                           for i, name in enumerate(sorted(self.required - {gate.CHECK}), 1)]

    def call(self, path, method='GET', data=None):
        if path == '/git/ref/heads/main':
            return {'ref': 'refs/heads/main', 'object': {'type': 'commit', 'sha': self.branch_tip or self.main_sha}}
        if path.startswith('/compare/') and path.endswith('...'+HEAD):
            self.compare_requests.append(path)
            base = path.removeprefix('/compare/').split('...')[0]
            commits = [{'author': {'login': a} if a else None, 'committer': {'login': c} if c else None}
                       for a, c in self.committers]
            # Only a comparison from the default branch's tip shows the true change.
            tip = self.branch_tip or self.main_sha
            paths = (self.paths if base == tip else
                     self.later_paths if self.later_paths and base == self.main_sha else
                     (self.stale_paths or self.paths))
            return {'behind_by': self.behind, 'merge_base_commit': {'sha': self.merge_base or base},
                    'total_commits': len(commits), 'commits': commits, 'files': [changed(p) for p in paths]}
        return super().call(path, method, data)

    def text(self, path, ref):
        if path in self.paths:
            return 'alpha  ' if ref == BASE else 'alpha'
        return super().text(path, ref)


ORIGINAL_CALL = ResearchGH.call

def scope_pair(**review):
    review = {'decision': 'changes_requested', 'scope_complete': False, 'not_reviewed': UNREAD, **review}
    return {'astra': envelope(review=report(**review)), 'fable': envelope('fable')}


def failure_envelope(family='astra'):
    """The record main() writes when a reviewer raised before delivering any report."""
    return envelope(family, complete=False, identity_error=None,
                    review={'decision': 'changes_requested',
                            'report': 'Infrastructure failure, not a model verdict: HTTP 529',
                            'scope_complete': False, 'not_reviewed': ['Review interrupted: HTTP 529'],
                            'findings': [], 'prior_findings': []})


class CollaboratorScopeDecisions(unittest.TestCase):
    def case(self, permission='write', ids='scope-1-1-astra', pair=None, paths=(NOTE,), login='collaborator',
             comments=None):
        gh, app = ResearchGH(), FakeApp()
        gh.paths, gh.permission = tuple(paths), permission
        gh.pr['changed_files'] = len(gh.paths)
        pair = pair or scope_pair()
        app.prior(pair)
        command = comment('/protocol-b override '+HEAD+' '+ids+' Coverage limit accepted for a research note', login)
        gh.comments = [report_comment(e) for e in (comments or pair).values()]+[command]
        event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': login}}
        known = {ident: {'objection': 'App-recorded item'} for ident in gate.override_findings(pair, HEAD)}
        return gh, app, event, known, gate.collaborator_scope_ids(pair)

    def decide(self, gh, app, event):
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            return run_pipeline(gh, app, event=event,
                                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review')))

    def test_non_author_collaborator_accepts_itemized_scope(self):
        for permission in ('write', 'maintain'):
            with self.subTest(permission=permission):
                gh, app, event, known, eligible = self.case(permission)
                self.assertEqual(eligible, {'scope-1-1-astra'})
                overrides = gate.history(gh, gh.pr, known, eligible)[2]
                self.assertEqual(overrides['scope-1-1-astra']['authority'], 'scope-collaborator')
                self.assertEqual(overrides['scope-1-1-astra']['collaborator'], 'collaborator')
                self.assertEqual(overrides['scope-1-1-astra']['default_tip'], BASE)
                gh, app, errors, state = self.decide(gh, app, event)
                self.assertEqual(errors, [])
                self.assertEqual(app.final['conclusion'], 'success')
                self.assertFalse(state['reports']['astra']['review']['scope_complete'])
                self.assertEqual(state['scope_overrides'][0]['id'], 'scope-1-1-astra')
                self.assertIn('Accepted by a collaborator who is not the author with incomplete reviewer scope',
                              state['summary'])
                self.assertNotIn('Accepted by admin', state['summary'])
                # The durable round summary posted on the pull request names the same authority.
                posted = [p['body'] for p in gh.posts if p['body'].startswith(gate.SUMMARY_MARKER)]
                self.assertTrue(posted)
                self.assertIn('A collaborator who is not the author (collaborator) accepted incomplete review scope',
                              posted[-1])
                self.assertNotIn('Admin accepted', posted[-1])

    def test_admin_record_is_unchanged(self):
        gh, app, event, known, eligible = self.case('admin')
        self.assertNotIn('authority', gate.history(gh, gh.pr, known, eligible)[2]['scope-1-1-astra'])
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertEqual(errors, [])
        self.assertIn('Accepted by admin with incomplete reviewer scope', state['summary'])
        self.assertNotIn('collaborator who is not the author', state['summary'])
        posted = [p['body'] for p in gh.posts if p['body'].startswith(gate.SUMMARY_MARKER)]
        self.assertIn('Admin accepted incomplete review scope', posted[-1])

    def test_without_app_eligibility_a_comment_decides_nothing(self):
        gh, app, event, known, eligible = self.case()
        self.assertFalse(gate.history(gh, gh.pr, known)[2])
        self.assertFalse(gate.history(gh, gh.pr, known, set())[2])
        self.assertFalse(gate.history(gh, gh.pr, None, eligible)[2])

    def refused(self, **kwargs):
        gh, app, event, known, eligible = self.case(**kwargs)
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertEqual(errors, [])
        self.assertIsNone(state)
        self.assertEqual(app.created, [])
        return gh

    def test_author_cannot_decide_own_pull_request(self):
        for login in ('author', 'Author'):
            gh = self.refused(login=login)
            self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))

    def test_reader_has_no_effect(self):
        self.refused(permission='read')

    def test_only_contribution_notes_are_open(self):
        for path in ('p.tex', 'README.md', '.github/workflows/protocol-b.yml', 'scripts/check.py',
                     'tests/protocol_b/test_gate.py', 'docs/maintenance.md', 'manuscripts/v22.tex',
                     'releases/v22.json', 'research/version22/table.json',
                     'research/quartic214/construction/build.py', 'research/notes/x.md',
                     'lean/ZInQ/Basic.lean', 'ThirdParty/GreenTao/A.lean',
                     'research/contributions/x/Proof.lean', 'research/contributions/x/PROOF.LEAN',
                     'research/contributions/x/lakefile.toml', 'research/contributions/x/lean-toolchain',
                     'Research/contributions/x/a.md', 'research/Contributions/x/a.md',
                     'research/contributions/../../scripts/a.py', 'research/contributions//a.md'):
            with self.subTest(path=path):
                self.assertTrue(gate.scope_decision_protected(path))
                gh = self.refused(paths=(NOTE, path))
                self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))
        for path in (NOTE, 'research/contributions/x/check_all.py', 'research/contributions/x/source/audit_v78/t.json',
                     'research/contributions/x/review.md'):
            self.assertFalse(gate.scope_decision_protected(path))

    def test_renamed_from_a_protected_path_needs_an_admin(self):
        gh, app, event, known, eligible = self.case()
        good = gh.call(f'/compare/{BASE}...{HEAD}')
        renamed = {**good, 'files': [changed(NOTE, previous_filename='docs/x.md')]}
        with patch.object(ResearchGH, 'call', lambda self, path, method='GET', data=None:
                          renamed if path.startswith('/compare/') else ORIGINAL_CALL(self, path, method, data)):
            self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])

    def test_incomplete_or_ambiguous_comparison_needs_an_admin(self):
        user = {'login': 'collaborator', 'type': 'User'}
        gh, app, event, known, eligible = self.case()
        self.assertTrue(gate.scope_decider(gh, gh.pr, user))
        gh, *_ = self.case(paths=(NOTE, NOTE))
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        gh, *_ = self.case()
        gh.pr['changed_files'] = 2
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        gh, *_ = self.case(paths=tuple('research/contributions/x/f%d.json' % i for i in range(300)))
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        gh, *_ = self.case()
        gh.committers = (('author', 'web-flow'),) * 250
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        for broken in ({'files': None}, {'files': []}, {'commits': []}, {'total_commits': 2},
                       {'merge_base_commit': None}):
            gh, *_ = self.case()
            good = gh.call(f'/compare/{BASE}...{HEAD}')
            with patch.object(ResearchGH, 'call', lambda self, path, method='GET', data=None, good=good, broken=broken:
                              {**good, **broken} if path.startswith('/compare/') else ORIGINAL_CALL(self, path, method, data)):
                self.assertFalse(gate.scope_decider(gh, gh.pr, user), broken)
        gh, *_ = self.case()
        self.assertFalse(gate.scope_decider(gh, {**gh.pr, 'head': {'sha': 'not-a-sha'}}, user))

    def test_paths_come_from_the_reviewed_commits_not_the_mutable_listing(self):
        # Round 2, Astra F1: the pull request shows a contribution-only head with the same
        # file count while its file listing is read, then returns to the protected head.
        gh, app, event, known, eligible = self.case(paths=('scripts/check.py',))
        gh.listed = (NOTE,)
        self.assertFalse(gate.scope_decider(gh, gh.pr, {'login': 'collaborator', 'type': 'User'}))
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertIsNone(state)
        self.assertEqual(app.created, [])

    def test_true_change_is_measured_from_the_default_branch_tip(self):
        # Round 3, Fable F1: the recorded base is old; the head contains the newer default
        # branch but restores a protected file, so only the diff from the tip shows it.
        user = {'login': 'collaborator', 'type': 'User'}
        gh, app, event, known, eligible = self.case(paths=(NOTE, '.github/workflows/protocol-b.yml'))
        gh.main_sha = 'd' * 40
        gh.stale_paths = (NOTE,)
        self.assertEqual(gh.pr['base']['sha'], BASE)
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])
        self.assertTrue(any(('d' * 40) in request for request in gh.compare_requests))
        # The converse: an honest branch that merged a newer default branch is not
        # charged with the default branch's own files.
        gh, app, event, known, eligible = self.case()
        gh.main_sha = 'd' * 40
        gh.stale_paths = (NOTE, 'scripts/changed_on_main.py')
        self.assertTrue(gate.scope_decider(gh, gh.pr, user))

    def test_default_branch_moving_after_the_decision_voids_it(self):
        # Round 4, Astra F1: both eligibility reads see tip B0; every later read sees B1,
        # already an ancestor of the head, against which the head restores a protected file.
        gh, app, event, known, eligible = self.case()
        gh.branch_tip = BASE
        overrides = gate.history(gh, gh.pr, known, eligible)[2]
        self.assertEqual(overrides['scope-1-1-astra']['default_tip'], BASE)
        gh.main_sha = 'd' * 40
        gh.later_paths = (NOTE, 'quartics/protected.json')
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertNotEqual((app.final or {}).get('conclusion'), 'success')
        self.assertEqual(gh.merge_requests, [])
        self.assertIn('default branch moved', str(app.final)+str(errors))

    def test_decision_waits_for_the_other_required_checks(self):
        # Round 5, Astra's unread item: a decision must not sit behind deferred auto-merge.
        for change in ({'status': 'in_progress', 'conclusion': None}, {'conclusion': 'failure'}):
            gh, app, event, known, eligible = self.case()
            gh.check_runs[0].update(change)
            self.assertFalse(gate.other_required_checks_passed(gh, HEAD, 'main'))
            gh, app, errors, state = self.decide(gh, app, event)
            self.assertNotEqual((app.final or {}).get('conclusion'), 'success')
            self.assertEqual(gh.merge_requests, [])
            self.assertTrue(any('every other required check has already passed' in p['body'] for p in gh.posts))
            self.assertFalse(any(p['body'].startswith('Accepted by collaborator override') for p in gh.posts))
        gh, app, event, known, eligible = self.case()
        gh.check_runs = []
        self.assertFalse(gate.other_required_checks_passed(gh, HEAD, 'main'))
        # An admin's decision is not subject to this condition.
        gh, app, event, known, eligible = self.case('admin')
        gh.check_runs[0].update(status='in_progress', conclusion=None)
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertEqual(app.final['conclusion'], 'success')

    def test_collaborator_decision_is_never_left_to_deferred_auto_merge(self):
        state = {'overrides': {'scope-1-1-astra': {'collaborator': 'jo', 'authority': 'scope-collaborator',
                                                   'default_tip': BASE}}}
        self.assertTrue(gate.collaborator_decided(state))
        self.assertFalse(gate.collaborator_decided({'overrides': {'x': {'collaborator': 'owner'}}}))
        self.assertFalse(gate.collaborator_decided({}))
        gh = ResearchGH()
        with patch.object(gate, 'merge_readiness', return_value=(False, {'auto_merge': None, 'node_id': 'PR_1'}, BASE)), \
             patch.object(gate, 'direct_merge', side_effect=AssertionError('no merge')), \
             patch.object(gh, 'api', side_effect=AssertionError('auto-merge must not be enabled')):
            with self.assertRaisesRegex(RuntimeError, 'not left to deferred auto-merge'):
                gate.merge_and_dispatch(gh, state)

    def test_acceptance_comment_is_not_posted_when_the_tip_has_moved(self):
        # Round 5, Fable N1: the tip is checked before the acceptance comment is posted.
        gh, app, event, known, eligible = self.case()
        reads = iter([BASE, BASE])
        original = gate.default_branch_tip
        with patch.object(gate, 'default_branch_tip', lambda g, default: next(reads, 'd' * 40)):
            gh, app, errors, state = self.decide(gh, app, event)
        self.assertNotEqual((app.final or {}).get('conclusion'), 'success')
        self.assertFalse(any(p['body'].startswith('Accepted by collaborator override') for p in gh.posts))
        self.assertTrue(any('default branch moved' in p['body'] for p in gh.posts))

    def test_stored_tip_is_checked_at_every_later_step(self):
        state = {'overrides': {'scope-1-1-astra': {'collaborator': 'jo', 'authority': 'scope-collaborator',
                                                   'default_tip': BASE}}}
        self.assertTrue(gate.scope_decision_tip_current(state, BASE))
        self.assertFalse(gate.scope_decision_tip_current(state, 'd' * 40))
        del state['overrides']['scope-1-1-astra']['default_tip']
        self.assertFalse(gate.scope_decision_tip_current(state, BASE))
        # Admin decisions and runs without overrides are not bound to a tip.
        self.assertTrue(gate.scope_decision_tip_current({'overrides': {'x': {'collaborator': 'owner'}}}, 'd' * 40))
        self.assertTrue(gate.scope_decision_tip_current({}, 'd' * 40))
        text = (gate.ROOT if hasattr(gate, 'ROOT') else __import__('test_gate').ROOT).joinpath(
            '.github/workflows/protocol-b.yml').read_text(encoding='utf-8')
        self.assertEqual(text.count('if not scope_decision_tip_current(state, latest_ref)'), 3)

    def test_tip_is_read_from_the_qualified_branch_ref(self):
        gh, *_ = self.case()
        self.assertEqual(gate.default_branch_tip(gh, 'main'), BASE)
        for bad in ({'ref': 'refs/tags/main', 'object': {'sha': BASE}}, {'ref': 'refs/heads/main', 'object': {}},
                    {'ref': 'refs/heads/main', 'object': {'sha': 'short'}}):
            with patch.object(ResearchGH, 'call', lambda self, path, method='GET', data=None, bad=bad: bad):
                with self.assertRaises(ValueError):
                    gate.default_branch_tip(gh, 'main')

    def test_branch_behind_or_not_based_on_the_default_tip_needs_an_admin(self):
        user = {'login': 'collaborator', 'type': 'User'}
        gh, *_ = self.case()
        gh.behind = 1
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        gh, *_ = self.case()
        gh.merge_base = 'e' * 40
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        gh, *_ = self.case()
        gh.pr['base']['ref'] = 'release'
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))

    def test_command_for_another_head_is_refused_before_any_check(self):
        gh, app, event, known, eligible = self.case()
        event['comment']['body'] = event['comment']['body'].replace(HEAD, BASE)
        gh.comments[-1] = event['comment']
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertIsNone(state)
        self.assertEqual(app.created, [])
        self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))

    def test_someone_who_committed_to_the_branch_cannot_decide(self):
        user = {'login': 'collaborator', 'type': 'User'}
        for committers in ((('author', 'web-flow'), ('Collaborator', 'web-flow')),
                           (('author', 'collaborator'),)):
            gh, app, event, known, eligible = self.case()
            gh.committers = committers
            self.assertFalse(gate.scope_decider(gh, gh.pr, user))
            self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])
        gh, *_ = self.case()
        gh.committers = ((None, None), ('author', 'web-flow'))
        self.assertTrue(gate.scope_decider(gh, gh.pr, user))

    def test_uncovered_discussion_is_not_set_aside_by_a_collaborator(self):
        # Round 2, Fable F1, case 1: a person objects after the reviews; no review covered it.
        gh, app, event, known, eligible = self.case()
        objection = comment('The table in section 3 contradicts Version 21.', 'reader')
        objection['id'] = 77
        gh.comments.insert(-1, objection)
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertNotEqual((app.final or {}).get('conclusion'), 'success')
        self.assertEqual(gh.merge_requests, [])
        self.assertTrue(any(p['body'].startswith('This scope decision was not applied.') for p in gh.posts))
        # The gate's own reply is not itself new discussion.
        reply = {'id': 78, 'author': 'github-actions[bot]', 'body': 'This scope decision was not applied. x'}
        self.assertEqual(gate.history_coverage([reply]), set())

    def test_admin_can_still_decide_with_uncovered_discussion(self):
        gh, app, event, known, eligible = self.case('admin')
        objection = comment('The table in section 3 contradicts Version 21.', 'reader')
        objection['id'] = 77
        gh.comments.insert(-1, objection)
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertEqual(app.final['conclusion'], 'success')

    def test_report_without_the_history_read_is_not_eligible(self):
        # Round 2, Fable F1, case 2.
        pair = scope_pair()
        pair['astra']['read_prerequisites_complete'] = False
        self.assertEqual(gate.collaborator_scope_ids(pair), set())

    def test_a_finding_is_never_a_collaborator_decision(self):
        pair = scope_pair(findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'A counterexample'}])
        gh = self.refused(ids='scope-1-1-astra,1-1-astra-F1', pair=pair)
        self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))

    def test_scope_alone_does_not_cover_a_finding(self):
        pair = scope_pair(findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'A counterexample'}])
        gh, app, event, known, eligible = self.case(pair=pair)
        self.assertEqual(set(gate.history(gh, gh.pr, known, eligible)[2]), {'scope-1-1-astra'})
        _, app, errors, state = self.decide(gh, app, event)
        self.assertIn('Uncovered findings: 1-1-astra-F1', str(app.final))
        self.assertNotEqual((app.final or {}).get('conclusion'), 'success')

    def not_eligible(self, pair, comments=None):
        self.assertIsNotNone(gate.review_scope_item(pair['astra']))
        gh, app, event, known, eligible = self.case(pair=pair, comments=comments)
        self.assertEqual(eligible, set())
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertNotEqual((app.final or {}).get('conclusion'), 'success')
        self.assertTrue(any('holds no completed reviewer report itemizing' in p['body'] for p in gh.posts))
        self.assertEqual(gh.merge_requests, [])

    def test_interrupted_review_record_is_not_a_reviewer_list(self):
        # Finding F1/F2 of the first review: main() writes a non-empty not_reviewed for a crash.
        self.not_eligible({'astra': failure_envelope(), 'fable': envelope('fable')})

    def test_both_reviewers_failing_cannot_be_accepted_by_a_collaborator(self):
        pair = {'astra': failure_envelope(), 'fable': failure_envelope('fable')}
        gh, app, event, known, eligible = self.case(pair=pair, ids='scope-1-1-astra,scope-1-1-fable')
        self.assertEqual(eligible, set())
        gh, app, errors, state = self.decide(gh, app, event)
        self.assertNotEqual((app.final or {}).get('conclusion'), 'success')
        self.assertEqual(gh.merge_requests, [])

    def test_other_unitemized_records_need_an_admin(self):
        self.not_eligible(scope_pair(scope_complete=True, not_reviewed=[]))
        pair = scope_pair()
        pair['astra']['post_review_error'] = 'Source record missing'
        self.not_eligible(pair)
        pair = scope_pair()
        pair['astra']['identity_error'] = 'Wrong model answered'
        self.assertEqual(gate.collaborator_scope_ids(pair), set())
        pair = scope_pair()
        pair['astra']['model'] = 'different-model'
        self.assertEqual(gate.collaborator_scope_ids(pair), set())
        pair = scope_pair(not_reviewed=['Unread argument '+str(i)+' '+('x'*1200) for i in range(100)])
        self.assertEqual(gate.collaborator_scope_ids(pair), set())
        pair = scope_pair(not_reviewed=['  '])
        self.assertEqual(gate.collaborator_scope_ids(pair), set())

    def test_forged_report_comment_cannot_make_an_app_record_eligible(self):
        # The App record rejected without findings and lists nothing; a bot-authored
        # comment with the same run, attempt and reviewer claims an itemized list.
        genuine = scope_pair(scope_complete=True, not_reviewed=[])
        forged = copy.deepcopy(genuine)
        forged['astra']['review'].update(scope_complete=False, not_reviewed=UNREAD)
        self.assertEqual(gate.review_scope_item(genuine['astra'])['id'], gate.review_scope_item(forged['astra'])['id'])
        self.not_eligible(genuine, comments=forged)
        # Likewise when the App record carries a metadata error the comment omits.
        genuine = scope_pair()
        genuine['astra']['post_review_error'] = 'Source record missing'
        self.not_eligible(genuine, comments=scope_pair())

    def test_a_collaborator_never_replaces_an_admin_decision(self):
        gh, app, event, known, eligible = self.case()
        admin = comment('/protocol-b override '+HEAD+' scope-1-1-astra Owner decision', 'owner')
        admin['id'] = 2
        gh.comments.insert(-1, admin)
        original = gate.administrator
        with patch.object(gate, 'administrator', lambda g, user: user['login'] == 'owner' or original(g, user)):
            overrides = gate.history(gh, gh.pr, known, eligible)[2]
        self.assertEqual(overrides['scope-1-1-astra']['collaborator'], 'owner')
        self.assertNotIn('authority', overrides['scope-1-1-astra'])

    def test_scope_shaped_name_without_app_record_is_not_a_decision(self):
        gh, app, event, _, eligible = self.case()
        self.assertFalse(gate.history(gh, gh.pr, None, eligible)[2])

    def test_edited_comment_and_revoked_access_do_not_decide(self):
        gh, app, event, known, eligible = self.case()
        self.assertTrue(gate.history(gh, gh.pr, known, eligible)[2])
        gh.comments[-1]['updated_at'] = 'later'
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])
        gh, app, event, known, eligible = self.case()
        gh.permission = 'read'
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])

    def test_other_head_is_not_a_decision(self):
        gh, app, event, known, eligible = self.case()
        gh.comments[-1]['body'] = gh.comments[-1]['body'].replace(HEAD, BASE)
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])

    def test_round_summary_names_each_authority(self):
        pair = {'astra': envelope(review=report(decision='changes_requested', scope_complete=False, not_reviewed=UNREAD)),
                'fable': envelope('fable', review=report(decision='changes_requested', scope_complete=False,
                                                         not_reviewed=UNREAD))}
        state = {'head': HEAD, 'check': 1, 'conclusion': 'success', 'reports': pair, 'overrides': {
            'scope-1-1-astra': {'collaborator': 'owner', 'reason': 'r', 'url': 'u'},
            'scope-1-1-fable': {'collaborator': 'jo', 'reason': 'r', 'url': 'u', 'authority': 'scope-collaborator'}}}
        text = gate.round_summary_body(state, 'x/y', 'https://example.invalid/check')
        self.assertIn('Admin accepted incomplete review scope', text)
        self.assertIn('A collaborator who is not the author (jo) accepted incomplete review scope', text)

    def test_summary_tells_collaborators_what_they_may_decide(self):
        text = gate.round_summary_body({'head': HEAD, 'check': 1, 'conclusion': 'failure',
                                        'reports': scope_pair()}, 'x/y', 'https://example.invalid/check')
        self.assertIn('a collaborator other than the author may accept these items', text)
        self.assertIn('findings always need an admin', text)


if __name__ == '__main__':
    unittest.main()

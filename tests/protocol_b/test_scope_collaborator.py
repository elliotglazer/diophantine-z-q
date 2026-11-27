"""A collaborator other than the author may accept itemized incomplete coverage, and nothing else."""
import copy
import unittest
from unittest.mock import patch

from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, changed, envelope, report, comment, report_comment, run_pipeline

NOTE = 'research/contributions/example/README.md'
UNREAD = ['The application of Theorem 3 on p. 14 was not reviewed.']


class ResearchGH(FakeGH):
    paths = (NOTE,)

    def pages(self, path):
        if path.endswith('/files'):
            return [changed(p) for p in self.paths]
        return super().pages(path)

    def text(self, path, ref):
        if path in self.paths:
            return 'alpha  ' if ref == BASE else 'alpha'
        return super().text(path, ref)


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
        with patch.object(ResearchGH, 'pages', lambda self, path: [changed(NOTE, previous_filename='docs/x.md')]
                          if path.endswith('/files') else FakeGH.pages(self, path)):
            self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])

    def test_incomplete_or_ambiguous_file_list_needs_an_admin(self):
        user = {'login': 'collaborator', 'type': 'User'}
        gh, app, event, known, eligible = self.case()
        self.assertTrue(gate.scope_decider(gh, gh.pr, user))
        gh.pr['changed_files'] = 2
        self.assertFalse(gate.history(gh, gh.pr, known, eligible)[2])
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))
        gh, *_ = self.case(paths=(NOTE, NOTE))
        self.assertFalse(gate.scope_decider(gh, gh.pr, user))

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
        self.assertTrue(any('no completed reviewer report itemizing' in p['body'] for p in gh.posts))
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

"""A collaborator other than the author may accept itemized incomplete coverage, and nothing else."""
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


class CollaboratorScopeDecisions(unittest.TestCase):
    def case(self, permission='write', ids='scope-1-1-astra', pair=None, paths=(NOTE,), login='collaborator'):
        gh, app = ResearchGH(), FakeApp()
        gh.paths, gh.permission = tuple(paths), permission
        gh.pr['changed_files'] = len(gh.paths)
        pair = pair or scope_pair()
        app.prior(pair)
        command = comment('/protocol-b override '+HEAD+' '+ids+' Coverage limit accepted for a research note', login)
        gh.comments = [report_comment(e) for e in pair.values()]+[command]
        event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': login}}
        known = {ident: {'objection': 'App-recorded item'} for ident in gate.override_findings(pair, HEAD)}
        return gh, app, event, known

    def decide(self, gh, app, event):
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call')):
            return run_pipeline(gh, app, event=event,
                                provider=lambda _: (_ for _ in ()).throw(AssertionError('No review')))

    def test_non_author_collaborator_accepts_itemized_scope(self):
        for permission in ('write', 'maintain'):
            with self.subTest(permission=permission):
                gh, app, event, known = self.case(permission)
                overrides = gate.history(gh, gh.pr, known)[2]
                self.assertEqual(overrides['scope-1-1-astra']['authority'], 'scope-collaborator')
                self.assertEqual(overrides['scope-1-1-astra']['collaborator'], 'collaborator')
                _, app, errors, state = self.decide(gh, app, event)
                self.assertEqual(errors, [])
                self.assertEqual(app.final['conclusion'], 'success')
                self.assertFalse(state['reports']['astra']['review']['scope_complete'])
                self.assertEqual(state['scope_overrides'][0]['id'], 'scope-1-1-astra')
                self.assertIn('Accepted by a collaborator who is not the author with incomplete reviewer scope',
                              state['summary'])
                self.assertNotIn('Accepted by admin', state['summary'])

    def test_admin_record_is_unchanged(self):
        gh, app, event, known = self.case('admin')
        self.assertNotIn('authority', gate.history(gh, gh.pr, known)[2]['scope-1-1-astra'])
        _, app, errors, state = self.decide(gh, app, event)
        self.assertEqual(errors, [])
        self.assertIn('Accepted by admin with incomplete reviewer scope', state['summary'])

    def refused(self, **kwargs):
        gh, app, event, known = self.case(**kwargs)
        self.assertFalse(gate.history(gh, gh.pr, known)[2])
        _, app, errors, state = self.decide(gh, app, event)
        self.assertEqual(errors, [])
        self.assertIsNone(state)
        self.assertEqual(app.created, [])
        return gh

    def test_author_cannot_decide_own_pull_request(self):
        gh = self.refused(login='author')
        self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))
        gh = self.refused(login='Author')
        self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))

    def test_reader_has_no_effect(self):
        self.refused(permission='read')

    def test_protected_paths_need_an_admin(self):
        for path in ('p.tex', 'README.md', '.github/workflows/protocol-b.yml', 'scripts/check.py',
                     'tests/protocol_b/test_gate.py', 'docs/maintenance.md', 'manuscripts/v22.tex',
                     'releases/v22.json', 'research/version22/table.json', 'Research/Version22/table.json',
                     'lean/lakefile.toml', 'research/x/lean-toolchain'):
            with self.subTest(path=path):
                self.assertTrue(gate.scope_decision_protected(path))
                gh = self.refused(paths=(NOTE, path))
                self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))
        for path in (NOTE, 'research/versions-note/x.md', 'lean/ZInQ/Basic.lean', 'ThirdParty/GreenTao/A.lean'):
            self.assertFalse(gate.scope_decision_protected(path))

    def test_renamed_from_a_protected_path_needs_an_admin(self):
        gh, app, event, known = self.case()
        with patch.object(ResearchGH, 'pages', lambda self, path: [changed(NOTE, previous_filename='docs/x.md')]
                          if path.endswith('/files') else FakeGH.pages(self, path)):
            self.assertFalse(gate.history(gh, gh.pr, known)[2])

    def test_incomplete_file_list_needs_an_admin(self):
        gh, app, event, known = self.case()
        gh.pr['changed_files'] = 2
        self.assertFalse(gate.history(gh, gh.pr, known)[2])
        self.assertFalse(gate.scope_decider(gh, gh.pr, {'login': 'collaborator', 'type': 'User'}))

    def test_a_finding_is_never_a_collaborator_decision(self):
        pair = scope_pair(findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'A counterexample'}])
        gh = self.refused(ids='scope-1-1-astra,1-1-astra-F1', pair=pair)
        self.assertTrue(any('Only a repository admin' in p['body'] for p in gh.posts))

    def test_scope_alone_does_not_cover_a_finding(self):
        pair = scope_pair(findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'A counterexample'}])
        gh, app, event, known = self.case(pair=pair)
        self.assertEqual(set(gate.history(gh, gh.pr, known)[2]), {'scope-1-1-astra'})
        _, app, errors, state = self.decide(gh, app, event)
        self.assertIn('Uncovered findings: 1-1-astra-F1', str(app.final))
        self.assertNotEqual((app.final or {}).get('conclusion'), 'success')

    def test_scope_without_an_itemized_list_needs_an_admin(self):
        pairs = {'rejected without findings': scope_pair(scope_complete=True, not_reviewed=[]),
                 'metadata failure': scope_pair()}
        pairs['metadata failure']['astra']['post_review_error'] = 'Source record missing'
        for name, pair in pairs.items():
            with self.subTest(name=name):
                self.assertIsNotNone(gate.review_scope_item(pair['astra']))
                gh, app, event, known = self.case(pair=pair)
                self.assertFalse(gate.history(gh, gh.pr, known)[2])
                _, app, errors, state = self.decide(gh, app, event)
                self.assertNotEqual((app.final or {}).get('conclusion'), 'success')
                self.assertTrue(any('left no itemized list' in p['body'] for p in gh.posts))

    def test_oversized_scope_list_needs_an_admin(self):
        pair = scope_pair(not_reviewed=['Unread argument '+str(i)+' '+('x'*1200) for i in range(100)])
        gh, app, event, known = self.case(pair=pair)
        self.assertFalse(gate.history(gh, gh.pr, known)[2])

    def test_scope_shaped_name_without_app_record_is_not_a_decision(self):
        gh, app, event, _ = self.case()
        self.assertFalse(gate.history(gh, gh.pr)[2])

    def test_edited_comment_and_revoked_access_do_not_decide(self):
        gh, app, event, known = self.case()
        self.assertTrue(gate.history(gh, gh.pr, known)[2])
        gh.comments[-1]['updated_at'] = 'later'
        self.assertFalse(gate.history(gh, gh.pr, known)[2])
        gh, app, event, known = self.case()
        gh.permission = 'read'
        self.assertFalse(gate.history(gh, gh.pr, known)[2])

    def test_other_head_is_not_a_decision(self):
        gh, app, event, known = self.case()
        gh.comments[-1]['body'] = gh.comments[-1]['body'].replace(HEAD, BASE)
        self.assertFalse(gate.history(gh, gh.pr, known)[2])

    def test_summary_tells_collaborators_what_they_may_decide(self):
        text = gate.round_summary_body({'head': HEAD, 'check': 1, 'conclusion': 'failure',
                                        'reports': scope_pair()}, 'x/y', 'https://example.invalid/check')
        self.assertIn('a collaborator other than the author may accept these items', text)
        self.assertIn('findings always need an admin', text)


if __name__ == '__main__':
    unittest.main()

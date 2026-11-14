"""Offline spending controls exercise the trusted embedded gate, with no API calls."""
import copy
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, APP_ID, report, envelope, comment, changed, run_pipeline


class Spending(unittest.TestCase):
    def tearDown(self):
        gate.configure_budget([])

    def blocked(self, gh, app=None, event=None):
        provider = Mock(side_effect=AssertionError('No review may start'))
        with patch.object(gate, 'model_turn') as request:
            result = run_pipeline(gh, app, event=event, provider=provider)
            request.assert_not_called()
        provider.assert_not_called()
        return result

    def command(self):
        return {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                'sender': {'login': 'collaborator'}}

    def test_outside_author_waits_for_current_collaborator_command(self):
        for permission in ['read', 'triage', 'none']:
            gh = FakeGH()
            gh.author_permission = permission
            _, app, _, state = self.blocked(gh)
            self.assertEqual(app.final['conclusion'], 'action_required')
            self.assertIn("awaiting a collaborator's /protocol-b review", state['summary'])
        gh = FakeGH()
        gh.author_permission, gh.permission = 'read', 'write'
        provider = Mock(return_value=report())
        _, app, errors, _ = run_pipeline(gh, provider=provider, event=self.command())
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(app.final['conclusion'], 'success')

    def test_dispatch_or_unauthorized_comment_cannot_start_outside_review(self):
        gh = FakeGH()
        gh.author_permission = 'read'
        self.blocked(gh, event={'inputs': {'pull_request': '1'}})
        _, app, _, _ = self.blocked(gh, event=self.command())
        self.assertFalse(app.created)

    def test_current_write_author_can_start_automatic_review(self):
        for permission in ['write', 'maintain', 'admin']:
            gh = FakeGH()
            gh.author_permission = permission
            provider = Mock(return_value=report())
            _, _, errors, state = run_pipeline(gh, provider=provider)
            self.assertEqual(errors, [])
            self.assertEqual(provider.call_count, 2)
            self.assertEqual(state['automatic_rounds'], 1)

    def test_failed_required_check_blocks_even_explicit_command(self):
        for event in [None, self.command()]:
            gh = FakeGH()
            gh.permission = 'write'
            gh.check_runs = [{'id': 2, 'name': 'Paper build', 'head_sha': HEAD,
                             'status': 'completed', 'conclusion': 'failure', 'app': {'id': 15368}}]
            _, app, _, state = self.blocked(gh, event=event)
            self.assertEqual(app.final['conclusion'], 'action_required')
            self.assertIn('fix failing checks first: Paper build', state['summary'])

    def test_nonrequired_failure_and_pending_check_do_not_block(self):
        gh = FakeGH()
        gh.check_runs = [{'id': 1, 'name': 'Paper build', 'head_sha': HEAD,
                         'status': 'in_progress', 'conclusion': None, 'app': {'id': 15368}},
                        {'id': 2, 'name': 'Optional experiment', 'head_sha': HEAD,
                         'status': 'completed', 'conclusion': 'failure', 'app': {'id': 15368}}]
        provider = Mock(return_value=report())
        _, _, errors, _ = run_pipeline(gh, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)

    def test_new_failure_between_turns_prevents_another_provider_request(self):
        gh = FakeGH()
        review = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'fable', 'local mathematical')
        def model(*args):
            gh.check_runs = [{'id': 2, 'name': 'Paper build', 'head_sha': HEAD,
                             'status': 'completed', 'conclusion': 'failure', 'app': {'id': 15368}}]
            return ([{'type': 'tool_use', 'id': 'h', 'name': 'read_history', 'input': {}}],
                    gate.MODELS['fable'], {}, 'fixture', 'tool_use')
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.object(gate, 'model_turn', side_effect=model) as provider:
            with self.assertRaisesRegex(RuntimeError, 'fix failing checks first'):
                review.run()
        self.assertEqual(provider.call_count, 1)

    def rounds(self, count=4):
        gh, app = FakeGH(), FakeApp()
        for i in range(1, count+1):
            past = str(i) * 40
            marker = {'number': 1, 'run': str(100+i), 'attempt': '1', 'started': True, 'trigger': 'automatic'}
            app.checks[i] = {'id': i, 'name': 'Protocol B / test review', 'head_sha': past,
                            'status': 'completed', 'conclusion': 'action_required', 'app': {'id': APP_ID},
                            'output': {'text': json.dumps({'schema': 'protocol-b-decisions/v1', 'head': past,
                                                          'review_round': marker, 'reports': {}})}}
            gh.comments.append(comment(gate.ROUND_MARKER + '\n```json\n' + json.dumps({'check': i}) + '\n```'))
        return gh, app

    def test_four_started_rounds_block_push_and_survive_force_push(self):
        gh, app = self.rounds()
        _, app, _, state = self.blocked(gh, app)
        self.assertEqual(state['automatic_rounds'], 4)
        self.assertIn('Four automatic', state['summary'])
        self.assertIn('4/4', app.final['output']['summary'])

    def test_fourth_round_runs_but_fifth_requires_command(self):
        gh, app = self.rounds(3)
        provider = Mock(return_value=report())
        _, app, errors, state = run_pipeline(gh, app, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(state['automatic_rounds'], 4)
        gh, app = self.rounds(4)
        gh.permission = 'write'
        _, app, errors, state = run_pipeline(gh, app, provider=provider, event=self.command())
        self.assertEqual(errors, [])
        self.assertEqual(state['automatic_rounds'], 4)
        self.assertEqual(state['review_round']['trigger'], 'command')

    def test_forged_round_pointer_is_not_authority(self):
        gh, app = self.rounds()
        for c in app.checks.values():
            c['app']['id'] = 15368
        _, _, errors, state = run_pipeline(gh, app)
        self.assertEqual(errors, [])
        self.assertEqual(state['automatic_rounds'], 1)

    def test_legacy_app_reports_count_toward_automatic_limit(self):
        gh, app = self.rounds()
        gh.comments = []
        for i, check in app.checks.items():
            pair = {family: envelope(family, run=str(100+i), head=check['head_sha']) for family in gate.MODELS}
            check['output']['text'] = json.dumps({'schema': 'protocol-b-decisions/v1',
                                                  'head': check['head_sha'], 'reports': pair})
            gh.comments.append(comment(gate.MARKER + '\n```json\n' + json.dumps(pair['astra']) + '\n```'))
            gh.dispatched_runs[100+i] = {'event': 'pull_request_target', 'path': gate.WORKFLOW}
        _, _, _, state = self.blocked(gh, app)
        self.assertEqual(state['automatic_rounds'], 4)

    def test_reopen_ready_and_duplicate_sync_reuse_complete_same_policy(self):
        for action in ['reopened', 'ready_for_review', 'synchronize']:
            gh, app = FakeGH(), FakeApp()
            app.prior({'astra': envelope(), 'fable': envelope('fable')})
            _, app, errors, _ = self.blocked(gh, app, event={'pull_request': {'number': 1}, 'action': action})
            self.assertEqual(errors, [])
            self.assertFalse(app.created)

    def test_new_policy_or_incomplete_review_does_not_reuse(self):
        for incomplete in [False, True]:
            gh, app = FakeGH(), FakeApp()
            pair = {'astra': envelope(), 'fable': envelope('fable', complete=not incomplete)}
            app.prior(pair)
            provider = Mock(return_value=report())
            original = gate.same_policy
            with patch.object(gate, 'same_policy', side_effect=lambda gh, old, new: old == new):
                if not incomplete:
                    pair['astra']['policy_ref'] = 'e' * 40
                    app.prior(pair)
                _, _, errors, _ = run_pipeline(gh, app, provider=provider,
                    event={'pull_request': {'number': 1}, 'action': 'reopened'})
            self.assertEqual(errors, [])
            self.assertEqual(provider.call_count, 2)

    def test_profiles_follow_changed_paths_and_renames(self):
        for file in [changed('manuscripts/new.tex'), changed('archive/old.tex', previous_filename='manuscripts/old.tex')]:
            profile = gate.configure_budget([file])
            self.assertEqual(profile['context_token_budget'], 900000)
            body = gate.model_body('fable', 'trusted', [])
            self.assertEqual(body['tools'][-2]['max_uses'], 10)
            self.assertEqual(body['tools'][-1]['max_uses'], 20)
            self.assertEqual(body['tools'][-1]['max_content_tokens'], 50000)
        profile = gate.configure_budget([changed('docs/manuscripts/note.md')])
        self.assertEqual(profile['context_token_budget'], 400000)
        self.assertEqual(profile['fable_web_max_uses'], {'web_search': 3, 'web_fetch': 5})

    def test_initial_low_context_can_report_unreviewed_scope_but_not_accept(self):
        for decision in ['accept', 'changes_requested']:
            gh = FakeGH()
            review = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'fable', 'local mathematical')
            review.input['material'] = 'x' * 280000
            result = report(decision=decision, sources_read=[],
                            report='Not reviewed: source statements and all consumers. The remaining context is insufficient; these checks remain open.',
                            findings=[{'id': 'INCOMPLETE', 'location': 'whole PR', 'objection': 'Required source review remains unfinished.'}])
            response = ([{'type': 'tool_use', 'id': 'finish', 'name': 'finish_review', 'input': result}],
                        gate.MODELS['fable'], {}, 'fixture', 'end_turn')
            with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                 patch.object(gate, 'model_turn', return_value=response) as model:
                if decision == 'accept':
                    with self.assertRaises(ValueError):
                        review.run()
                else:
                    self.assertEqual(review.run()['decision'], 'changes_requested')
                self.assertIn(gate.FINISH_NOW_INSTRUCTION, model.call_args.args[1])


if __name__ == '__main__':
    unittest.main()

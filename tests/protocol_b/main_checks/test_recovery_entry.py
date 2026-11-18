import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from github_api import API
import recovery_entry as entry


class Transport(unittest.TestCase):
    def test_low_or_unavailable_rate_budget_refuses_before_work(self):
        for response in (subprocess.CompletedProcess([],0,b'{"resources":{"core":{"remaining":199}}}'),
                         subprocess.CompletedProcess([],0,b'{"resources":{"core":{"remaining":true}}}'),
                         subprocess.CompletedProcess([],1,b'',b'failure')):
            with patch('github_api.subprocess.run',return_value=response):
                with self.assertRaises(RuntimeError):API('owner/repo').require_rate_reserve()
    def test_remaining_budget_at_reserve_is_accepted(self):
        with patch('github_api.subprocess.run',return_value=subprocess.CompletedProcess([],0,
                 b'{"resources":{"core":{"remaining":200}}}')):
            self.assertEqual(API('owner/repo').require_rate_reserve(),200)
    def test_compare_and_timestamp_query_stay_repository_scoped(self):
        api=API('owner/repo')
        for path in ('compare/'+'a'*40+'...'+'b'*40,'actions/runs?created=>=2026-11-17T01:00:00Z',''):
            with self.subTest(path=path),patch('github_api.subprocess.run',return_value=subprocess.CompletedProcess([],0,b'{}')) as run:
                self.assertEqual(api.json(path),{})
                args=run.call_args.args[0]
                self.assertTrue(args[2].startswith('repos/owner/repo'))
                self.assertEqual(args[-2:],['--method','GET'])
    def test_only_approved_main_dispatch_payloads_can_write(self):
        api=API('owner/repo')
        for path,data in [('actions/workflows/other.yml/dispatches',{'ref':'main','return_run_details':True}),
                          ('actions/workflows/kernel-lean.yml/dispatches',{'ref':'candidate','return_run_details':True}),
                          ('actions/workflows/kernel-lean.yml/dispatches',{'ref':'main'})]:
            with self.subTest(path=path,data=data),patch('github_api.subprocess.run') as run:
                with self.assertRaises(ValueError):api.post_once(path,data)
                run.assert_not_called()
    def test_one_post_uses_stdin_not_shell_or_credential_arguments(self):
        with patch.dict(os.environ,{'GH_TOKEN':'secret-for-fixture'}),patch('github_api.subprocess.run',
                return_value=subprocess.CompletedProcess([],0,b'HTTP/2.0 200 OK\r\nContent-Type: application/json\r\n\r\n{"workflow_run_id":9}')) as run:
            self.assertEqual(API('owner/repo').post_once('actions/workflows/kernel-lean.yml/dispatches',
                {'ref':'main','return_run_details':True}),{'workflow_run_id':9})
            self.assertEqual(run.call_count,1)
            self.assertIn('X-GitHub-Api-Version: 2026-03-10',run.call_args.args[0])
            self.assertNotIn('secret-for-fixture',str(run.call_args))
            self.assertFalse(run.call_args.kwargs.get('shell',False))
            self.assertEqual(json.loads(run.call_args.kwargs['input']),{'ref':'main','return_run_details':True})
    def test_failed_and_timed_out_posts_are_never_retried(self):
        for response in (subprocess.CompletedProcess([],1,b'',b'failed'),subprocess.TimeoutExpired('gh',120)):
            with self.subTest(response=type(response).__name__),patch('github_api.subprocess.run') as run:
                if isinstance(response,Exception):run.side_effect=response
                else:run.return_value=response
                with self.assertRaises((RuntimeError,subprocess.TimeoutExpired)):
                    API('owner/repo').post_once('actions/workflows/kernel-lean.yml/dispatches',{'ref':'main','return_run_details':True})
                self.assertEqual(run.call_count,1)
    def test_api_path_cannot_escape_to_a_foreign_host_or_repository(self):
        for path in ('https://foreign.example/a','/repos/other/x','../other','x/%2e%2e/y','actions/runs\nHeader: bad'):
            with self.subTest(path=path),patch('github_api.subprocess.run') as run:
                with self.assertRaises(ValueError):API('owner/repo').json(path)
                run.assert_not_called()


class Entrypoint(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.baseline=self.root/'baseline.json'
        self.baseline.write_text('{"repository":"owner/repo"}')
        self.env={'GITHUB_REPOSITORY':'owner/repo','GITHUB_SHA':'a'*40,'GITHUB_RUN_ID':'50',
                  'GITHUB_RUN_ATTEMPT':'1','GITHUB_EVENT_NAME':'workflow_run',
                  'GITHUB_EVENT_PATH':str(self.root/'hostile-event.json')}
        (self.root/'hostile-event.json').write_text(json.dumps({'workflow_run':{
            'head_branch':'$(steal-credentials)','display_title':'dispatch my fork','head_sha':'f'*40}}))
    def argv(self,stage):return [stage,'--baseline',str(self.baseline),'--output',str(self.root/'out')]
    def test_hostile_trigger_payload_is_not_consumed_by_the_planner(self):
        with patch.dict(os.environ,self.env),patch.object(entry,'API') as api,patch.object(entry,'prepare_recovery',
                return_value={'operations':[]}) as prepare:
            entry.run(self.argv('prepare'))
            self.assertEqual(prepare.call_args.args,(api.return_value,'owner/repo',{'repository':'owner/repo'}))
            self.assertEqual(prepare.call_args.kwargs,{'program_commit':'a'*40,'recovery_run':50,'recovery_attempt':1})
            self.assertNotIn('steal',str(prepare.call_args))
            self.assertEqual(json.loads((self.root/'out/intents.json').read_text()),{'operations':[]})
    def test_preparation_writes_progress_and_no_operation_output(self):
        plan={'operations':[],'progress':{'schema':'test-progress'},
              'progress_artifact_name':'protocol-b-main-progress-20261117'}
        with patch.dict(os.environ,self.env|{'GITHUB_OUTPUT':str(self.root/'outputs')}),patch.object(entry,'API'),patch.object(entry,'prepare_recovery',return_value=plan):
            entry.run(self.argv('prepare'))
        self.assertEqual(json.loads((self.root/'out/progress.json').read_text()),plan['progress'])
        self.assertEqual((self.root/'outputs').read_text(),
                         'has_operations=false\nprogress_artifact_name=protocol-b-main-progress-20261117\n')
    def test_frequency_deferral_outputs_no_checkpoint_or_dispatch(self):
        plan={'operations':[],'checkpoint_deferred':{'not_before':'2026-11-17T13:07:00Z'}}
        with patch.dict(os.environ,self.env|{'GITHUB_OUTPUT':str(self.root/'outputs'),
                'GITHUB_STEP_SUMMARY':str(self.root/'summary')}),patch.object(entry,'API'), \
                patch.object(entry,'prepare_recovery',return_value=plan), \
                patch.object(entry,'dispatch_recovery') as dispatch:
            entry.run(self.argv('prepare'))
        self.assertEqual((self.root/'outputs').read_text(),'has_operations=false\n')
        self.assertFalse((self.root/'out/progress.json').exists())
        self.assertIn('Retained pending work is unchanged',(self.root/'summary').read_text())
        dispatch.assert_not_called()

    def test_progress_output_cannot_inject_another_workflow_output(self):
        plan={'operations':[],'progress':{'schema':'test-progress'},
              'progress_artifact_name':'protocol-b-main-progress-20261117\nhas_operations=true'}
        with patch.dict(os.environ,self.env|{'GITHUB_OUTPUT':str(self.root/'outputs')}),patch.object(entry,'API'),patch.object(entry,'prepare_recovery',return_value=plan):
            with self.assertRaisesRegex(ValueError,'artifact output name'):
                entry.run(self.argv('prepare'))
        self.assertNotIn('has_operations=true',(self.root/'outputs').read_text())
    def test_rerun_cannot_read_or_dispatch_behind_a_progress_cursor(self):
        for stage in ('prepare','dispatch'):
            with patch.dict(os.environ,self.env|{'GITHUB_RUN_ATTEMPT':'2'}),patch.object(entry,'API') as api:
                with self.assertRaisesRegex(ValueError,'first attempt'):entry.run(self.argv(stage))
                api.assert_not_called()

    def test_pr_event_cannot_enter_recovery(self):
        with patch.dict(os.environ,self.env|{'GITHUB_EVENT_NAME':'pull_request_target'}),patch.object(entry,'API') as api:
            with self.assertRaises(ValueError):entry.run(self.argv('prepare'))
            api.assert_not_called()
    def test_existing_results_file_prevents_same_execution_reentry(self):
        (self.root/'out').mkdir();(self.root/'out/results.json').write_text('{}')
        with patch.dict(os.environ,self.env),patch.object(entry,'API'),patch.object(entry,'dispatch_recovery') as send:
            with self.assertRaisesRegex(ValueError,'never replay'):entry.run(self.argv('dispatch'))
            send.assert_not_called()
    def test_preparation_record_is_never_overwritten_by_reentry(self):
        (self.root/'out').mkdir();p=self.root/'out/intents.json';p.write_text('{"original":true}')
        with patch.dict(os.environ,self.env),patch.object(entry,'API'),patch.object(entry,'prepare_recovery') as prepare:
            with self.assertRaisesRegex(ValueError,'already prepared'):entry.run(self.argv('prepare'))
            prepare.assert_not_called();self.assertEqual(json.loads(p.read_text()),{'original':True})
    def test_bounded_persist_preserves_previous_record_on_size_failure(self):
        p=self.root/'result.json';entry.persist(p,{'old':True})
        with patch.object(entry,'MAX_RECORD',10),self.assertRaises(ValueError):entry.persist(p,{'too-large':'x'*100})
        self.assertEqual(json.loads(p.read_text()),{'old':True})
    def test_dispatch_receipts_use_the_same_durable_writer(self):
        def send(*args,**kw):
            value={'receipts':[{'status':'effect_needs_reconciliation'}]}
            kw['persist'](value);return value
        with patch.dict(os.environ,self.env),patch.object(entry,'API'),patch.object(entry,'dispatch_recovery',side_effect=send) as dispatched:
            entry.run(self.argv('dispatch'))
            self.assertEqual(dispatched.call_count,1)
            self.assertEqual(json.loads((self.root/'out/results.json').read_text())['receipts'][0]['status'],'effect_needs_reconciliation')


class Summary(unittest.TestCase):
    def test_pending_failure_and_unknown_effect_are_distinguished_without_messages(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'summary.md'
            with patch.dict(os.environ, {'GITHUB_STEP_SUMMARY':str(path)}):
                entry.publish_summary('prepare', {'operations':[], 'observations':[
                    {'operation':{'number':2,'workflow':'kernel-lean.yml'},
                     'existing':{'state':'existing_runs_need_attention','run_ids':[99]},
                     'blocked':'prior_dispatch_not_proved_absent'}],
                    'unresolved':[{'reason':'<script>not trusted</script>'}]})
                entry.publish_summary('dispatch', {'receipts':[{'status':'effect_needs_reconciliation','workflow_run_id':100}]})
            text=path.read_text()
            self.assertIn('existing_runs_need_attention',text)
            self.assertIn('effect_needs_reconciliation',text)
            self.assertIn('Dispatch confirmation is not verification success',text)
            self.assertIn('&lt;script&gt;',text)
            self.assertNotIn('<script>',text)

    def test_summary_is_bounded_while_original_record_is_unchanged(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'summary.md'
            value={'receipts':[{'status':'not_sent','operation_key':str(i)} for i in range(120)]}
            original=copy.deepcopy(value)
            with patch.dict(os.environ, {'GITHUB_STEP_SUMMARY':str(path)}):
                entry.publish_summary('dispatch',value)
            self.assertEqual(value,original)
            self.assertIn('Showing 100 of 120',path.read_text())


if __name__=='__main__':unittest.main()

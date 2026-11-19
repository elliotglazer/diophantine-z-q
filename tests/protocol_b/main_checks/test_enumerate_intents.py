import copy
import unittest
from urllib.parse import quote
import test_discover_intents as fixtures
from enumerate_intents import enumerate_recovery_intents
from discover_intents import JOB, UPLOAD, DISPATCH


class EnumerateIntents(unittest.TestCase):
    def setUp(self):
        fixture=fixtures.RecoveryIntents();fixture.setUp();self.f=fixture
        self.baseline={'schema':'main-check-baseline/v1','repository':fixture.repo,
            'activation_commit':fixture.activation,'activated_at':'2026-11-17T00:00:00Z'}
        self.path='actions/workflows/50/runs?branch=main&created='+quote('>='+self.baseline['activated_at'],safe='')+'&per_page=100&page=1'
        fixture.publisher.update(workflow_id=50,created_at='2026-11-17T01:00:00Z')
        fixture.records['actions/workflows/protocol-b.yml']={'id':50,'path':fixture.publisher['path']}
        fixture.records[self.path]={'workflow_runs':[{'id':10}],'total_count':1}
    def result(self,**kw):
        value=enumerate_recovery_intents(self.f.api,self.f.repo,self.baseline,self.f.main,**kw)
        self.assertFalse(value['dispatch_authorized']);return value
    def test_prior_intent_recovers_pr_identity(self):
        r=self.result();self.assertFalse(r['unresolved']);self.assertEqual(r['pending_numbers'],[161])
        self.assertEqual(len(r['executions']),1)
    def test_current_attempt_excluded_but_previous_attempt_recovered(self):
        self.f.records['actions/runs/10/attempts/1']=copy.deepcopy(self.f.publisher)
        self.f.publisher['run_attempt']=2
        r=self.result(current_execution=(10,2));self.assertEqual(len(r['executions']),1)
        self.assertEqual(r['excluded'][0]['reason'],'current_preparation')
    def test_prior_publisher_failure_does_not_erase_an_intent(self):
        self.f.publisher.update(status='completed',conclusion='failure')
        self.assertEqual(len(self.result()['executions']),1)
    def test_missing_original_attempt_stays_unresolved(self):
        self.f.publisher['run_attempt']=2
        r=self.result(current_execution=(10,2));self.assertTrue(r['unlocated_effects'])
        self.assertEqual(r['unresolved'][0]['attempt'],1)
    def test_missing_intents_after_started_dispatch_is_not_absence(self):
        self.f.artifacts.clear();self.f.records[self.f.art_path]['total_count']=0
        r=self.result();self.assertTrue(r['unlocated_effects']);self.assertFalse(r['executions'])
    def test_missing_intents_before_explicitly_skipped_dispatch_is_absence(self):
        self.f.artifacts.clear();self.f.records[self.f.art_path]['total_count']=0
        self.f.job['steps'][1].update(conclusion='skipped',started_at=None)
        r=self.result();self.assertFalse(r['unresolved']);self.assertEqual(r['excluded'][0]['reason'],'dispatcher_explicitly_never_started')
    def test_explicit_skip_does_not_require_a_null_start_timestamp(self):
        self.f.artifacts.clear();self.f.records[self.f.art_path]['total_count']=0
        self.f.job['steps'][1].update(conclusion='skipped');self.f.job['steps'][1].pop('started_at')
        self.assertFalse(self.result()['unlocated_effects'])
    def test_active_job_with_no_artifact_is_not_safe_to_take_over(self):
        self.f.job['status']='in_progress';self.f.artifacts.clear();self.f.records[self.f.art_path]['total_count']=0
        self.assertTrue(self.result()['unlocated_effects'])
    def test_old_workflow_without_recovery_job_is_classified(self):
        self.f.records[self.f.job_path]={'jobs':[],'total_count':0}
        self.f.artifacts.clear();self.f.records[self.f.art_path]['total_count']=0
        r=self.result();self.assertFalse(r['unresolved']);self.assertEqual(r['excluded'][0]['reason'],'no_recovery_job')
    def test_active_run_with_job_not_yet_provisioned_is_not_absence(self):
        self.f.publisher['status']='in_progress'
        self.f.records[self.f.job_path]={'jobs':[],'total_count':0}
        self.f.artifacts.clear();self.f.records[self.f.art_path]['total_count']=0
        self.assertTrue(self.result()['unlocated_effects'])
    def test_original_attempt_identity_is_not_taken_from_latest(self):
        self.f.records['actions/runs/10/attempts/1']=dict(self.f.publisher,run_attempt=2)
        self.f.publisher['run_attempt']=2
        self.assertTrue(self.result(current_execution=(10,2))['unlocated_effects'])
    def test_orphan_archive_with_no_job_cannot_be_ignored(self):
        self.f.records[self.f.job_path]={'jobs':[],'total_count':0}
        self.assertTrue(self.result()['unlocated_effects'])
    def test_skipped_job_is_not_a_dispatch(self):
        self.f.job.update(conclusion='skipped',steps=[]);self.f.artifacts.clear();self.f.records[self.f.art_path]['total_count']=0
        self.assertEqual(self.result()['excluded'][0]['reason'],'recovery_job_skipped')
    def test_wrong_actual_workflow_is_unresolved(self):
        self.f.publisher['workflow_id']=60
        self.assertTrue(self.result()['unlocated_effects'])
    def test_old_time_and_other_trigger_are_excluded(self):
        for field,value,reason in [('created_at','2026-11-16T00:00:00Z','before_deployment_time'),('event','pull_request_target','not_a_recovery_trigger')]:
            original=self.f.publisher[field];self.f.publisher[field]=value
            self.assertEqual(self.result()['excluded'][0]['reason'],reason);self.f.publisher[field]=original
    def test_failed_individual_read_keeps_other_execution(self):
        self.f.records[self.path]={'workflow_runs':[{'id':9},{'id':10}],'total_count':2}
        r=self.result();self.assertEqual(r['unresolved'][0]['run'],9);self.assertEqual(len(r['executions']),1)
    def test_later_page_is_not_skipped(self):
        self.f.records[self.path]={'workflow_runs':[{'id':i} for i in range(1,101)],'total_count':101}
        self.f.records[self.path[:-1]+'2']={'workflow_runs':[{'id':101}],'total_count':101}
        for i in range(1,102):
            if i!=10:self.f.records[f'actions/runs/{i}']=dict(self.f.publisher,id=i,event='pull_request_target')
        r=self.result();self.assertEqual(len(r['excluded']),100);self.assertEqual(len(r['executions']),1)
    def test_incomplete_run_list_never_yields_partial_absence(self):
        self.f.records[self.path]['total_count']=2
        with self.assertRaisesRegex(ValueError,'incomplete'):self.result()
    def test_duplicate_run_identity_is_rejected(self):
        self.f.records[self.path]={'workflow_runs':[{'id':10},{'id':10}],'total_count':2}
        with self.assertRaisesRegex(ValueError,'identity'):self.result()
    def test_excessive_attempt_count_is_unresolved(self):
        self.f.publisher['run_attempt']=33
        self.assertTrue(self.result()['unlocated_effects'])


    def no_artifacts(self):
        self.f.artifacts.clear(); self.f.records[self.f.art_path]['total_count'] = 0

    def test_real_github_skipped_step_shape_with_timestamp_is_inert(self):
        # Fields from job 134330004196, run 44152406835 attempt 2, step 10.
        # Adapt only the name/number to the recovery dispatch; it was a kernel job.
        self.no_artifacts()
        self.f.job['steps'][1] = {'name': DISPATCH, 'number': 4, 'status': 'completed',
            'conclusion': 'skipped', 'started_at': '2026-11-17T20:08:14Z',
            'completed_at': '2026-11-17T20:08:14Z'}
        self.assertFalse(self.result()['unlocated_effects'])

    def test_terminal_cancelled_job_without_runner_is_inert(self):
        self.no_artifacts()
        self.f.job.update(status='completed', conclusion='cancelled', runner_id=0, steps=[])
        result = self.result()
        self.assertFalse(result['unlocated_effects'])
        self.assertEqual(result['excluded'][0]['reason'], 'cancelled_before_runner_assignment')
        self.f.job['runner_id'] = 42
        self.assertTrue(self.result()['unlocated_effects'])
        self.f.job.pop('runner_id')
        self.assertTrue(self.result()['unlocated_effects'])

    def test_failed_upload_and_unstarted_dispatch_do_not_poison_future_work(self):
        self.no_artifacts()
        self.f.job['steps'][1].update(status='pending', conclusion=None, started_at=None, completed_at=None)
        for conclusion in ('failure', 'cancelled', 'skipped'):
            with self.subTest(conclusion=conclusion):
                self.f.job['steps'][0].update(status='completed', conclusion=conclusion)
                result = self.result()
                self.assertFalse(result['unlocated_effects'])
                self.assertEqual(result['excluded'][0]['reason'], 'intent_upload_did_not_succeed')
        self.f.job['steps'][0].update(conclusion='success')
        self.assertTrue(self.result()['unlocated_effects'])

    def test_failed_bootstrap_without_upload_or_dispatch_is_inert(self):
        self.no_artifacts()
        self.f.job['steps'] = [{'name': 'Load recovery code from the actual main execution',
            'number': 1, 'status': 'completed', 'conclusion': 'failure'}]
        self.assertFalse(self.result()['unlocated_effects'])
        self.f.job['steps'][0]['status'] = 'in_progress'
        self.assertTrue(self.result()['unlocated_effects'])

    def test_started_dispatch_never_falls_back_to_failed_prerequisite(self):
        self.no_artifacts()
        self.f.job['steps'][0].update(conclusion='failure')
        self.assertTrue(self.result()['unlocated_effects'])
        self.f.job['steps'][1].update(status='pending', conclusion=None, started_at=None)
        self.f.job['status'] = 'in_progress'
        self.assertTrue(self.result()['unlocated_effects'])

    def test_ambiguous_step_records_do_not_prove_absence(self):
        self.no_artifacts()
        self.f.job['steps'][1].update(conclusion='skipped')
        self.f.job['steps'].append(copy.deepcopy(self.f.job['steps'][1]))
        self.assertTrue(self.result()['unlocated_effects'])


if __name__=='__main__':unittest.main()

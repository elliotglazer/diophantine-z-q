import copy
import unittest
from dispatch_intents import operation_key, reconcile_intent

class DispatchIntents(unittest.TestCase):
    def setUp(self):
        self.op={'repository':'owner/repo','number':160,'head':'a'*40,'merge':'b'*40,
                 'workflow':'kernel-lean.yml','ref':'main'}
        self.key=operation_key(self.op)
        self.intent={'schema':'main-check-intent/v1','operation_key':self.key,'operation':self.op,
                     'request':{'ref':'main','return_run_details':True},'recovery_run':10,'recovery_attempt':1}
        self.job={'run_id':10,'run_attempt':1,'status':'completed',
                  'steps':[{'name':'Dispatch Kernel','status':'completed','conclusion':'success','started_at':'2026-11-17T12:00:00Z'}]}
        self.receipt={'schema':'main-check-receipt/v1','operation_key':self.key,
                      'recovery_run':10,'recovery_attempt':1,'workflow_run_id':20}
        self.run={'id':20,'repository':{'full_name':'owner/repo'},'head_repository':{'full_name':'owner/repo'},
                  'path':'.github/workflows/kernel-lean.yml','head_branch':'main','head_sha':'b'*40,
                  'event':'workflow_dispatch','status':'queued','conclusion':None}
    def check(self,receipt=None,**kw):
        result=reconcile_intent(self.op,self.intent,receipt,self.job,dispatch_step='Dispatch Kernel',
                                current_runs=[self.run],enumeration_complete=True,**kw)
        self.assertFalse(result['dispatch_authorized'])
        return result
    def test_original_response_and_actual_queued_run_are_not_verification(self):
        self.assertEqual(self.check(self.receipt)['state'],'response_and_actual_run_confirmed')
    def test_completed_failed_run_does_not_authorize_retry(self):
        self.run.update(status='completed',conclusion='failure')
        result=self.check(self.receipt)
        self.assertEqual(result['run_id'],20);self.assertFalse(result['safe_absence'])
    def test_lost_response_after_started_step_is_uncertain(self):
        for status,conclusion in [('completed','success'),('completed','failure'),('completed','cancelled'),('in_progress',None),('pending',None)]:
            self.job['steps'][0].update(status=status,conclusion=conclusion)
            self.assertEqual(self.check()['state'],'effect_uncertain_no_retry')
    def test_no_job_steps_is_not_proof_of_no_effect(self):
        self.job['steps']=[]
        self.assertEqual(self.check()['state'],'ambiguous_dispatch_step')
    def test_terminal_explicit_skip_has_only_local_absence(self):
        self.job['steps'][0].update(conclusion='skipped',started_at=None)
        result=self.check();self.assertEqual(result['state'],'dispatcher_explicitly_not_started')
        self.assertTrue(result['safe_absence'])
    def test_skip_with_missing_or_present_start_is_uncertain(self):
        self.job['steps'][0]['conclusion']='skipped'
        self.assertFalse(self.check()['safe_absence'])
        self.job['steps'][0].pop('started_at')
        self.assertFalse(self.check()['safe_absence'])
    def test_running_executor_is_not_safe_to_take_over(self):
        self.job['status']='in_progress'
        self.job['steps'][0].update(conclusion='skipped',started_at=None)
        self.assertEqual(self.check()['state'],'executor_not_terminal')
    def test_duplicate_named_steps_are_ambiguous(self):
        self.job['steps'].append(copy.deepcopy(self.job['steps'][0]))
        self.assertEqual(self.check()['state'],'ambiguous_dispatch_step')
    def test_different_attempt_receipt_cannot_reconcile_current_intent(self):
        self.receipt['recovery_attempt']=2
        self.assertEqual(self.check(self.receipt)['state'],'invalid_receipt')
    def test_operation_key_does_not_alias_other_pr_or_workflow(self):
        for field,value in [('number',161),('head','c'*40),('merge','c'*40),('workflow','research-checks.yml')]:
            other=self.op|{field:value}
            self.assertNotEqual(operation_key(other),self.key)
    def test_request_cannot_change_ref_or_suppress_receipt(self):
        for request in ({'ref':'candidate','return_run_details':True},{'ref':'main'}):
            self.intent['request']=request
            self.assertEqual(self.check()['state'],'invalid_intent')
    def test_returned_run_needs_exact_real_run(self):
        self.receipt['workflow_run_id']=21
        self.assertEqual(self.check(self.receipt)['state'],'returned_run_not_reconciled')
    def test_branch_or_foreign_run_cannot_confirm_dispatch(self):
        original=copy.deepcopy(self.run)
        for field,value in [('head_branch','candidate'),('event','pull_request'),('repository',{'full_name':'other/repo'}),
                            ('head_repository',None),('path','.github/workflows/other.yml'),('head_sha','wrong')]:
            self.run=original|{field:value}
            self.assertEqual(self.check(self.receipt)['state'],'returned_run_identity_mismatch')
    def test_duplicate_run_records_do_not_hide_ambiguity(self):
        result=reconcile_intent(self.op,self.intent,self.receipt,self.job,dispatch_step='Dispatch Kernel',
                                current_runs=[self.run,self.run],enumeration_complete=True)
        self.assertEqual(result['state'],'returned_run_not_reconciled')
    def test_incomplete_enumeration_refuses_even_a_valid_receipt(self):
        result=reconcile_intent(self.op,self.intent,self.receipt,self.job,dispatch_step='Dispatch Kernel',
                                current_runs=[self.run],enumeration_complete=False)
        self.assertEqual(result['state'],'incomplete_run_enumeration')
    def test_invalid_receipt_does_not_fall_back_to_skip(self):
        self.job['steps'][0].update(conclusion='skipped',started_at=None)
        self.receipt['operation_key']='c'*64
        self.assertFalse(self.check(self.receipt)['safe_absence'])
    def test_receipt_without_run_keeps_uncertainty(self):
        self.receipt.pop('workflow_run_id')
        self.assertEqual(self.check(self.receipt)['state'],'receipt_has_no_confirmed_run')
    def test_unexpected_executor_is_refused(self):
        for field,value in [('run_id',11),('run_attempt',2)]:
            old=self.job[field];self.job[field]=value
            self.assertEqual(self.check()['state'],'wrong_executor');self.job[field]=old

    def test_authentic_terminal_result_can_prove_no_post_was_sent(self):
        receipt={k:v for k,v in self.receipt.items() if k!='workflow_run_id'}
        receipt.update(status='not_sent',request_sent=False)
        result=self.check(receipt,results_persisted_after_dispatch=True)
        self.assertEqual(result['state'],'authenticated_result_confirms_not_sent')
        self.assertTrue(result['safe_absence'])
    def test_unverified_or_uncertain_receipt_never_proves_absence(self):
        receipt={k:v for k,v in self.receipt.items() if k!='workflow_run_id'}
        receipt.update(status='not_sent',request_sent=False)
        self.assertFalse(self.check(receipt)['safe_absence'])
        for change in ({'request_sent':None},{'request_sent':True},{'status':'sending'},
                       {'workflow_run_id':99},{'response':{}},{'request_sent':0}):
            self.assertFalse(self.check(receipt|change,results_persisted_after_dispatch=True)['safe_absence'])
    def test_known_absence_requires_the_original_executor_terminal(self):
        receipt={k:v for k,v in self.receipt.items() if k!='workflow_run_id'}
        receipt.update(status='not_sent',request_sent=False);self.job['status']='in_progress'
        self.assertFalse(self.check(receipt,results_persisted_after_dispatch=True)['safe_absence'])
    def test_actual_main_workflow_path_suffix_preserves_run_evidence(self):
        self.run['path']+='@main'
        self.assertEqual(self.check(self.receipt)['state'],'response_and_actual_run_confirmed')


if __name__=='__main__': unittest.main()

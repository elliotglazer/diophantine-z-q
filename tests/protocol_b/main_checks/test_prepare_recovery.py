import copy
import unittest
from unittest.mock import patch
import prepare_recovery as planner
from dispatch_intents import operation_key


class API:
    def __init__(self):self.calls=[]
    def json(self,path):
        self.calls.append(path)
        if path=='git/ref/heads/main':return {'ref':'refs/heads/main','object':{'type':'commit','sha':'b'*40}}
        if path=='':return {'full_name':'owner/repo','id':7}
        if path=='compare/'+'b'*40+'...'+'b'*40:
            return {'base_commit':{'sha':'b'*40},'merge_base_commit':{'sha':'b'*40},'behind_by':0,'status':'identical'}
        raise AssertionError('Unexpected API read: '+path)


class Planner(unittest.TestCase):
    def setUp(self):
        self.api=API();self.repo='owner/repo';self.program='c'*40
        self.baseline={'schema':'main-check-baseline/v1','repository':self.repo,
            'activation_commit':'d'*40,'activated_at':'2026-11-17T00:00:00Z'}
        self.pr={'number':7,'state':'closed','merged':True,'head':{'sha':'a'*40},'merge_commit_sha':'b'*40,
            'merged_at':'2026-11-17T01:00:00Z','base':{'ref':'main','repo':{'full_name':self.repo}},
            'merged_by':{'login':'github-actions[bot]','type':'Bot'}}
        self.previous={'pending_numbers':[],'executions':[],'unlocated_effects':False,'unresolved':[]}
        self.queue={'candidates':[{'number':7,'pr':self.pr}],'unresolved':[]}
        self.transition={'exact_release_required':False}
        self.source={'eligible':True,'pr':self.pr,'accepted':{'check':{'id':1},'publisher':{'id':10}},
                     'requester':{'publisher':{'id':9}}}
        self.classified={'classification':{'state':'no_confirmed_run_check_intents','run_ids':[]},'runs':[]}
        self.patchers=[patch.object(planner,'enumerate_recovery_intents',return_value=self.previous),
            patch.object(planner,'discover_queue',return_value=self.queue),
            patch.object(planner,'release_transition',return_value=self.transition),
            patch.object(planner,'discover_deferred',return_value=self.source),
            patch.object(planner,'existing_evidence',return_value=self.classified)]
        self.mocks=[p.start() for p in self.patchers]
        for p in self.patchers:self.addCleanup(p.stop)
    def result(self,**kw):
        r=planner.prepare_recovery(self.api,self.repo,self.baseline,program_commit=self.program,
            recovery_run=50,recovery_attempt=1,**kw)
        self.assertFalse(r['dispatch_authorized']);return r
    def prior_intent(self):
        op={'repository':self.repo,'number':7,'head':'a'*40,'merge':'b'*40,'workflow':'kernel-lean.yml','ref':'main'}
        key=operation_key(op)
        intent={'schema':'main-check-intent/v1','operation':op,'operation_key':key,
            'request':{'ref':'main','return_run_details':True},'recovery_run':40,'recovery_attempt':1}
        execution={'operations':{key:{'intent':intent,'receipt':None}},'dispatch_step':'Dispatch confirmed main checks',
            'job':{'run_id':40,'run_attempt':1,'status':'completed','steps':[{'name':'Dispatch confirmed main checks',
                'status':'completed','conclusion':'failure','started_at':'2026-11-17T01:10:00Z'}]}}
        self.previous['executions'].append(execution);return execution
    def test_confirmed_deferred_source_plans_both_main_operations_without_writes(self):
        r=self.result();self.assertEqual(len(r['operations']),2)
        self.assertEqual({o['operation']['workflow'] for o in r['operations']},set(planner.WORKFLOWS))
        self.assertEqual({o['operation']['ref'] for o in r['operations']},{'main'})
        self.assertEqual({o['source']['requester_run'] for o in r['operations']},{9})
    def test_existing_success_running_or_failed_checks_do_not_start_again(self):
        for state in ('verification_passed','existing_run_in_progress','existing_runs_need_attention'):
            self.classified['classification']['state']=state
            self.assertFalse(self.result()['operations'])
        self.mocks[3].assert_not_called()
    def test_exact_release_missing_on_later_main_is_not_repaired_by_a_later_tree(self):
        self.transition['exact_release_required']=True
        self.classified['classification']['state']='missing_exact_release_run'
        r=self.result();self.assertFalse(r['operations']);self.assertTrue(all(x['release_transition']['exact_release_required'] for x in r['observations']))
    def test_unknown_prior_effect_blocks_new_plans(self):
        self.previous.update(unlocated_effects=True,unresolved=[{'run':41,'reason':'lost effect'}])
        r=self.result();self.assertFalse(r['operations']);self.assertEqual(r['prior_execution_errors'][0]['run'],41)
        self.mocks[3].assert_not_called()
    def test_uncertain_kernel_intent_does_not_block_unrelated_research(self):
        self.prior_intent();r=self.result()
        self.assertEqual([o['operation']['workflow'] for o in r['operations']],['research-checks.yml'])
        self.assertEqual(r['observations'][1]['blocked'],'prior_dispatch_not_proved_absent')
    def test_explicitly_skipped_prior_execution_allows_fresh_plan_not_dispatch(self):
        execution=self.prior_intent();execution['job']['steps'][0].update(conclusion='skipped',started_at=None)
        self.assertEqual(len(self.result()['operations']),2)
    def test_receipt_with_returned_id_but_absent_run_never_retries(self):
        execution=self.prior_intent();item=next(iter(execution['operations'].values()))
        item['receipt']={'schema':'main-check-receipt/v1','operation_key':item['intent']['operation_key'],
            'recovery_run':40,'recovery_attempt':1,'workflow_run_id':99}
        r=self.result();self.assertEqual(len(r['operations']),1)
        self.assertEqual(r['observations'][1]['prior_executions'][0]['state'],'returned_run_not_reconciled')
    def test_retained_pending_ids_are_passed_to_complete_queue_scan(self):
        self.previous['pending_numbers']=[2,7]
        self.result();self.assertEqual(self.mocks[1].call_args.kwargs['pending_numbers'],[2,7])
    def test_no_authenticated_deferred_source_means_no_plan(self):
        self.source['eligible']=False
        r=self.result();self.assertFalse(r['operations']);self.assertEqual(len(r['unresolved']),2)
    def test_unmerged_retained_pr_is_not_dispatched(self):
        self.pr['merged']=False
        r=self.result();self.assertFalse(r['operations']);self.assertTrue(r['unresolved'])
        self.mocks[3].assert_not_called()
    def test_source_head_changed_since_initial_scan_is_refused(self):
        self.source['pr']=dict(self.pr,head={'sha':'f'*40})
        self.assertFalse(self.result()['operations'])
    def test_source_merge_changed_since_initial_scan_is_refused(self):
        self.source['pr']=dict(self.pr,merge_commit_sha='f'*40)
        self.assertFalse(self.result()['operations'])
    def test_human_merge_is_not_a_gate_recovery(self):
        self.source['pr']=dict(self.pr,merged_by={'login':'owner','type':'User'})
        self.assertFalse(self.result()['operations'])
    def test_foreign_ancestry_cannot_get_a_plan(self):
        with patch.object(planner,'_ancestor',side_effect=ValueError('not on main')):
            r=self.result();self.assertFalse(r['operations']);self.assertTrue(r['unresolved'])
        self.mocks[3].assert_not_called()
    def test_operation_bound_keeps_other_work_for_next_batch(self):
        r=self.result(limit=1);self.assertEqual(len(r['operations']),1)
        self.assertEqual(r['observations'][1]['blocked'],'next_batch')
    def test_failed_individual_source_does_not_erase_other_plan(self):
        self.mocks[3].side_effect=[ValueError('unavailable source'),self.source]
        r=self.result();self.assertEqual([o['operation']['workflow'] for o in r['operations']],['kernel-lean.yml'])
        self.assertEqual(r['unresolved'][0]['workflow'],'research-checks.yml')
    def test_incomplete_prior_execution_enumeration_never_returns_partial_plan(self):
        self.mocks[0].side_effect=ValueError('incomplete listing')
        with self.assertRaisesRegex(ValueError,'incomplete'):self.result()
        self.mocks[1].assert_not_called()
    def test_actual_main_is_recorded_in_every_intent(self):
        r=self.result();self.assertEqual(r['observed_main'],'b'*40)
        self.assertTrue(all(o['planned_main']=='b'*40 for o in r['operations']))


if __name__=='__main__':unittest.main()

import copy
import unittest
from existing_runs import classify_existing_runs

class ExistingRuns(unittest.TestCase):
    def setUp(self):
        self.merge='a'*40; self.later='b'*40
        self.op={'repository':'owner/repo','workflow':'kernel-lean.yml','merge':self.merge}
        self.run={'id':42,'repository':{'full_name':'owner/repo'},'head_repository':{'full_name':'owner/repo'},
            'head_branch':'main','event':'workflow_dispatch','path':'.github/workflows/kernel-lean.yml',
            'head_sha':self.merge,'created_at':'2026-11-17T12:00:01Z','status':'completed','conclusion':'success'}
        self.args={'merged_at':'2026-11-17T12:00:00Z','observed_main':self.merge,
                   'exact_release':False,'enumeration_complete':True}
    def classify(self,runs=None,comparisons=None,**kw):
        result=classify_existing_runs(self.op,[self.run] if runs is None else runs,comparisons or {},**(self.args|kw))
        self.assertFalse(result['dispatch_authorized'])
        return result
    def test_exact_run_is_verified(self):
        self.assertEqual(self.classify()['state'],'verification_passed')
    def test_running_does_not_mean_verified(self):
        for status in ('queued','pending','waiting','requested','in_progress'):
            self.run.update(status=status,conclusion=None)
            self.assertEqual(self.classify()['state'],'existing_run_in_progress')
    def test_failed_or_unexecuted_attempt_requires_attention_not_retry(self):
        for conclusion in ('failure','cancelled','timed_out','startup_failure','action_required','stale','neutral','skipped'):
            self.run['conclusion']=conclusion
            self.assertTrue(self.classify()['needs_attention'])
    def test_success_does_not_hide_failed_attempt(self):
        other=copy.deepcopy(self.run);other.update(id=43,conclusion='cancelled')
        result=self.classify([self.run,other])
        self.assertTrue(result['needs_attention']);self.assertEqual(result['run_ids'],[42,43])
    def test_wrong_origin_or_pr_runs_never_supply_evidence(self):
        for field,value in [('repository',{'full_name':'foreign/fork'}),('head_repository',None),
            ('head_branch','contributor'),('event','pull_request'),('path','.github/workflows/forged.yml')]:
            run=copy.deepcopy(self.run);run[field]=value
            self.assertEqual(self.classify([run])['state'],'no_confirmed_run_check_intents')
    def test_old_run_is_not_current_merge_evidence(self):
        self.run['created_at']='2026-11-17T11:59:59Z'
        self.assertEqual(self.classify()['state'],'no_confirmed_run_check_intents')
    def test_later_commit_needs_real_comparison(self):
        self.run['head_sha']=self.later
        self.assertEqual(self.classify()['state'],'missing_ancestry')
        comparison={'base_commit':{'sha':self.merge},'commits':[{'sha':self.later}],'behind_by':0,'status':'ahead'}
        self.assertEqual(self.classify(comparisons={self.later:comparison})['state'],'verification_passed')
        for field,value in [('base_commit',{'sha':'c'*40}),('commits',[{'sha':'d'*40}]),('behind_by',False)]:
            bad=copy.deepcopy(comparison);bad[field]=value
            self.assertTrue(self.classify(comparisons={self.later:bad})['needs_attention'])
    def test_diverged_commit_cannot_cover_merge(self):
        self.run['head_sha']=self.later
        comparison={'base_commit':{'sha':self.merge},'commits':[{'sha':self.later}],'behind_by':1,'status':'diverged'}
        self.assertEqual(self.classify(comparisons={self.later:comparison})['state'],'no_confirmed_run_check_intents')
    def test_release_cannot_be_satisfied_by_later_main(self):
        self.run['head_sha']=self.later
        result=self.classify(exact_release=True,observed_main=self.later)
        self.assertEqual(result['state'],'missing_exact_release_run');self.assertTrue(result['needs_attention'])
    def test_exact_release_pending_run_is_retained_when_main_advanced(self):
        self.run.update(status='in_progress',conclusion=None)
        self.assertEqual(self.classify(exact_release=True,observed_main=self.later)['run_ids'],[42])
    def test_empty_list_never_authorizes_dispatch_before_intent_checks(self):
        self.assertEqual(self.classify([])['state'],'no_confirmed_run_check_intents')
    def test_incomplete_enumeration_blocks_even_apparent_success(self):
        self.assertEqual(self.classify(enumeration_complete=False)['state'],'incomplete_enumeration')
    def test_duplicate_snapshot_conflict_is_unresolved(self):
        other=copy.deepcopy(self.run);other['conclusion']='failure'
        self.assertEqual(self.classify([self.run,other])['state'],'conflicting_run_records')
        self.assertEqual(self.classify([self.run,self.run])['run_ids'],[42])
    def test_malformed_records_remain_unresolved(self):
        for field,value in [('head_sha','abc'),('id',True),('created_at','yesterday'),('status','invented')]:
            run=copy.deepcopy(self.run);run[field]=value
            self.assertTrue(self.classify([run])['needs_attention'])

    def test_main_ref_suffix_does_not_hide_a_real_run(self):
        self.run['path']+='@main'
        self.assertEqual(self.classify()['state'],'verification_passed')
    def test_different_ref_suffix_does_not_supply_main_evidence(self):
        self.run['path']+='@candidate'
        self.assertEqual(self.classify()['state'],'no_confirmed_run_check_intents')


if __name__=='__main__': unittest.main()

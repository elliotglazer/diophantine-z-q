import copy,unittest
from unittest.mock import patch
from dispatch_intents import operation_key
import revalidate_operations as check
import prepare_recovery as planner


class API:
    def __init__(self,pr):self.pr=pr;self.paths=[]
    def json(self,path):self.paths.append(path);return copy.deepcopy(self.pr)


class Revalidate(unittest.TestCase):
    def setUp(self):
        self.op={'repository':'owner/repo','number':9,'head':'a'*40,'merge':'b'*40,'workflow':'kernel-lean.yml','ref':'main'}
        self.key=operation_key(self.op)
        self.intent={'schema':'main-check-intent/v1','operation_key':self.key,'operation':self.op,
            'request':{'ref':'main','return_run_details':True},'recovery_run':50,'recovery_attempt':1,'exact_release':False}
        self.pr={'number':9,'merge_commit_sha':'b'*40,'head':{'sha':'a'*40},'merged_at':'2026-11-17T00:00:00Z'}
        self.api=API(self.pr)
        self.plan={'repository':'owner/repo','repository_id':7,'recovery_run':50,'recovery_attempt':1,
            'program_commit':'c'*40,'discovery':{'run_sequence_complete':True,'retained_executions':[40,50]}}
        self.original={'plan':self.plan,'operations':{self.key:{'intent':self.intent,'receipt':None}}}
        self.previous={'unresolved':[],'unlocated_effects':False,'executions':[]}
        self.evidence={'classification':{'state':'no_confirmed_run_check_intents'},'runs':[]}
        self.patches=[patch.object(planner,'main_tip',return_value='b'*40),
                      patch.object(planner,'existing_evidence',return_value=self.evidence),
                      patch.object(check,'enumerate_recovery_intents',return_value=self.previous)]
        self.mocks=[p.start() for p in self.patches]
        for p in self.patches:self.addCleanup(p.stop)
    def result(self):
        return check.revalidate_operations(self.api,'owner/repo',{},self.original,
                program_commit='c'*40,recovery_run=50,recovery_attempt=1)
    def test_rechecks_only_uploaded_operations_and_original_executors(self):
        r=self.result();self.assertEqual(r['operations'],[self.intent])
        self.assertEqual(self.mocks[2].call_args.kwargs['run_ids'],[40])
        self.assertEqual(self.api.paths,['pulls/9'])
    def test_incomplete_sequence_or_wrong_plan_identity_refuses(self):
        for key,value in [('repository','evil/repo'),('recovery_attempt',2),('program_commit','d'*40)]:
            old=self.plan[key];self.plan[key]=value
            with self.assertRaises(ValueError):self.result()
            self.plan[key]=old
        self.plan['discovery']['run_sequence_complete']=False
        with self.assertRaises(ValueError):self.result()
    def test_unlocated_executor_refuses_all_operations(self):
        self.previous['unlocated_effects']=True
        with self.assertRaisesRegex(ValueError,'unresolved'):self.result()
    def test_changed_pr_identity_is_refused(self):
        self.pr['head']['sha']='d'*40
        with self.assertRaisesRegex(ValueError,'identity changed'):self.result()
    def test_actual_existing_run_never_replays_operation(self):
        for state in ('verification_passed','existing_run_in_progress','existing_runs_need_attention'):
            self.evidence['classification']['state']=state;self.assertFalse(self.result()['operations'])
    def old_executor(self,step):
        intent=copy.deepcopy(self.intent);intent['recovery_run']=40
        return {'operations':{self.key:{'intent':intent,'receipt':None}},'dispatch_step':'dispatch',
                'job':{'run_id':40,'run_attempt':1,'status':'completed','steps':[dict(name='dispatch',**step)]}}
    def test_unknown_old_dispatch_effect_remains_blocking(self):
        self.previous['executions']=[self.old_executor({'status':'completed','conclusion':'failure'})]
        self.assertFalse(self.result()['operations'])
    def test_explicit_old_skip_allows_current_fresh_recheck(self):
        self.previous['executions']=[self.old_executor({'status':'completed','conclusion':'skipped','started_at':'2026-11-17T00:00:00Z'})]
        self.assertEqual(self.result()['operations'],[self.intent])

    def test_revalidation_resumes_uploaded_search_and_returns_new_cursor(self):
        original={'pending_windows':[{'start':'before','end':'then'}]}
        updated={'pending_windows':[]}
        self.plan['existing_searches']={self.key:original}
        self.evidence['search']=updated
        result=self.result()
        self.assertEqual(self.mocks[1].call_args.kwargs['cursor'],original)
        self.assertEqual(result['existing_searches'][self.key],updated)
        self.assertEqual(self.plan['existing_searches'][self.key],original)
        self.assertEqual(result['operations'],[self.intent])
    def test_newly_found_run_revokes_dispatch_without_losing_search_progress(self):
        self.plan['existing_searches']={self.key:{'pending_windows':[]}}
        self.evidence.update(classification={'state':'existing_run_in_progress'},search={'newly_found':123})
        result=self.result()
        self.assertFalse(result['operations'])
        self.assertEqual(result['existing_searches'][self.key],{'newly_found':123})

if __name__=='__main__':unittest.main()

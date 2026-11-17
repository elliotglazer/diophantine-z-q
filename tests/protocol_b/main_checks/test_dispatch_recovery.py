import copy
import unittest
from unittest.mock import patch
import dispatch_recovery as dispatch
from dispatch_intents import operation_key


class API:
    def __init__(self):self.posts=[];self.runs={};self.fail=False;self.before_post=None
    def json(self,path):return copy.deepcopy(self.runs[int(path.rsplit('/',1)[-1])])
    def post_once(self,path,body):
        if self.before_post:self.before_post(path,body)
        self.posts.append((path,body))
        if self.fail:raise RuntimeError('Response lost after possible acceptance')
        ident=100+len(self.posts)
        if ident not in self.runs:
            self.runs[ident]={'id':ident,'event':'workflow_dispatch','head_branch':'main',
                'path':'.github/workflows/'+path.split('/')[2], 'head_sha':'b'*40,
                'repository':{'full_name':'owner/repo'},'head_repository':{'full_name':'owner/repo'}}
        return {'workflow_run_id':ident}


class Dispatcher(unittest.TestCase):
    def setUp(self):
        self.api=API();self.saved=[];self.repo='owner/repo';self.program='c'*40
        self.baseline={'activation_commit':'d'*40}
        self.ops=[]
        for workflow in ('research-checks.yml','kernel-lean.yml'):
            op={'repository':self.repo,'number':9,'head':'a'*40,'merge':'b'*40,'workflow':workflow,'ref':'main'}
            self.ops.append({'schema':'main-check-intent/v1','operation':op,'operation_key':operation_key(op),
                'source':{'accepted_check':1,'accepted_run':2,'requester_run':3},'exact_release':False,
                'recovery_run':50,'recovery_attempt':1})
        self.original={'publisher':{'head_sha':self.program,'status':'in_progress'},
            'job':{'status':'in_progress','steps':[{'name':dispatch.DISPATCH,'status':'in_progress'}]},
            'artifacts':{'intents':{'id':10}},'operations':{
                x['operation_key']:{'intent':x,'receipt':None} for x in self.ops}}
        self.fresh={'repository':self.repo,'repository_id':7,'recovery_run':50,'recovery_attempt':1,
                    'program_commit':self.program,'operations':copy.deepcopy(self.ops)}
        self.pr={'merged':True,'state':'closed','merge_commit_sha':'b'*40,'head':{'sha':'a'*40},
                 'merged_at':'2026-11-17T00:00:00Z','merged_by':{'login':'github-actions[bot]','type':'Bot'}}
        self.source={'eligible':True,'pr':self.pr,'accepted':{'check':{'id':1},'publisher':{'id':2}},
                     'requester':{'publisher':{'id':3}}}
        self.transition={'exact_release_required':False}
        self.existing={'classification':{'state':'no_confirmed_run_check_intents'}}
        data=[('main_tip',{'return_value':'b'*40}),('discover_recovery_intents',{'return_value':self.original}),
              ('prepare_recovery',{'return_value':self.fresh}),('discover_deferred',{'return_value':self.source}),
              ('_ancestor',{}),('release_transition',{'return_value':self.transition}),
              ('existing_evidence',{'return_value':self.existing})]
        self.mocks={}
        for name,kw in data:
            p=patch.object(dispatch,name,**kw);self.mocks[name]=p.start();self.addCleanup(p.stop)
        self.api.before_post=self.check_saved_boundary
    def persist(self,value):self.saved.append(copy.deepcopy(value))
    def check_saved_boundary(self,path,body):
        receipt=self.saved[-1]['receipts'][-1]
        self.assertEqual(receipt['status'],'sending');self.assertIsNone(receipt['request_sent'])
        self.assertEqual(path,'actions/workflows/'+receipt['workflow']+'/dispatches')
        self.assertEqual(body,{'ref':'main','return_run_details':True})
    def run_dispatch(self,persist=None):
        return dispatch.dispatch_recovery(self.api,self.repo,self.baseline,program_commit=self.program,
                    recovery_run=50,recovery_attempt=1,persist=persist or self.persist)
    def assert_no_posts(self):self.assertEqual(self.api.posts,[])
    def test_durable_intents_then_fresh_merge_then_two_one_shot_dispatches(self):
        r=self.run_dispatch();self.assertEqual(len(self.api.posts),2)
        self.assertEqual([x['status'] for x in r['receipts']],['run_confirmed','run_confirmed'])
        self.assertEqual([x['workflow_run_id'] for x in r['receipts']],[101,102])
        self.assertEqual({x['merge_commit_sha'] for x in r['receipts']},{'b'*40})
    def test_missing_or_invalid_uploaded_intent_cannot_dispatch(self):
        self.mocks['discover_recovery_intents'].side_effect=ValueError('no completed original upload')
        with self.assertRaises(ValueError):self.run_dispatch()
        self.assert_no_posts();self.assertEqual(self.saved,[])
    def test_terminal_or_different_program_executor_is_refused(self):
        original=copy.deepcopy(self.original)
        for change in ('terminal','different_program','step_not_running'):
            self.original.clear();self.original.update(copy.deepcopy(original))
            if change=='terminal':self.original['job']['status']='completed'
            elif change=='different_program':self.original['publisher']['head_sha']='e'*40
            else:self.original['job']['steps'][0]['status']='queued'
            with self.subTest(change=change),self.assertRaises(ValueError):self.run_dispatch()
            self.assert_no_posts()
    def test_existing_result_never_replays_current_attempt(self):
        self.original['artifacts']['results']={'id':11}
        with self.assertRaisesRegex(ValueError,'already has results'):self.run_dispatch()
        self.assert_no_posts()
    def test_fresh_reconciliation_refusal_prevents_all_writes(self):
        self.mocks['prepare_recovery'].side_effect=ValueError('uncertain earlier dispatcher')
        with self.assertRaises(ValueError):self.run_dispatch()
        self.assert_no_posts()
    def test_operation_removed_from_fresh_plan_is_recorded_not_sent(self):
        self.fresh['operations']=[];r=self.run_dispatch();self.assert_no_posts()
        self.assertTrue(all(x['request_sent'] is False for x in r['receipts']))
    def test_changed_source_record_prevents_sending(self):
        self.source['accepted']['check']['id']=77
        r=self.run_dispatch();self.assert_no_posts();self.assertIn('changed accepted',r['receipts'][0]['reason'])
    def test_no_confirmed_merge_prevents_sending(self):
        self.pr['merged']=False;r=self.run_dispatch();self.assert_no_posts()
        self.assertTrue(all(x['status']=='not_sent' for x in r['receipts']))
    def test_human_merge_is_not_a_gate_recovery(self):
        self.pr['merged_by']={'login':'owner','type':'User'};self.run_dispatch();self.assert_no_posts()
    def test_existing_actual_run_prevents_duplicate_dispatch(self):
        for state in ('verification_passed','existing_run_in_progress','existing_runs_need_attention'):
            self.existing['classification']['state']=state
            self.run_dispatch();self.assert_no_posts()
    def test_release_main_advancing_before_send_is_not_sent(self):
        for op in self.ops:op['exact_release']=True
        for op in self.fresh['operations']:op['exact_release']=True
        self.transition['exact_release_required']=True
        self.mocks['main_tip'].return_value='e'*40
        r=self.run_dispatch();self.assert_no_posts();self.assertIn('no longer main',r['receipts'][0]['reason'])
    def test_nonrelease_actual_newer_head_is_recorded(self):
        self.api.runs[101]={'id':101,'event':'workflow_dispatch','head_branch':'main','head_sha':'e'*40,
            'path':'.github/workflows/research-checks.yml@main','repository':{'full_name':self.repo},
            'head_repository':{'full_name':self.repo}}
        r=self.run_dispatch();self.assertTrue(r['receipts'][0]['head_differs_from_merge'])
        self.assertEqual(r['receipts'][0]['head_sha'],'e'*40)
    def test_release_race_after_send_is_not_claimed_exact_or_retried(self):
        for op in self.ops:op['exact_release']=True
        for op in self.fresh['operations']:op['exact_release']=True
        self.transition['exact_release_required']=True
        self.api.runs[101]={'id':101,'event':'workflow_dispatch','head_branch':'main','head_sha':'e'*40,
            'path':'.github/workflows/research-checks.yml','repository':{'full_name':self.repo},
            'head_repository':{'full_name':self.repo}}
        r=self.run_dispatch();self.assertFalse(r['receipts'][0]['exact_release_covered'])
        self.assertIn('attention',r['receipts'][0]);self.assertEqual(len(self.api.posts),2)
    def test_lost_response_is_never_retried(self):
        self.api.fail=True;r=self.run_dispatch();self.assertEqual(len(self.api.posts),2)
        self.assertTrue(all(x['status']=='effect_needs_reconciliation' and x['request_sent'] is None for x in r['receipts']))
    def test_response_without_run_id_is_preserved_as_uncertain(self):
        self.api.post_once=lambda path,body: {}
        r=self.run_dispatch();self.assertEqual(r['receipts'][0]['response'],{})
        self.assertEqual(r['receipts'][0]['status'],'effect_needs_reconciliation')
    def test_returned_foreign_run_is_not_confirmed(self):
        self.api.runs[101]={'id':101,'head_sha':'b'*40,'head_branch':'candidate'}
        r=self.run_dispatch();self.assertEqual(r['receipts'][0]['status'],'effect_needs_reconciliation')
        self.assertEqual(r['receipts'][0]['workflow_run_id'],101)
    def test_initial_record_failure_makes_no_request(self):
        with self.assertRaises(OSError):self.run_dispatch(lambda _:(_ for _ in ()).throw(OSError('disk full')))
        self.assert_no_posts()
    def test_pre_send_record_failure_makes_no_request(self):
        def persist(value):
            if value['receipts']:raise OSError('intent boundary write failed')
            self.persist(value)
        with self.assertRaises(OSError):self.run_dispatch(persist)
        self.assert_no_posts()
    def test_post_response_record_failure_never_retries_the_post(self):
        def persist(value):
            if any(r['status']=='response_received' for r in value['receipts']):raise OSError('response write failed')
            self.persist(value)
        r=self.run_dispatch(persist);self.assertEqual(len(self.api.posts),2)
        self.assertTrue(all(x['status']=='effect_needs_reconciliation' for x in r['receipts']))


if __name__=='__main__':unittest.main()

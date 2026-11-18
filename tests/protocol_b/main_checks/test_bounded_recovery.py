import copy,datetime,unittest
from unittest.mock import patch
import bounded_recovery as bounded
import prepare_recovery as planner
from read_budget import BoundedReads,ReadBudgetExceeded


class API:
    def __init__(self):
        self.calls=[];self.records={
          'git/ref/heads/main':{'ref':'refs/heads/main','object':{'type':'commit','sha':'c'*40}},
          '':{'id':7,'full_name':'owner/repo'},
          'actions/workflows/protocol-b.yml':{'id':99,'path':'.github/workflows/protocol-b.yml'},
          'actions/runs/5':{'id':5,'workflow_id':99,'run_number':4,'repository':{'full_name':'owner/repo'}},
          'actions/runs/10':{'id':10,'run_attempt':1,'head_sha':'b'*40,'head_branch':'main',
              'workflow_id':99,'event':'schedule','run_number':10,
              'path':'.github/workflows/protocol-b.yml',
              'repository':{'id':7,'full_name':'owner/repo'},'head_repository':{'id':7}}}
    def json(self,path):self.calls.append(path);return copy.deepcopy(self.records[path])


class Bounded(unittest.TestCase):
    def setUp(self):
        self.api=API();self.baseline={'repository':'owner/repo','activation_commit':'a'*40,
            'activated_at':'2026-11-17T00:00:00Z','workflow_run_id':5,'workflow_run_number':4}
        self.history={'cursor':{'schema':'main-check-history/v1','repository':'owner/repo',
            'activation_commit':'a'*40,'frontier':'c'*40,'scan_head':None,'next_commit':None},
            'candidates':[],'unresolved':[],'enumeration_complete':True}
        self.scan={'runs':[],'enumeration_complete':True,'partial':None,'unresolved':[]}
        self.previous={'pending_numbers':[],'unresolved':[],'executions':[],'unlocated_effects':False}
        self.plan={'operations':[],'observations':[],'unresolved':[]}
        self.mocks={}
        for module,name,result in [(bounded,'latest_progress',{'progress':None,'unresolved':[]}),
             (bounded,'discover_main_history',self.history),(bounded,'scan_run_sequence',self.scan),
             (bounded,'enumerate_recovery_intents',self.previous),(planner,'plan_recovery',self.plan)]:
            p=patch.object(module,name,return_value=result);self.mocks[name]=p.start();self.addCleanup(p.stop)
    def run_prepare(self):
        return bounded.prepare_bounded(self.api,'owner/repo',self.baseline,program_commit='b'*40,
            recovery_run=10,recovery_attempt=1)
    def old(self,pending=()):
        record={'history':self.history['cursor'],'pending_prs':list(pending),
            'executions':[{'run':8,'attempt':1}], 'run_sequence':{'frontier':8,'partial':None}}
        self.mocks['latest_progress'].return_value={'progress':{'record':record,'artifact':{'id':42}},'unresolved':[]}
        return record
    def pr(self,n):
        return {'number':n,'base':{'repo':{'full_name':'owner/repo'}},'merge_commit_sha':'e'*40}
    def test_quiet_wake_has_small_bound_and_retains_own_executor(self):
        r=self.run_prepare();self.assertEqual(len(self.api.calls),5)
        self.assertEqual(r['progress']['executions'],[{'run':10,'attempt':1}])
        self.assertEqual(r['progress']['run_sequence']['frontier'],9)
        self.assertFalse(r['progress']['dispatch_authorized'])
    def test_uses_only_retained_and_new_recovery_executions(self):
        self.old();self.scan['runs']=[{'id':9,'event':'schedule','head_branch':'main'},
          {'id':11,'event':'pull_request_target','head_branch':'topic'}]
        self.run_prepare()
        self.assertEqual(self.mocks['enumerate_recovery_intents'].call_args.kwargs['run_ids'],[8,9])
    def test_incomplete_sequence_cannot_authorize_any_plan(self):
        self.scan.update(enumeration_complete=False,partial={'frontier':4,'target':9,'next_page':2,'records':[]})
        r=self.run_prepare()
        args=self.mocks['plan_recovery'].call_args.kwargs
        self.assertTrue(args['previous']['unlocated_effects']);self.assertFalse(r['discovery']['run_sequence_complete'])
    def test_partial_older_window_blocks_until_current_sequence_accounted(self):
        old=self.old();old['run_sequence']['partial']={'frontier':8,'target':8,'next_page':2,'records':[]}
        r=self.run_prepare();self.assertFalse(r['discovery']['run_sequence_complete'])
        self.assertEqual(r['progress']['run_sequence']['frontier'],8)
    def test_new_and_old_pending_items_survive_bounded_selection(self):
        self.old([2,3]);self.history['candidates']=[self.pr(4)]
        for n in (2,3,4):self.api.records['pulls/'+str(n)]=self.pr(n)
        r=self.run_prepare();self.assertEqual(r['progress']['pending_prs'],[4,2,3])
        self.assertEqual([c['number'] for c in self.mocks['plan_recovery'].call_args.kwargs['queue']['candidates']],[2,3])
    def test_old_unresolved_work_rotates_so_new_items_are_not_starved(self):
        self.old([2,3,4]);
        for n in (2,3,4):self.api.records['pulls/'+str(n)]=self.pr(n)
        first=self.run_prepare()
        self.mocks['latest_progress'].return_value={'progress':{'record':first['progress'],'artifact':{'id':42}},'unresolved':[]}
        self.run_prepare()
        selected=self.mocks['plan_recovery'].call_args.kwargs['queue']['candidates']
        self.assertEqual([x['number'] for x in selected],[4,2])
    def test_only_two_passed_workflows_retire_pending_item(self):
        self.old([2]);self.api.records['pulls/2']=self.pr(2)
        self.plan['observations']=[{'operation':{'number':2},'existing':{'state':'verification_passed'}} for _ in range(2)]
        self.assertFalse(self.run_prepare()['progress']['pending_prs'])
    def test_failed_or_exact_missing_release_is_not_retired(self):
        self.old([2]);self.api.records['pulls/2']=self.pr(2)
        for state in ('existing_runs_need_attention','missing_exact_release_run'):
            self.plan['observations']=[{'operation':{'number':2},'existing':{'state':state}} for _ in range(2)]
            self.assertEqual(self.run_prepare()['progress']['pending_prs'],[2])
    def test_unlocated_executor_survives_even_without_readable_pr(self):
        self.previous['unresolved']=[{'run':8,'reason':'lost artifact'}]
        r=self.run_prepare();self.assertIn({'run':8,'attempt':1},r['progress']['executions'])
    def test_execution_backlog_stops_new_discovery_and_is_processed_in_batches(self):
        old=self.old();old['executions']=[{'run':rid,'attempt':1} for rid in range(100,150)]
        r=self.run_prepare()
        self.mocks['scan_run_sequence'].assert_not_called()
        self.assertEqual(self.mocks['enumerate_recovery_intents'].call_args.kwargs['run_ids'],list(range(100,108)))
        self.assertEqual([e['run'] for e in r['progress']['executions']],list(range(108,150))+[10])
        self.assertFalse(r['discovery']['run_sequence_complete'])
        self.assertTrue(self.mocks['plan_recovery'].call_args.kwargs['previous']['unlocated_effects'])

    def test_unresolved_executors_rotate_behind_unexamined_work(self):
        old=self.old();old['executions']=[{'run':rid,'attempt':1} for rid in range(100,110)]
        self.previous['unresolved']=[{'run':rid,'reason':'unknown original effect'} for rid in range(100,108)]
        r=self.run_prepare()
        self.assertEqual([e['run'] for e in r['progress']['executions']],list(range(108,110))+list(range(100,108))+[10])

    def test_pr_backlog_pauses_history_walk_without_losing_cursor_or_pending_items(self):
        old=self.old(list(range(100,145)))
        r=self.run_prepare()
        self.mocks['discover_main_history'].assert_not_called()
        self.assertEqual(r['progress']['history'],old['history'])
        self.assertEqual(set(r['progress']['pending_prs']),set(old['pending_prs']))
        self.assertFalse(r['discovery']['history_complete'])

    def test_large_inert_history_drains_without_rediscovery_or_unbounded_queue(self):
        from urllib.parse import parse_qs,urlparse
        from run_sequence import scan_run_sequence
        self.api.records['actions/runs/10']['run_number']=1600
        raw_json=self.api.json
        rows=[{'id':10000+n,'workflow_id':99,'run_number':n,'event':'workflow_run',
               'head_branch':'main','created_at':'2026-11-17T00:00:00Z'} for n in range(1599,4,-1)]
        def json_page(path):
            if path.startswith('actions/workflows/99/runs?'):
                self.api.calls.append(path)
                page=int(parse_qs(urlparse(path).query)['page'][0])
                return {'total_count':len(rows),'workflow_runs':copy.deepcopy(rows[(page-1)*100:page*100])}
            return raw_json(path)
        self.api.json=json_page
        self.mocks['scan_run_sequence'].side_effect=scan_run_sequence
        seen=set();peak=0
        for _ in range(250):
            result=self.run_prepare()
            selected=self.mocks['enumerate_recovery_intents'].call_args.kwargs['run_ids']
            self.assertLessEqual(len(selected),8)
            self.assertFalse(seen&set(selected),'proved-inert execution was enqueued again')
            seen.update(selected)
            progress=result['progress'];peak=max(peak,len(progress['executions']))
            self.assertLessEqual(result['discovery']['reads'],60)
            if result['discovery']['run_sequence_complete'] and progress['executions']==[{'run':10,'attempt':1}]:
                break
            self.mocks['latest_progress'].return_value={'progress':{'record':progress,'artifact':{'id':42}},'unresolved':[]}
        else:self.fail('bounded discovery did not drain its inert backlog')
        self.assertEqual(seen,{row['id'] for row in rows})
        self.assertLessEqual(peak,341)

    def test_wrong_current_execution_or_sequence_anchor_stops(self):
        for path,key,value in [('actions/runs/10','run_attempt',2),('actions/runs/5','run_number',3),
            ('actions/runs/5','id',999),('actions/runs/10','path','.github/workflows/other.yml'),
            ('actions/runs/10','repository',{'id':8,'full_name':'elsewhere/repo'}),
            ('actions/runs/10','head_repository',{'id':8})]:
            old=self.api.records[path][key];self.api.records[path][key]=value
            with self.assertRaises(ValueError):self.run_prepare()
            self.api.records[path][key]=old


    def original_not_sent(self,attempt=1):
        from dispatch_intents import operation_key
        op={'repository':'owner/repo','number':2,'head':'d'*40,'merge':'e'*40,
            'workflow':'kernel-lean.yml','ref':'main'}
        key=operation_key(op)
        intent={'schema':'main-check-intent/v1','operation':op,'operation_key':key,
                'request':{'ref':'main','return_run_details':True},'recovery_run':8,'recovery_attempt':attempt}
        receipt={'schema':'main-check-receipt/v1','operation_key':key,'status':'not_sent',
                 'request_sent':False,'recovery_run':8,'recovery_attempt':attempt}
        return {'publisher':{'id':8,'run_attempt':attempt},'executor_terminal':True,
                'job':{'run_id':8,'run_attempt':attempt,'status':'completed',
                    'steps':[{'name':'Dispatch','status':'completed','conclusion':'success'}]},
                'dispatch_step':'Dispatch','results_persisted_after_dispatch':True,
                'operations':{key:{'intent':intent,'receipt':receipt}}}

    def test_known_unsent_executor_retires_but_pending_pr_is_preserved(self):
        self.old([2]);self.api.records['pulls/2']=self.pr(2)
        self.previous['executions']=[self.original_not_sent()]
        r=self.run_prepare()
        self.assertEqual(r['progress']['pending_prs'],[2])
        self.assertEqual(r['progress']['executions'],[{'run':10,'attempt':1}])

    def test_inert_attempt_cannot_erase_an_unlocated_attempt(self):
        self.old([2]);self.api.records['pulls/2']=self.pr(2)
        self.previous['executions']=[self.original_not_sent()]
        self.previous['unresolved']=[{'run':8,'attempt':2,'reason':'missing original receipt'}]
        r=self.run_prepare()
        self.assertIn({'run':8,'attempt':1},r['progress']['executions'])
        self.assertFalse(r['discovery']['run_sequence_complete'])

    def test_inert_attempt_cannot_erase_another_recovered_uncertain_attempt(self):
        self.old([2]);self.api.records['pulls/2']=self.pr(2)
        inert=self.original_not_sent();unknown=self.original_not_sent(attempt=2)
        next(iter(unknown['operations'].values()))['receipt']=None
        for executions in ([inert,unknown],[unknown,inert]):
            self.previous['executions']=executions
            self.assertIn({'run':8,'attempt':1},self.run_prepare()['progress']['executions'])


    def test_existing_search_progress_retained_for_pending_pr_only(self):
        old=self.old([2,3])
        cursors={'keep':{'operation':{'number':2}},'retire':{'operation':{'number':3}}}
        old['existing_searches']=copy.deepcopy(cursors)
        self.plan['existing_searches']=copy.deepcopy(cursors)
        for n in (2,3):self.api.records['pulls/'+str(n)]=self.pr(n)
        self.plan['observations']=[{'operation':{'number':3},'existing':{'state':'verification_passed'}} for _ in range(2)]
        result=self.run_prepare()
        self.assertEqual(self.mocks['plan_recovery'].call_args.kwargs['searches'],cursors)
        self.assertEqual(result['progress']['existing_searches'],{'keep':cursors['keep']})
        self.assertEqual(result['progress']['pending_prs'],[2])

class Budget(unittest.TestCase):
    def test_cache_and_limit_preserve_read_bound(self):
        raw=API();api=BoundedReads(raw,2)
        api.json('');api.json('');api.json('actions/runs/5')
        self.assertEqual(len(raw.calls),2)
        with self.assertRaises(ReadBudgetExceeded):api.json('actions/runs/10')
        self.assertEqual(len(raw.calls),2)
    def test_fresh_clears_values_but_not_budget(self):
        raw=API();api=BoundedReads(raw,2);api.json('');raw.records['']['id']=8
        self.assertEqual(api.json('')['id'],7);api.fresh();self.assertEqual(api.json('')['id'],8)
        self.assertEqual(api.remaining,0)


if __name__=='__main__':unittest.main()

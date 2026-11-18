import copy,hashlib,io,json,unittest,zipfile
import test_discover_intents as fixtures
from progress_record import NAME,PREPARE,UPLOAD,read_progress,latest_progress,baseline_digest,checkpoint_name
from discover_intents import DISPATCH


class Progress(unittest.TestCase):
    def setUp(self):
        self.f=fixtures.RecoveryIntents();self.f.setUp();f=self.f
        self.baseline={'schema':'main-check-baseline/v1','repository':f.repo,'activation_commit':f.activation,
                       'activated_at':'2026-11-17T00:00:00.012345+00:00','workflow_run_number':4,'workflow_run_id':5}
        f.publisher.update(run_number=10,workflow_id=99,created_at='2026-11-17T00:59:00Z')
        f.job.update(started_at='2026-11-17T01:00:00Z',completed_at='2026-11-17T01:00:03Z')
        f.job['steps']=[{'number':2,'name':PREPARE,'status':'completed','conclusion':'success'},
                       {'number':3,'name':UPLOAD,'status':'completed','conclusion':'success'},
                       {'number':5,'name':DISPATCH,'status':'completed','conclusion':'failure'}]
        self.record={'schema':'main-check-progress/v1','repository':f.repo,'repository_id':12,
          'recovery_run':10,'recovery_attempt':1,'program_commit':f.program,
          'baseline_sha256':baseline_digest(self.baseline),'dispatch_authorized':False,'run_anchor':{'run':10,'number':10},
          'history':{'schema':'main-check-history/v1','repository':f.repo,'activation_commit':f.activation,
                     'frontier':f.program,'scan_head':None,'next_commit':None},
          'pending_prs':[161],'executions':[{'run':10,'attempt':1},{'run':9,'attempt':1}],
          'run_sequence':{'frontier':9,'partial':None}}
        self.pack()
    def pack(self,entries=None):
        buf=io.BytesIO()
        with zipfile.ZipFile(buf,'w',zipfile.ZIP_DEFLATED) as z:
            for name,body in entries or [('progress.json',json.dumps(self.record))]:z.writestr(name,body)
        raw=buf.getvalue();f=self.f
        self.artifact={'id':42,'name':checkpoint_name(f.job['started_at']),'expired':False,'size_in_bytes':len(raw),
          'created_at':'2026-11-17T01:00:01Z','digest':'sha256:'+hashlib.sha256(raw).hexdigest(),
          'workflow_run':{'id':10,'repository_id':12,'head_sha':f.program}}
        f.records['actions/artifacts/42']=self.artifact
        f.blobs['actions/artifacts/42/zip']=raw
    def read(self):
        value=read_progress(self.f.api,self.f.repo,42,self.baseline,self.f.main)
        self.assertFalse(value['dispatch_authorized']);return value
    def test_authenticated_progress_retains_pending_prs_and_own_uncertain_effect(self):
        value=self.read();self.assertEqual(value['record']['pending_prs'],[161])
        self.assertIn({'run':10,'attempt':1},value['record']['executions'])
        self.assertTrue(all(method in ('GET','GET_BYTES') for method,_ in self.f.api.calls))
    def test_failed_dispatch_does_not_make_checkpoint_a_claim_of_success(self):
        self.assertEqual(self.f.job['steps'][-1]['conclusion'],'failure')
        self.assertFalse(self.read()['record']['dispatch_authorized'])
    def test_omitted_own_executor_is_refused(self):
        self.record['executions']=[{'run':9,'attempt':1}];self.pack()
        with self.assertRaisesRegex(ValueError,'own unfinished'):self.read()
    def test_active_original_executor_cannot_supply_progress(self):
        self.f.job['status']='in_progress'
        with self.assertRaisesRegex(ValueError,'not terminal'):self.read()
    def test_terminal_recovery_job_can_supply_progress_while_other_jobs_run(self):
        self.f.publisher['status']='in_progress'
        self.assertEqual(self.read()['job']['status'],'completed')
    def test_wrong_day_or_upload_outside_original_job_is_refused(self):
        self.artifact['name']=NAME+'-20261116'
        with self.assertRaisesRegex(ValueError,'job-date bucket'):self.read()
        self.artifact['name']=NAME+'-20261117';self.artifact['created_at']='2026-11-17T00:59:00Z'
        with self.assertRaisesRegex(ValueError,'outside original job'):self.read()
    def test_later_run_number_in_earlier_execution_is_preserved(self):
        self.record['run_anchor']={'run':11,'number':11}
        self.record['run_sequence']['frontier']=10
        self.f.records['actions/runs/11']=dict(self.f.publisher,id=11,run_number=11)
        self.pack()
        self.assertEqual(self.read()['record']['run_sequence']['frontier'],10)
    def test_forged_or_future_workflow_anchor_is_refused(self):
        self.record['run_anchor']={'run':11,'number':11};self.pack()
        for mutation in ({'run_number':12},{'workflow_id':101},{'created_at':'2026-11-18T01:00:00Z'}):
            self.f.records['actions/runs/11']=dict(self.f.publisher,id=11,run_number=11)
            self.f.records['actions/runs/11'].update(mutation)
            with self.subTest(mutation=mutation),self.assertRaisesRegex(ValueError,'anchor binding'):self.read()
    def test_original_attempt_is_read_after_rerun(self):
        self.f.records['actions/runs/10/attempts/1']=copy.deepcopy(self.f.publisher)
        self.f.publisher['run_attempt']=2
        self.assertEqual(self.read()['publisher']['run_attempt'],1)
    def test_rerun_progress_cannot_impersonate_original_attempt(self):
        self.record['recovery_attempt']=2;self.pack()
        with self.assertRaisesRegex(ValueError,'execution binding'):self.read()
    def test_fork_wrong_branch_trigger_or_program_rejected(self):
        original=copy.deepcopy(self.f.publisher)
        for key,value in [('head_repository',{'id':999}),('head_branch','candidate'),
                          ('event','issue_comment'),('path','.github/workflows/evil.yml')]:
            self.f.publisher.clear();self.f.publisher.update(copy.deepcopy(original));self.f.publisher[key]=value
            with self.assertRaises(ValueError):self.read()
    def test_modified_archive_cannot_skip_history(self):
        self.artifact['digest']='sha256:'+'0'*64
        with self.assertRaisesRegex(ValueError,'digest'):self.read()
    def test_expired_progress_is_not_empty_progress(self):
        self.artifact['expired']=True
        with self.assertRaisesRegex(ValueError,'expiry'):self.read()
    def test_foreign_artifact_identity_is_refused(self):
        self.artifact['workflow_run']['head_sha']='f'*40
        with self.assertRaisesRegex(ValueError,'source binding'):self.read()
    def test_non_main_program_ancestry_rejected(self):
        self.f.records[f'compare/{self.f.program}...{self.f.main}']['behind_by']=1
        with self.assertRaisesRegex(ValueError,'ancestry'):self.read()
    def test_missing_failed_duplicate_or_late_progress_upload_refused(self):
        original=copy.deepcopy(self.f.job['steps'])
        for mutation in ('missing','failure','duplicate','late'):
            steps=copy.deepcopy(original)
            if mutation=='missing':steps.pop(1)
            if mutation=='failure':steps[1]['conclusion']='failure'
            if mutation=='duplicate':steps.append(copy.deepcopy(steps[1]))
            if mutation=='late':steps[1]['number']=6
            self.f.job['steps']=steps
            with self.assertRaises(ValueError):self.read()
    def test_archive_members_do_not_write_any_file(self):
        self.pack(entries=[('../progress.json',json.dumps(self.record))])
        with self.assertRaisesRegex(ValueError,'archive members'):self.read()
    def test_changed_baseline_never_reuses_old_frontier(self):
        self.baseline['activated_at']='2026-11-17T00:00:01Z'
        with self.assertRaisesRegex(ValueError,'baseline'):self.read()
    def test_pending_ids_are_positive_unique_and_not_boolean(self):
        for value in ([True],[0],[161,161],['161']):
            self.record['pending_prs']=value;self.pack()
            with self.assertRaisesRegex(ValueError,'pending PR'):self.read()
    def test_future_run_frontier_cannot_drop_unseen_runs(self):
        self.record['run_sequence']['frontier']=10;self.pack()
        with self.assertRaisesRegex(ValueError,'run-number frontier'):self.read()
    def test_partial_sequence_retained_and_foreign_frontier_rejected(self):
        partial={'frontier':9,'target':9,'next_page':2,'records':[]}
        self.record['run_sequence']['partial']=partial;self.pack()
        self.assertEqual(self.read()['record']['run_sequence']['partial'],partial)
        partial['frontier']=8;self.pack()
        with self.assertRaisesRegex(ValueError,'partial run-number'):self.read()
    def search_record(self):
        from existing_search import search_existing
        from dispatch_intents import operation_key
        from test_existing_search import API, OP, START, row, printed
        operation=dict(OP,repository=self.f.repo,number=161)
        api=API([row(i,event='schedule') for i in range(1000)])
        search=search_existing(api,operation,printed(START),'b'*40,False,now=START+999)['search']
        key=operation_key(operation)
        self.record['existing_searches']={key:search}
        return key,search
    def test_authenticated_progress_preserves_unvisited_run_windows(self):
        key,search=self.search_record();self.pack()
        loaded=self.read()['record']['existing_searches'][key]
        self.assertEqual(loaded,search)
        self.assertTrue(loaded['pending_windows'])
        self.assertFalse(loaded['identities'])
    def test_progress_rejects_foreign_or_unqueued_existing_search(self):
        from dispatch_intents import operation_key
        for mutation in ('foreign','unqueued','wrong_key'):
            key,search=self.search_record()
            if mutation=='foreign':search['operation']['repository']='outsider/fork'
            if mutation=='unqueued':search['operation']['number']=162
            actual=operation_key(search['operation'])
            search['operation_key']=actual
            self.record['existing_searches']={('f'*64 if mutation=='wrong_key' else actual):search}
            self.pack()
            with self.subTest(mutation=mutation),self.assertRaisesRegex(ValueError,'search ownership'):
                self.read()
    def test_progress_rejects_embedded_mutable_run_outcome(self):
        from existing_search import search_existing
        from dispatch_intents import operation_key
        from test_existing_search import API, OP, START, row, printed
        operation=dict(OP,repository=self.f.repo,number=161)
        run=row(0)
        for field in ('repository','head_repository'):run[field]['full_name']=self.f.repo
        search=search_existing(API([run]),operation,printed(START),'b'*40,False,now=START+1)['search']
        search['identities'][0]['conclusion']='success'
        self.record['existing_searches']={operation_key(operation):search};self.pack()
        with self.assertRaisesRegex(ValueError,'search record'):self.read()

if __name__=='__main__':unittest.main()

"""Compose real preparation, artifact authentication and dispatch offline.

All GitHub responses and ZIPs are fixtures. No network or real workflow write
is possible; the API records simulated POSTs for assertion only.
"""
import copy,hashlib,io,json,unittest,zipfile
import test_dispatch_read_budget as fixtures
from bounded_recovery import prepare_bounded
from discover_intents import JOB,DISPATCH,UPLOAD as INTENT_UPLOAD,RESULTS_UPLOAD
from progress_record import NAME,PREPARE,UPLOAD as PROGRESS_UPLOAD


class Preparation(unittest.TestCase):
    def setUp(self):
        self.f=fixtures.ReadHeadroom();self.f.setUp()
        self.api=self.f.api;self.records=self.f.records;self.blobs=self.f.blobs
        self.baseline=dict(self.f.baseline,workflow_run_id=499,workflow_run_number=499)
        self.records['actions/runs/499']={'id':499,'workflow_id':900,'run_number':499,
            'repository':{'id':7,'full_name':self.f.repo}}
        self.records['actions/runs/500']['run_number']=500
        self.job=self.records['actions/runs/500/attempts/1/jobs?per_page=100&page=1']['jobs'][0]
        self.job.update(started_at='2026-11-17T13:01:00Z',completed_at=None)
        self.job['steps']=[{'number':1,'name':PREPARE,'status':'in_progress','conclusion':None},
            {'number':2,'name':PROGRESS_UPLOAD,'status':'pending','conclusion':None},
            {'number':3,'name':INTENT_UPLOAD,'status':'pending','conclusion':None},
            {'number':4,'name':DISPATCH,'status':'pending','conclusion':None},
            {'number':5,'name':RESULTS_UPLOAD,'status':'pending','conclusion':None}]
        self.bucket='actions/artifacts?name='+NAME+'-20261117&per_page=100&page=1'
        self.records[self.bucket]={'total_count':0,'artifacts':[]}
        self.records['git/commits/'+'e'*40]['parents']=[{'sha':'d'*40}]
        self.records['commits/'+'b'*40+'/pulls?per_page=100&page=1']=[{'id':7,'number':7}]
        self.records['commits/'+'e'*40+'/pulls?per_page=100&page=1']=[]
        self.records['compare/'+'d'*40+'...'+'d'*40]={
            'base_commit':{'sha':'d'*40},'merge_base_commit':{'sha':'d'*40},'behind_by':0,'status':'identical'}
        self.records['actions/runs/500/artifacts?per_page=100&page=1']={'total_count':0,'artifacts':[]}
        self.counts=[]
    def prepare(self,rid=500):
        before=len(self.api.reads)
        result=prepare_bounded(self.api,self.f.repo,self.baseline,program_commit=self.f.program,
                               recovery_run=rid,recovery_attempt=1)
        self.counts.append(len(self.api.reads)-before)
        self.assertLessEqual(self.counts[-1],60)
        return result
    def pack(self,rid,kind,value,*,name=None):
        listing=self.records[f'actions/runs/{rid}/artifacts?per_page=100&page=1']
        aid=rid*100+len(listing['artifacts'])
        buf=io.BytesIO()
        with zipfile.ZipFile(buf,'w',zipfile.ZIP_DEFLATED) as archive:
            archive.writestr(kind+'.json',json.dumps(value))
        raw=buf.getvalue()
        meta={'id':aid,'name':name or f'protocol-b-main-{kind}-{rid}-1','expired':False,
            'created_at':'2026-11-17T13:02:00Z','size_in_bytes':len(raw),
            'digest':'sha256:'+hashlib.sha256(raw).hexdigest(),
            'workflow_run':{'id':rid,'repository_id':7,'head_sha':self.f.program}}
        self.blobs[f'actions/artifacts/{aid}/zip']=raw;self.records[f'actions/artifacts/{aid}']=meta
        listing['artifacts'].append(meta);listing['total_count']=len(listing['artifacts'])
        return meta
    def upload_plan(self,plan):
        progress=self.pack(500,'progress',plan['progress'],name=plan['progress_artifact_name'])
        self.records[self.bucket]={'total_count':1,'artifacts':[progress]}
        if plan['operations']:self.pack(500,'intents',plan)
        for step in self.job['steps'][:3]:step.update(status='completed',conclusion='success')
        self.job['steps'][3].update(status='in_progress',conclusion=None)
    def finish_original(self,*,unknown):
        self.records['actions/runs/500']['status']='completed'
        self.job.update(status='completed',completed_at='2026-11-17T13:03:00Z')
        self.job['steps'][3].update(status='completed',conclusion='failure' if unknown else 'success')
        self.job['steps'][4].update(status='completed',conclusion='failure' if unknown else 'success')
        self.records['actions/runs/501']=dict(self.records['actions/runs/500'],id=501,
            run_number=501,status='in_progress',created_at='2026-11-17T13:04:00Z')
        newjob=copy.deepcopy(self.job);newjob.update(id=2501,run_id=501,status='in_progress',
            started_at='2026-11-17T13:05:00Z',completed_at=None)
        self.records['actions/runs/501/attempts/1/jobs?per_page=100&page=1']={'total_count':1,'jobs':[newjob]}
        self.records['actions/workflows/900/runs?per_page=100&page=1']={
            'workflow_runs':[self.records['actions/runs/501'],self.records['actions/runs/500']]}
    def test_first_preparation_plans_both_workflows_within_read_cap(self):
        plan=self.prepare()
        self.assertEqual(len(plan['operations']),2,plan)
        self.assertEqual(plan['progress']['pending_prs'],[7])
        self.assertEqual(plan['progress_artifact_name'],NAME+'-20261117')
        self.assertFalse(self.api.posts)
    def test_preparation_upload_and_dispatch_are_composed_without_planner_mocks(self):
        plan=self.prepare();self.upload_plan(plan)
        self.assertFalse(self.api.posts)
        before=len(self.api.reads);result=self.f.run_dispatch()
        self.assertEqual(len(self.api.posts),2,result)
        self.assertTrue(all(r['status']=='run_confirmed' for r in result['receipts']),result)
        self.assertLessEqual(len(self.api.reads)-before,60)
    def test_next_wake_can_retire_authenticated_unsent_executor(self):
        plan=self.prepare();self.upload_plan(plan);self.finish_original(unknown=False)
        self.pack(500,'results',{'schema':'main-check-results/v1','repository_id':7,
            'recovery_run':500,'recovery_attempt':1,'program_commit':self.f.program,
            'receipts':[{'schema':'main-check-receipt/v1','operation_key':op['operation_key'],
                'recovery_run':500,'recovery_attempt':1,'status':'not_sent','request_sent':False}
                for op in plan['operations']]})
        resumed=self.prepare(501)
        self.assertGreaterEqual(len(resumed['operations']),1,resumed)
        self.assertNotIn({'run':500,'attempt':1},resumed['progress']['executions'])
        self.assertEqual(resumed['progress']['pending_prs'],[7])
        self.assertFalse(self.api.posts)
    def test_next_wake_authenticates_progress_and_keeps_unknown_effect(self):
        plan=self.prepare();self.upload_plan(plan);self.finish_original(unknown=True)
        resumed=self.prepare(501)
        self.assertFalse(resumed['operations'],resumed)
        self.assertIn({'run':500,'attempt':1},resumed['progress']['executions'])
        self.assertEqual(resumed['progress']['pending_prs'],[7])
        self.assertTrue(all(o.get('blocked')=='prior_dispatch_not_proved_absent'
                            for o in resumed['observations']),resumed)
        self.assertFalse(self.api.posts)


if __name__=='__main__':unittest.main()

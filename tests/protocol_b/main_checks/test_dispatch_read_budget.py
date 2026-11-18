"""Exercise the real discovery/revalidation/dispatch code with an offline API.

No network transport is available. Archive bytes are fixtures, never original
review evidence. These tests measure composed read counts, not provider costs.
"""
import copy,hashlib,io,json,unittest,zipfile
from urllib.parse import urlparse,parse_qs
from dispatch_recovery import dispatch_recovery
from dispatch_intents import operation_key
from discover_intents import JOB,UPLOAD,DISPATCH,RESULTS_UPLOAD
import test_discover_deferred as source_fixtures


class OfflineAPI:
    def __init__(self,records,blobs):
        self.records=records;self.blobs=blobs;self.reads=[];self.posts=[];self.empty_windows=True
    def json(self,path):
        self.reads.append(('json',path))
        if path.startswith(('actions/workflows/800/runs?','actions/workflows/801/runs?')):
            return {'total_count':0,'workflow_runs':[]}
        return copy.deepcopy(self.records[path])
    def bytes(self,path):self.reads.append(('bytes',path));return self.blobs[path]
    def post_once(self,path,body):
        self.posts.append((path,copy.deepcopy(body),len(self.reads)))
        rid=1000+len(self.posts)
        self.records['actions/runs/'+str(rid)]={'id':rid,'event':'workflow_dispatch','head_branch':'main',
          'path':'.github/workflows/'+path.split('/')[2],'head_sha':'b'*40,
          'repository':{'full_name':'owner/repo'},'head_repository':{'full_name':'owner/repo'}}
        return {'workflow_run_id':rid}


class ReadHeadroom(unittest.TestCase):
    def setUp(self):
        fixture=source_fixtures.Discovery();fixture.setUp()
        self.records=fixture.records;self.blobs=fixture.binaries
        self.repo='owner/repo';self.program='b'*40;self.baseline={
          'schema':'main-check-baseline/v1','repository':self.repo,'activation_commit':'d'*40,
          'activated_at':'2026-11-17T00:00:00Z'}
        self.records['git/ref/heads/main']={'ref':'refs/heads/main','object':{'type':'commit','sha':self.program}}
        self.records['actions/workflows/protocol-b.yml']={'id':900,'path':'.github/workflows/protocol-b.yml'}
        for workflow,wid in [('research-checks.yml',800),('kernel-lean.yml',801)]:
            self.records['actions/workflows/'+workflow]={'id':wid,'path':'.github/workflows/'+workflow}
        for old,new in [('d'*40,self.program),(self.program,self.program)]:
            self.records['compare/'+old+'...'+new]={'base_commit':{'sha':old},'merge_base_commit':{'sha':old},
                'behind_by':0,'status':'identical' if old==new else 'ahead'}
        # A complete immutable tree proves that the release manifest is unchanged.
        self.records['git/commits/'+'b'*40]={'sha':'b'*40,'parents':[{'sha':'e'*40}], 'tree':{'sha':'f'*40}}
        self.records['git/commits/'+'e'*40]={'sha':'e'*40,'tree':{'sha':'1'*40}}
        for tree,docs in [('f'*40,'2'*40),('1'*40,'3'*40)]:
            self.records['git/trees/'+tree]={'sha':tree,'truncated':False,'tree':[{'path':'docs','mode':'040000','type':'tree','sha':docs}]}
            self.records['git/trees/'+docs]={'sha':docs,'truncated':False,'tree':[{'path':'current-manuscript.json','mode':'100644','type':'blob','sha':'4'*40}]}
        self.api=OfflineAPI(self.records,self.blobs);self.saved=[];self.prior=[]
        self.execution(500,active=True)

    def execution(self,rid,*,active):
        publisher={'id':rid,'workflow_id':900,'run_attempt':1,'head_sha':self.program,
          'repository':{'id':7,'full_name':self.repo},'head_repository':{'id':7},
          'path':'.github/workflows/protocol-b.yml','head_branch':'main','event':'schedule',
          'created_at':'2026-11-17T13:00:00Z','status':'in_progress' if active else 'completed'}
        job={'id':rid+2000,'run_id':rid,'run_attempt':1,'name':JOB,'status':publisher['status'],
             'steps':[{'number':1,'name':UPLOAD,'status':'completed','conclusion':'success'},
                      {'number':2,'name':DISPATCH,'status':'in_progress' if active else 'completed','conclusion':None if active else 'success'},
                      {'number':3,'name':RESULTS_UPLOAD,'status':'pending' if active else 'completed','conclusion':None if active else 'success'}]}
        self.records['actions/runs/'+str(rid)]=publisher
        self.records[f'actions/runs/{rid}/attempts/1/jobs?per_page=100&page=1']={'total_count':1,'jobs':[job]}
        operations=[]
        for workflow in ('research-checks.yml','kernel-lean.yml'):
            op={'repository':self.repo,'number':7,'head':'a'*40,'merge':'b'*40,'workflow':workflow,'ref':'main'}
            operations.append({'schema':'main-check-intent/v1','operation':op,'operation_key':operation_key(op),
             'request':{'ref':'main','return_run_details':True},'recovery_run':rid,'recovery_attempt':1,
             'source':{'accepted_check':10,'accepted_run':124,'requester_run':123},'exact_release':False})
        plan={'schema':'main-check-intents/v1','repository':self.repo,'repository_id':7,'recovery_run':rid,
          'recovery_attempt':1,'program_commit':self.program,'operations':operations,
          'discovery':{'run_sequence_complete':True,'retained_executions':self.prior+[rid]}}
        artifacts=[]
        def pack(kind,value):
            archive=io.BytesIO()
            with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:z.writestr(kind+'.json',json.dumps(value))
            raw=archive.getvalue();aid=rid*10+len(artifacts)
            self.blobs[f'actions/artifacts/{aid}/zip']=raw
            artifacts.append({'id':aid,'name':f'protocol-b-main-{kind}-{rid}-1','expired':False,'size_in_bytes':len(raw),
              'digest':'sha256:'+hashlib.sha256(raw).hexdigest(),'workflow_run':{'id':rid,'repository_id':7,'head_sha':self.program}})
        pack('intents',plan)
        if not active:
            receipts=[{'schema':'main-check-receipt/v1','operation_key':o['operation_key'],'recovery_run':rid,
                       'recovery_attempt':1,'status':'not_sent','request_sent':False} for o in operations]
            pack('results',{'schema':'main-check-results/v1','repository_id':7,'recovery_run':rid,
                            'recovery_attempt':1,'program_commit':self.program,'receipts':receipts})
        self.records[f'actions/runs/{rid}/artifacts?per_page=100&page=1']={'total_count':len(artifacts),'artifacts':artifacts}

    def run_dispatch(self):
        return dispatch_recovery(self.api,self.repo,self.baseline,program_commit=self.program,
             recovery_run=500,recovery_attempt=1,persist=lambda v:self.saved.append(copy.deepcopy(v)))

    def test_real_discovery_and_two_workflows_fit_the_read_cap(self):
        result=self.run_dispatch()
        self.assertEqual(len(self.api.posts),2,result)
        self.assertEqual([r['status'] for r in result['receipts']],['run_confirmed','run_confirmed'])
        self.assertLessEqual(len(self.api.reads),60)
        self.assertTrue(all(p[1]=={'ref':'main','return_run_details':True} for p in self.api.posts))

    def test_retained_original_intent_does_not_starve_the_first_send(self):
        self.execution(400,active=False);self.prior=[400];self.execution(500,active=True)
        result=self.run_dispatch()
        self.assertGreaterEqual(len(self.api.posts),1,result)
        self.assertLessEqual(len(self.api.reads),60)
        self.assertTrue(all(r['status'] in ('run_confirmed','not_sent') for r in result['receipts']))
        self.assertEqual(result['receipts'][-1]['status'],'not_sent')
        self.assertIn('read budget',result['receipts'][-1]['reason'])

    def test_failed_fresh_revalidation_retains_known_absence_for_every_intent(self):
        for rid in range(400,412):self.execution(rid,active=False)
        self.prior=list(range(400,412));self.execution(500,active=True)
        with self.assertRaisesRegex(ValueError,'unresolved'):
            self.run_dispatch()
        self.assertFalse(self.api.posts)
        self.assertLessEqual(len(self.api.reads),60)
        self.assertEqual(len(self.saved[-1]['receipts']),2)
        self.assertTrue(all(r['status']=='not_sent' and r['request_sent'] is False
                            for r in self.saved[-1]['receipts']))


    def test_new_runs_after_revalidation_block_both_real_dispatch_boundaries(self):
        original_json=self.api.json;window_reads={}
        def changing_json(path):
            if path.startswith(('actions/workflows/800/runs?','actions/workflows/801/runs?')):
                wid=int(path.split('/')[2]);window_reads[wid]=window_reads.get(wid,0)+1
                if window_reads[wid]>=2:
                    self.api.reads.append(('json',path))
                    workflow='research-checks.yml' if wid==800 else 'kernel-lean.yml'
                    created=parse_qs(urlparse(path).query)['created'][0].split('..')[-1]
                    run={'id':wid+5000,'workflow_id':wid,'created_at':created,
                         'status':'in_progress','conclusion':None,'head_sha':'b'*40,'head_branch':'main',
                         'event':'workflow_dispatch','path':'.github/workflows/'+workflow,
                         'repository':{'full_name':self.repo},'head_repository':{'full_name':self.repo}}
                    self.records['actions/runs/'+str(run['id'])]=copy.deepcopy(run)
                    return {'total_count':1,'workflow_runs':[run]}
            return original_json(path)
        self.api.json=changing_json
        result=self.run_dispatch()
        self.assertEqual(window_reads,{800:2,801:2})
        self.assertFalse(self.api.posts)
        self.assertTrue(all(r['status']=='not_sent' and r['request_sent'] is False for r in result['receipts']))
        self.assertEqual([r['existing']['state'] for r in result['receipts']],['existing_run_in_progress']*2)
        self.assertTrue(all('actual main checks already exist' in r['reason'] for r in result['receipts']))
        self.assertLessEqual(len(self.api.reads),60)

if __name__=='__main__':unittest.main()

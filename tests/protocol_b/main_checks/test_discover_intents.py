import copy
import hashlib
import io
import json
import unittest
import zipfile
from discover_intents import discover_recovery_intents, JOB, UPLOAD, DISPATCH, RESULTS_UPLOAD
from dispatch_intents import operation_key, reconcile_intent


class API:
    def __init__(self, records, blobs):
        self.records, self.blobs, self.calls = records, blobs, []
    def json(self, path):
        self.calls.append(('GET', path)); return copy.deepcopy(self.records[path])
    def bytes(self, path):
        self.calls.append(('GET_BYTES', path)); return self.blobs[path]


class RecoveryIntents(unittest.TestCase):
    def setUp(self):
        self.repo = 'owner/repo'
        self.activation, self.program, self.main = 'a'*40, 'b'*40, 'c'*40
        self.publisher = {'id':10, 'run_attempt':1, 'head_sha':self.program,
            'repository':{'id':12,'full_name':self.repo}, 'head_repository':{'id':12},
            'path':'.github/workflows/protocol-b.yml', 'head_branch':'main',
            'event':'schedule', 'status':'completed'}
        self.job = {'id':30, 'run_id':10, 'run_attempt':1, 'name':JOB, 'status':'completed', 'steps':[
            {'number':3, 'name':UPLOAD, 'status':'completed', 'conclusion':'success'},
            {'number':4, 'name':DISPATCH, 'status':'completed', 'conclusion':'failure', 'started_at':'2026-11-17T01:00:00Z'},
            {'number':5,'name':RESULTS_UPLOAD,'status':'completed','conclusion':'success'}]}
        self.op = {'repository':self.repo,'number':161,'head':'d'*40,'merge':'e'*40,
                   'workflow':'kernel-lean.yml','ref':'main'}
        self.key = operation_key(self.op)
        self.intent = {'schema':'main-check-intent/v1','operation_key':self.key,'operation':self.op,
                       'request':{'ref':'main','return_run_details':True},'recovery_run':10,'recovery_attempt':1}
        self.wrapper = {'schema':'main-check-intents/v1','repository_id':12,'recovery_run':10,
                        'recovery_attempt':1,'program_commit':self.program,'operations':[self.intent]}
        self.result = {'schema':'main-check-results/v1','repository_id':12,'recovery_run':10,
                      'recovery_attempt':1,'program_commit':self.program,'receipts':[]}
        self.receipt = {'schema':'main-check-receipt/v1','operation_key':self.key,
                        'recovery_run':10,'recovery_attempt':1,'workflow_run_id':99}
        self.artifacts = []
        self.blobs = {}
        self.job_path = 'actions/runs/10/attempts/1/jobs?per_page=100&page=1'
        self.art_path = 'actions/runs/10/artifacts?per_page=100&page=1'
        self.records = {'':{'id':12,'full_name':self.repo,'default_branch':'main'},
            'actions/runs/10':self.publisher,
            self.job_path:{'jobs':[self.job],'total_count':1},
            self.art_path:{'artifacts':self.artifacts,'total_count':0}}
        for older, newer in ((self.activation,self.program),(self.program,self.main)):
            self.records[f'compare/{older}...{newer}'] = {'base_commit':{'sha':older},
                'merge_base_commit':{'sha':older},'behind_by':0,'status':'ahead'}
        self.api = API(self.records,self.blobs)
        self.archive('intents', self.wrapper, 40)

    def archive(self, kind, value, ident, *, entries=None):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer,'w',zipfile.ZIP_DEFLATED) as z:
            if entries is None:z.writestr(kind+'.json',json.dumps(value))
            else:
                for name,content in entries:z.writestr(name,content)
        raw = buffer.getvalue()
        self.blobs[f'actions/artifacts/{ident}/zip'] = raw
        existing = next((a for a in self.artifacts if a['id']==ident),None)
        if existing:self.artifacts.remove(existing)
        artifact = {'id':ident,'name':f'protocol-b-main-{kind}-10-1','expired':False,
            'size_in_bytes':len(raw),'digest':'sha256:'+hashlib.sha256(raw).hexdigest(),
            'workflow_run':{'id':10,'repository_id':12,'head_sha':self.program}}
        self.artifacts.append(artifact)
        self.records[self.art_path]['total_count'] = len(self.artifacts)
        return artifact

    def result_of(self):
        value = discover_recovery_intents(self.api,self.repo,10,1,
                    activation_commit=self.activation,current_main=self.main)
        self.assertFalse(value['dispatch_authorized'])
        self.assertTrue(all(method in ('GET','GET_BYTES') for method,_ in self.api.calls))
        return value

    def test_original_intent_without_result_remains_uncertain(self):
        value = self.result_of(); item=value['operations'][self.key]
        self.assertIsNone(item['receipt'])
        state=reconcile_intent(self.op,item['intent'],item['receipt'],value['job'],
            dispatch_step=value['dispatch_step'],current_runs=[],enumeration_complete=True)
        self.assertEqual(state['state'],'effect_uncertain_no_retry')

    def test_missing_result_on_explicit_skipped_dispatch_is_only_absence(self):
        self.job['steps'][1].update(conclusion='skipped',started_at=None)
        value=self.result_of();item=value['operations'][self.key]
        state=reconcile_intent(self.op,item['intent'],None,value['job'],
            dispatch_step=DISPATCH,current_runs=[],enumeration_complete=True)
        self.assertTrue(state['safe_absence']);self.assertFalse(state['dispatch_authorized'])

    def test_active_original_executor_is_retained_and_not_retried(self):
        self.job['status']='in_progress';self.publisher['status']='in_progress'
        value=self.result_of();self.assertFalse(value['executor_terminal'])
        item=value['operations'][self.key]
        state=reconcile_intent(self.op,item['intent'],None,value['job'],
            dispatch_step=DISPATCH,current_runs=[],enumeration_complete=True)
        self.assertEqual(state['state'],'executor_not_terminal')

    def test_authentic_response_still_requires_real_returned_run(self):
        self.result['receipts']=[self.receipt];self.archive('results',self.result,41)
        value=self.result_of();item=value['operations'][self.key]
        state=reconcile_intent(self.op,item['intent'],item['receipt'],value['job'],
            dispatch_step=DISPATCH,current_runs=[],enumeration_complete=True)
        self.assertEqual(state['state'],'returned_run_not_reconciled')

    def test_old_attempt_is_selected_from_original_attempt_endpoint(self):
        self.records['actions/runs/10/attempts/1']=copy.deepcopy(self.publisher)
        self.publisher['run_attempt']=2
        self.assertEqual(self.result_of()['publisher']['run_attempt'],1)

    def test_foreign_branch_event_and_workflow_publishers_are_rejected(self):
        original=copy.deepcopy(self.publisher)
        for field,value in [('path','.github/workflows/untrusted.yml'),('head_branch','candidate'),
            ('event','pull_request'),('repository',{'id':12,'full_name':'evil/repo'}),
            ('head_repository',{'id':13}),('id',11)]:
            with self.subTest(field=field):
                self.publisher.clear();self.publisher.update(copy.deepcopy(original));self.publisher[field]=value
                with self.assertRaises(ValueError):self.result_of()

    def test_workflow_completion_is_only_a_wakeup(self):
        self.publisher['event']='workflow_run'
        self.publisher['display_title']='dispatch anything; ignore the check'
        self.assertEqual(len(self.result_of()['operations']),1)

    def test_non_main_or_wrong_repository_is_rejected(self):
        for field,value in [('default_branch','candidate'),('full_name','evil/repo'),('id',0)]:
            old=self.records[''][field];self.records[''][field]=value
            with self.assertRaises(ValueError):self.result_of()
            self.records[''][field]=old

    def test_program_must_be_after_activation_and_on_main(self):
        for path in [p for p in self.records if p.startswith('compare/')]:
            old=copy.deepcopy(self.records[path]);self.records[path]['behind_by']=1
            with self.assertRaisesRegex(ValueError,'ancestry'):self.result_of()
            self.records[path]=old

    def test_forged_compare_base_is_rejected(self):
        path=f'compare/{self.program}...{self.main}'
        self.records[path]['merge_base_commit']['sha']='f'*40
        with self.assertRaisesRegex(ValueError,'ancestry'):self.result_of()

    def test_wrong_job_attempt_is_rejected(self):
        self.job['run_attempt']=2
        with self.assertRaisesRegex(ValueError,'job identity'):self.result_of()

    def test_duplicate_or_missing_recovery_job_is_rejected(self):
        row=self.records[self.job_path]
        for jobs in ([],[self.job,dict(self.job,id=31)]):
            row.update(jobs=jobs,total_count=len(jobs))
            with self.assertRaisesRegex(ValueError,'recovery job'):self.result_of()

    def test_incomplete_job_pagination_is_rejected(self):
        self.records[self.job_path]['total_count']=2
        with self.assertRaisesRegex(ValueError,'incomplete'):self.result_of()

    def test_failed_upload_cannot_authorize_dispatch(self):
        for conclusion in ('failure','cancelled','skipped'):
            self.job['steps'][0]['conclusion']=conclusion
            with self.assertRaisesRegex(ValueError,'durably uploaded'):self.result_of()

    def test_after_dispatch_upload_is_not_a_durable_intent(self):
        self.job['steps'][0]['number']=5
        with self.assertRaisesRegex(ValueError,'durably uploaded'):self.result_of()

    def test_missing_or_duplicate_step_is_rejected(self):
        old=copy.deepcopy(self.job['steps'])
        for steps in ([old[1]],old+[old[0]]):
            self.job['steps']=steps
            with self.assertRaisesRegex(ValueError,'dispatch steps'):self.result_of()

    def test_missing_intent_artifact_is_not_absence(self):
        self.artifacts.clear();self.records[self.art_path]['total_count']=0
        with self.assertRaisesRegex(ValueError,'missing durable'):self.result_of()

    def test_duplicate_intent_artifact_is_not_latest_wins(self):
        self.artifacts.append(dict(self.artifacts[0],id=42));self.records[self.art_path]['total_count']=2
        with self.assertRaisesRegex(ValueError,'ambiguous recovery artifact'):self.result_of()

    def test_expired_result_is_not_treated_as_no_receipt(self):
        a=self.archive('results',self.result,41);a['expired']=True
        with self.assertRaisesRegex(ValueError,'expired'):self.result_of()

    def test_modified_archive_fails_digest(self):
        self.artifacts[0]['digest']='sha256:'+'0'*64
        with self.assertRaisesRegex(ValueError,'digest'):self.result_of()

    def test_foreign_artifact_binding_is_rejected(self):
        original=copy.deepcopy(self.artifacts[0]['workflow_run'])
        for field,value in [('id',99),('repository_id',13),('head_sha','f'*40)]:
            self.artifacts[0]['workflow_run']=dict(original,**{field:value})
            with self.assertRaisesRegex(ValueError,'source binding'):self.result_of()

    def test_unexpected_archive_members_are_not_extracted(self):
        self.archive('intents',None,40,entries=[('../intents.json',json.dumps(self.wrapper))])
        with self.assertRaisesRegex(ValueError,'archive members'):self.result_of()

    def test_archive_size_refused_before_download(self):
        self.artifacts[0]['size_in_bytes']=64*1024*1024
        with self.assertRaisesRegex(ValueError,'archive size'):self.result_of()
        self.assertFalse(any(method=='GET_BYTES' for method,_ in self.api.calls))

    def test_record_cannot_change_program_or_execution(self):
        original=copy.deepcopy(self.wrapper)
        for field,value in [('repository_id',13),('recovery_run',11),('recovery_attempt',2),('program_commit','f'*40)]:
            changed=dict(original,**{field:value});self.archive('intents',changed,40)
            with self.assertRaisesRegex(ValueError,'execution binding'):self.result_of()

    def test_operation_cannot_name_other_repo_ref_or_key(self):
        original=copy.deepcopy(self.intent)
        for mutation in ('repo','ref','key','attempt','request'):
            changed=copy.deepcopy(original)
            if mutation=='repo':changed['operation']['repository']='evil/repo';changed['operation_key']=operation_key(changed['operation'])
            elif mutation=='ref':changed['operation']['ref']='candidate'
            elif mutation=='key':changed['operation_key']='0'*64
            elif mutation=='attempt':changed['recovery_attempt']=2
            elif mutation=='request':changed['request']={'ref':'candidate','return_run_details':True}
            self.wrapper['operations']=[changed];self.archive('intents',self.wrapper,40)
            with self.assertRaises(ValueError):self.result_of()

    def test_duplicate_operations_are_rejected(self):
        self.wrapper['operations']=[self.intent,self.intent];self.archive('intents',self.wrapper,40)
        with self.assertRaisesRegex(ValueError,'duplicate operation'):self.result_of()

    def test_orphan_or_duplicate_receipt_is_not_silently_reused(self):
        for receipts in ([dict(self.receipt,operation_key='f'*64)],[self.receipt,self.receipt],
                         [dict(self.receipt,recovery_attempt=2)]):
            self.result['receipts']=receipts;self.archive('results',self.result,41)
            with self.assertRaisesRegex(ValueError,'receipt'):self.result_of()

    def test_partial_receipts_preserve_each_operation_independently(self):
        second=copy.deepcopy(self.intent);second['operation']['workflow']='research-checks.yml'
        second['operation_key']=operation_key(second['operation'])
        self.wrapper['operations'].append(second);self.archive('intents',self.wrapper,40)
        self.result['receipts']=[self.receipt];self.archive('results',self.result,41)
        values=self.result_of()['operations']
        self.assertIsNotNone(values[self.key]['receipt'])
        self.assertIsNone(values[second['operation_key']]['receipt'])


    def test_result_requires_completed_upload_after_completed_dispatch(self):
        self.result['receipts']=[self.receipt];self.archive('results',self.result,41)
        self.assertTrue(self.result_of()['results_persisted_after_dispatch'])
        original=copy.deepcopy(self.job['steps'])
        for change in ('missing','early','failed','running_dispatch','duplicate'):
            self.job['steps']=copy.deepcopy(original)
            if change=='missing':self.job['steps'].pop()
            elif change=='early':self.job['steps'][-1]['number']=2
            elif change=='failed':self.job['steps'][-1]['conclusion']='failure'
            elif change=='running_dispatch':self.job['steps'][1]['status']='in_progress'
            else:self.job['steps'].append(copy.deepcopy(self.job['steps'][-1]))
            with self.subTest(change=change),self.assertRaisesRegex(ValueError,'results not uploaded'):
                self.result_of()
    def test_no_result_never_claims_result_upload_proof(self):
        self.assertFalse(self.result_of()['results_persisted_after_dispatch'])


if __name__=='__main__':unittest.main()

import copy
import hashlib
import io
import json
import unittest
import zipfile
from unittest.mock import patch
from discover_deferred import pages, required_review_app, discover_deferred
import test_deferred_source as fixtures


class ReadAPI:
    def __init__(self, records, binaries):
        self.records=records;self.binaries=binaries;self.calls=[]
    def json(self,path):
        self.calls.append(('GET JSON',path))
        return copy.deepcopy(self.records[path])
    def bytes(self,path):
        self.calls.append(('GET BYTES',path))
        return self.binaries[path]


class Discovery(unittest.TestCase):
    def setUp(self):
        fixture=fixtures.PublicationChainTests();fixture.setUp()
        self.repo=fixture.repo;self.pr=fixture.pr;self.accepted=fixture.accepted;self.requester=fixture.requester
        self.pin={'type':'required_status_checks','parameters':{'required_status_checks':[
            {'context':'Protocol B / review','integration_id':42}]}}
        self.check_path='commits/'+'a'*40+'/check-runs?filter=all&per_page=100&page=1'
        self.records={'':{'id':7,'full_name':self.repo,'default_branch':'main'},'pulls/7':self.pr,
            'rules/branches/main?per_page=100&page=1':[self.pin],self.check_path:{'total_count':2,
                'check_runs':[self.accepted['check'],self.requester['check']]}}
        self.binaries={}
        for bundle in (self.accepted,self.requester): self.pack(bundle)
        self.api=ReadAPI(self.records,self.binaries)
    def pack(self,bundle):
        run=bundle['publisher'];rid=run['id'];run['head_sha']='d'*40
        self.records[f'actions/runs/{rid}']=run
        archive=io.BytesIO()
        with zipfile.ZipFile(archive,'w') as z:
            for file,key in [('decision.json','decision'),('post-merge-manual.json','deferred'),('auto-merge-result.json','auto_result')]:
                if key in bundle:z.writestr(file,json.dumps(bundle[key]))
        raw=archive.getvalue();aid=rid+1000
        metadata={'id':aid,'name':f'protocol-b-{rid}-1','expired':False,'size_in_bytes':len(raw),
            'digest':'sha256:'+hashlib.sha256(raw).hexdigest(),
            'workflow_run':{'id':rid,'repository_id':7,'head_sha':run['head_sha']}}
        self.records[f'actions/runs/{rid}/artifacts?per_page=100&page=1']={'total_count':1,'artifacts':[metadata]}
        self.binaries[f'actions/artifacts/{aid}/zip']=raw
    def result(self):
        result=discover_deferred(self.api,self.repo,7)
        self.assertFalse(result['dispatch_authorized'])
        return result
    def test_current_rules_and_two_original_runs_are_both_required(self):
        result=self.result();self.assertTrue(result['eligible'])
        self.assertEqual(result['requester']['publisher']['id'],123)
        self.assertEqual(result['accepted']['publisher']['id'],124)
        self.assertEqual({op['ref'] for op in result['result']['operations']},{'main'})
        self.assertTrue(all(method.startswith('GET') for method,path in self.api.calls))
        self.assertFalse(any('contents/' in path for method,path in self.api.calls))
    def test_required_app_on_later_page_is_not_missed(self):
        self.records['rules/branches/main?per_page=100&page=1']=[{'type':'other'} for _ in range(100)]
        self.records['rules/branches/main?per_page=100&page=2']=[self.pin]
        self.assertTrue(self.result()['eligible'])
    def test_latest_failed_check_never_falls_back_to_old_acceptance(self):
        self.accepted['check']['conclusion']='failure'
        with self.assertRaisesRegex(ValueError,'latest required'):self.result()
        self.assertFalse(any(method=='GET BYTES' for method,path in self.api.calls))
    def test_forged_check_name_from_actions_is_ignored(self):
        fake=copy.deepcopy(self.accepted['check']);fake.update(id=999,app={'id':15368},details_url='https://evil.invalid')
        listing=self.records[self.check_path];listing['total_count']=3;listing['check_runs'].insert(0,fake)
        self.assertTrue(self.result()['eligible'])
    def test_missing_null_or_conflicting_app_pin_is_refused(self):
        path='rules/branches/main?per_page=100&page=1'
        for value in ([],[{'type':'required_status_checks','parameters':{'required_status_checks':[
                    {'context':'Protocol B / review','integration_id':None}]}}],
                [self.pin,{'type':'required_status_checks','parameters':{'required_status_checks':[
                    {'context':'Protocol B / review','integration_id':43}]}}]):
            self.records[path]=value
            with self.assertRaises(ValueError):self.result()
    def test_open_or_human_merge_stops_before_review_downloads(self):
        for key,value in [('merged',False),('state','open'),('merged_by',{'login':'owner','type':'User'})]:
            with patch.dict(self.pr,{key:value}):
                with self.assertRaisesRegex(ValueError,'confirmed gate-actor'):self.result()
        self.assertFalse(any(method=='GET BYTES' for method,path in self.api.calls))
    def test_active_publisher_cannot_race_its_inline_dispatch(self):
        self.accepted['publisher']['status']='in_progress'
        with self.assertRaisesRegex(ValueError,'still active'):self.result()
    def test_wrong_publisher_repository_or_workflow_is_rejected(self):
        for key,value in [('repository',{'full_name':'fork/repo'}),('path','.github/workflows/forged.yml')]:
            with patch.dict(self.accepted['publisher'],{key:value}):
                with self.assertRaises(ValueError):self.result()
    def test_modified_archive_never_supplies_receipt(self):
        self.binaries['actions/artifacts/1123/zip']+=b'changed'
        result=self.result();self.assertFalse(result['eligible'])
        self.assertIn('artifact digest',[e['reason'] for e in result['examined']])
    def test_declared_oversized_archive_is_not_downloaded(self):
        self.records['actions/runs/124/artifacts?per_page=100&page=1']['artifacts'][0]['size_in_bytes']=33*1024*1024
        with self.assertRaisesRegex(ValueError,'declared archive'):self.result()
        self.assertFalse(any(method=='GET BYTES' for method,path in self.api.calls))
    def test_expired_requester_is_unresolved_not_absent(self):
        self.records['actions/runs/123/artifacts?per_page=100&page=1']['artifacts'][0]['expired']=True
        result=self.result();self.assertFalse(result['eligible'])
        self.assertIn('expired original artifact',[e['reason'] for e in result['examined']])
    def test_requester_rerun_still_reads_original_attempt(self):
        old=copy.deepcopy(self.requester['publisher'])
        self.records['actions/runs/123/attempts/1']=old
        self.records['actions/runs/123']=old|{'run_attempt':2}
        result=self.result()
        self.assertTrue(result['eligible'])
        self.assertEqual(result['requester']['publisher']['run_attempt'],1)
        self.assertIn(('GET JSON','actions/runs/123/attempts/1'),self.api.calls)
    def test_wrong_original_attempt_is_refused(self):
        old=copy.deepcopy(self.requester['publisher'])
        self.records['actions/runs/123/attempts/1']=old|{'run_attempt':2}
        self.records['actions/runs/123']=old|{'run_attempt':2}
        result=self.result();self.assertFalse(result['eligible'])
        self.assertIn('original attempt identity',[e['reason'] for e in result['examined']])
    def test_duplicate_attempt_artifacts_are_ambiguous(self):
        listing=self.records['actions/runs/123/artifacts?per_page=100&page=1']
        listing['artifacts'].append(listing['artifacts'][0]|{'id':9876})
        listing['total_count']=2
        self.assertFalse(self.result()['eligible'])
    def test_missing_original_request_cannot_be_synthesized_from_merge(self):
        self.requester.pop('auto_result');self.pack(self.requester)
        self.assertFalse(self.result()['eligible'])
    def test_pagination_changing_total_duplicate_id_and_limit_refuse(self):
        one=[{'id':i+1} for i in range(100)]
        for second in ({'total_count':102,'rows':[{'id':101}]},{'total_count':101,'rows':[{'id':100}]},
                       {'total_count':102,'rows':[{'id':101}]}):
            api=ReadAPI({'x?per_page=100&page=1':{'total_count':101,'rows':one},'x?per_page=100&page=2':second},{})
            with self.assertRaises(ValueError):pages(api,'x','rows',identity='id')
        api=ReadAPI({'x?per_page=100&page=1':{'total_count':100,'rows':one}},{})
        with self.assertRaisesRegex(ValueError,'pagination limit'):pages(api,'x','rows',identity='id',max_pages=1)
    def test_declared_missing_tail_is_rejected(self):
        self.records[self.check_path]['total_count']=3
        with self.assertRaisesRegex(ValueError,'incomplete collection'):self.result()
    def test_candidate_report_and_event_payload_are_not_inputs(self):
        result=self.result()
        self.assertTrue(result['eligible'])
        paths=[p for _,p in self.api.calls]
        self.assertFalse(any('comments' in p or 'contents/' in p or 'event' in p for p in paths))

if __name__=='__main__':unittest.main()

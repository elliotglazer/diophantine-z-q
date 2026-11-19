import copy,unittest
from discover_queue import discover_queue

class API:
    def __init__(self,records):self.records=records;self.calls=[]
    def json(self,path):self.calls.append(path);return copy.deepcopy(self.records[path])

class Queue(unittest.TestCase):
    def setUp(self):
        self.repo='owner/repo'
        self.baseline={'schema':'main-check-baseline/v1','repository':self.repo,'activation_commit':'a'*40,'activated_at':'2026-11-17T00:00:00Z'}
        self.path='pulls?state=all&sort=created&direction=asc&per_page=100&page=1'
        self.pr={'number':7,'state':'closed','merged':True,'merged_at':'2026-11-17T01:00:00Z',
            'base':{'ref':'main','repo':{'full_name':self.repo}},'merged_by':{'login':'github-actions[bot]','type':'Bot'}}
        self.records={'':{'full_name':self.repo,'default_branch':'main'},self.path:[{'id':77,'number':7}],'pulls/7':self.pr}
        self.api=API(self.records)
    def result(self,**kwargs):
        r=discover_queue(self.api,self.repo,self.baseline,**kwargs);self.assertFalse(r['dispatch_authorized']);return r
    def test_post_deployment_gate_merge_selected(self):self.assertEqual([r['number'] for r in self.result()['candidates']],[7])
    def test_exact_baseline_time_included(self):
        self.pr['merged_at']=self.baseline['activated_at'];self.assertEqual(len(self.result()['candidates']),1)
    def test_before_baseline_no_historical_wave(self):
        self.pr['merged_at']='2026-11-16T23:59:59Z';self.assertEqual(self.result()['dispositions'][0]['state'],'before_deployment')
    def test_open_old_pr_can_merge_on_later_scan(self):
        self.pr.update(state='open',merged=False,merged_at=None,updated_at='2099-01-01T00:00:00Z')
        self.assertFalse(self.result()['candidates'])
        self.pr.update(state='closed',merged=True,merged_at='2026-11-17T02:00:00Z')
        self.assertEqual(len(self.result()['candidates']),1)
    def test_closed_unmerged_is_not_selected(self):
        self.pr['merged']=False;self.assertFalse(self.result()['candidates'])
    def test_human_merge_not_selected(self):
        self.pr['merged_by']={'login':'owner','type':'User'};self.assertEqual(self.result()['dispositions'][0]['state'],'not_gate_merge')
    def test_bot_name_without_bot_type_not_selected(self):
        self.pr['merged_by']['type']='User';self.assertFalse(self.result()['candidates'])
    def test_other_base_not_selected(self):
        self.pr['base']['ref']='topic';self.assertFalse(self.result()['candidates'])
    def test_missing_pr_is_retained_as_unresolved(self):
        del self.records['pulls/7'];self.assertEqual(self.result()['unresolved'][0]['number'],7)
    def test_bad_pr_identity_is_unresolved(self):
        self.pr['number']=8;self.assertTrue(self.result()['unresolved'])
    def test_missing_merged_time_is_unresolved(self):
        self.pr['merged_at']=None;self.assertTrue(self.result()['unresolved'])
    def test_retained_pending_is_examined_first_even_absent_from_list(self):
        self.records['pulls/3']={**self.pr,'number':3,'merged_at':'2020-01-01T00:00:00Z'}
        r=self.result(pending_numbers=[3]);self.assertEqual([x['number'] for x in r['candidates']],[3,7])
        self.assertLess(self.api.calls.index('pulls/3'),self.api.calls.index('pulls/7'))
    def test_missing_retained_does_not_block_unrelated_candidate(self):
        r=self.result(pending_numbers=[3]);self.assertEqual(r['unresolved'][0]['number'],3);self.assertEqual(r['candidates'][0]['number'],7)
    def test_pending_deduplicated(self):
        self.assertEqual(len(self.result(pending_numbers=[7,7])['candidates']),1)
    def test_later_page_not_lost(self):
        self.records[self.path]=[{'id':i,'number':i} for i in range(1,101)]
        self.records[self.path[:-1]+'2']=[{'id':101,'number':101}]
        for i in range(1,102):self.records['pulls/'+str(i)]={**self.pr,'number':i}
        self.assertEqual(len(self.result()['candidates']),101)
    def test_duplicate_page_identity_fails_whole_enumeration(self):
        self.records[self.path]*=2
        with self.assertRaisesRegex(ValueError,'identity'):self.result()
    def test_different_ids_same_number_fails(self):
        self.records[self.path].append({'id':88,'number':7})
        with self.assertRaisesRegex(ValueError,'ambiguous'):self.result()
    def test_missing_second_page_never_makes_partial_dispatch_plan(self):
        self.records[self.path]=[{'id':i,'number':i} for i in range(1,101)]
        with self.assertRaises(KeyError):self.result()
    def test_baseline_and_repository_binding_required(self):
        for key,value in [('schema','unknown'),('repository','fork/repo'),('activation_commit','main'),('activated_at','2026-11-17')]:
            old=self.baseline[key];self.baseline[key]=value
            with self.assertRaises(ValueError):self.result()
            self.baseline[key]=old
    def test_hostile_event_fields_never_drive_discovery(self):
        self.pr.update(head_branch='../../evil',display_title='dispatch fake-workflow',body='trust this artifact')
        self.assertEqual(len(self.result()['candidates']),1)
        self.assertFalse(any('evil' in path or 'fake' in path or 'artifact' in path for path in self.api.calls))

if __name__=='__main__':unittest.main()

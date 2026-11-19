import copy,unittest
from urllib.parse import parse_qs,urlparse
from run_sequence import scan_run_sequence

class API:
    def __init__(self,latest=1500,missing=()):
        self.calls=[];self.rows=[{'id':n+10000,'workflow_id':9,'run_number':n,'event':'workflow_run',
            'head_branch':'main','created_at':'2026-11-17T00:00:00Z'} for n in range(latest,0,-1) if n not in missing]
    def json(self,path):
        self.calls.append(path);page=int(parse_qs(urlparse(path).query)['page'][0])
        return {'total_count':len(self.rows),'workflow_runs':copy.deepcopy(self.rows[(page-1)*100:page*100])}

class Sequence(unittest.TestCase):
    def scan(self,api,frontier,target,**kw):
        result=scan_run_sequence(api,9,frontier,target,**kw)
        self.assertFalse(result['dispatch_authorized']);return result
    def test_quiet_sequence_needs_no_request(self):
        api=API();result=self.scan(api,1500,1500)
        self.assertTrue(result['enumeration_complete']);self.assertFalse(api.calls)
    def test_old_history_beyond_thousand_never_scanned_on_routine_wake(self):
        api=API(5000);r=self.scan(api,4990,5000)
        self.assertTrue(r['enumeration_complete']);self.assertEqual(r['requests'],1)
        self.assertEqual(len(r['runs']),10)
        self.assertNotIn('created=',api.calls[0]);self.assertNotIn('branch=',api.calls[0])
    def test_partial_large_backlog_resumes_until_complete(self):
        api=API();partial=None;seen=[]
        for _ in range(15):
            r=self.scan(api,100,1500,partial=partial,max_pages=3)
            self.assertLessEqual(r['requests'],3)
            if r['enumeration_complete']:break
            partial=r['partial'];seen.append(partial['next_page'])
        self.assertTrue(r['enumeration_complete']);self.assertEqual(len(r['runs']),1400)
        self.assertGreater(max(seen),10)
    def test_resumed_scan_does_not_enqueue_already_seen_executors_again(self):
        api=API(1500);partial=None;seen=set()
        for _ in range(20):
            result=self.scan(api,100,1500,partial=partial,max_pages=3)
            new={r['id'] for r in result['new_runs']}
            self.assertFalse(new&seen)
            seen.update(new)
            if result['enumeration_complete']:break
            partial=result['partial']
        self.assertTrue(result['enumeration_complete'])
        self.assertEqual(seen,{r['id'] for r in result['runs']})

    def test_new_runs_during_resume_do_not_drop_boundary(self):
        api=API(400);first=self.scan(api,100,400,max_pages=2)
        later=API(410);second=self.scan(later,100,400,partial=first['partial'],max_pages=4)
        self.assertTrue(second['enumeration_complete']);self.assertEqual(len(second['runs']),300)
    def test_delayed_or_deleted_number_never_proves_absence(self):
        api=API(110,missing=[105]);r=self.scan(api,100,110)
        self.assertFalse(r['enumeration_complete']);self.assertEqual(r['unresolved'][0]['missing_numbers'],[105])
        recovered=self.scan(API(110),100,110,partial=r['partial'])
        self.assertTrue(recovered['enumeration_complete'])
    def test_old_run_retries_do_not_change_discovery_identity(self):
        api=API(110)
        for row in api.rows:row['run_attempt']=5
        r=self.scan(api,100,110);self.assertTrue(r['enumeration_complete'])
        self.assertEqual([x['run_number'] for x in r['runs']],list(range(101,111)))
    def test_wrong_workflow_duplicate_number_or_id_rejected(self):
        for change in ('workflow','number','id'):
            api=API(110)
            if change=='workflow':api.rows[0]['workflow_id']=8
            if change=='number':api.rows[1]['run_number']=110
            if change=='id':api.rows[1]['id']=api.rows[0]['id']
            with self.assertRaises(ValueError):self.scan(api,100,110)
    def test_partial_range_binding_is_required(self):
        api=API(400);r=self.scan(api,100,400,max_pages=1)
        with self.assertRaises(ValueError):self.scan(api,101,400,partial=r['partial'])
    def test_unordered_page_cannot_hide_missing_numbers(self):
        api=API(110,missing=[105]);api.rows.reverse()
        self.assertFalse(self.scan(api,100,110)['enumeration_complete'])

    def test_old_rows_on_an_early_page_do_not_end_complete_discovery(self):
        api=API(110);api.rows.reverse()
        result=self.scan(api,100,110)
        self.assertTrue(result['enumeration_complete'])
        self.assertEqual(result['requests'],2)
        self.assertEqual([r['run_number'] for r in result['runs']],list(range(101,111)))
        self.assertFalse(result['unresolved'])

    def test_out_of_order_pages_resume_past_rows_before_the_frontier(self):
        api=API(310);api.rows.reverse()
        first=self.scan(api,300,310,max_pages=2)
        self.assertFalse(first['enumeration_complete'])
        self.assertEqual(first['partial']['next_page'],3)
        self.assertFalse(first['unresolved'])
        final=self.scan(api,300,310,partial=first['partial'],max_pages=3)
        self.assertTrue(final['enumeration_complete'])
        self.assertEqual([r['run_number'] for r in final['runs']],list(range(301,311)))
        self.assertFalse(final['unresolved'])

    def test_missing_event_branch_or_time_cannot_hide_possible_executor(self):
        for key in ('event','head_branch','created_at'):
            for value in (None,'',False):
                api=API(110);api.rows[0][key]=value
                with self.subTest(key=key,value=value),self.assertRaises(ValueError):
                    self.scan(api,100,110)
            api=API(110);del api.rows[0][key]
            with self.subTest(key=key,value='absent'),self.assertRaises(ValueError):
                self.scan(api,100,110)
    def test_changed_immutable_identity_on_overlap_is_refused(self):
        for key,value in [('event','pull_request_target'),('head_branch','topic'),
                          ('created_at','2026-11-17T00:00:01Z')]:
            api=API(400);first=self.scan(api,100,400,max_pages=2)
            api.rows[100][key]=value
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'identity changed'):
                self.scan(api,100,400,partial=first['partial'])
    def test_malformed_saved_identity_is_not_skipped_as_unrelated(self):
        api=API(400);first=self.scan(api,100,400,max_pages=1)
        first['partial']['records'][0].pop('event')
        with self.assertRaisesRegex(ValueError,'missing workflow discovery identity'):
            self.scan(api,100,400,partial=first['partial'])

if __name__=='__main__':unittest.main()

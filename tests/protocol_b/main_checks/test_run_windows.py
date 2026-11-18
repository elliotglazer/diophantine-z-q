import copy,datetime,unittest
from urllib.parse import parse_qs,urlparse
from run_windows import scan_run_windows,printed,stamp


class API:
    def __init__(self,rows):self.rows=rows;self.calls=[];self.break_page=None
    def json(self,path):
        self.calls.append(path);q=parse_qs(urlparse(path).query)
        start,end=q['created'][0].split('..');page=int(q['page'][0])
        rows=[r for r in self.rows if stamp(start)<=stamp(r['created_at'])<=stamp(end)]
        rows.sort(key=lambda r:(r['created_at'],r['id']),reverse=True)
        value={'total_count':len(rows),'workflow_runs':copy.deepcopy(rows[(page-1)*100:min(page*100,1000)])}
        if self.break_page==page:value['workflow_runs']=[]
        return value


class Windows(unittest.TestCase):
    def setUp(self):self.start=stamp('2026-11-17T00:00:00Z')
    def rows(self,n):return [{'id':i+1,'created_at':printed(self.start+i)} for i in range(n)]
    def run_scan(self,api,seconds,**kw):
        result=scan_run_windows(api,9,[{'start':printed(self.start),'end':printed(self.start+seconds)}],**kw)
        self.assertFalse(result['dispatch_authorized']);return result
    def test_small_window_uses_one_request(self):
        api=API(self.rows(3));result=self.run_scan(api,10)
        self.assertEqual(result['requests'],1);self.assertTrue(result['enumeration_complete'])
        self.assertEqual(len(result['runs']),3)
    def test_empty_window_proves_empty_with_one_request(self):
        result=self.run_scan(API([]),10);self.assertTrue(result['enumeration_complete']);self.assertFalse(result['runs'])
    def test_exact_thousand_splits_in_case_total_count_was_clipped(self):
        result=self.run_scan(API(self.rows(1000)),999)
        self.assertTrue(result['enumeration_complete']);self.assertEqual(len(result['runs']),1000)
        self.assertEqual(result['requests'],11)
    def test_more_than_thousand_splits_without_losing_later_pages(self):
        result=self.run_scan(API(self.rows(1200)),1199)
        self.assertTrue(result['enumeration_complete']);self.assertEqual(len(result['runs']),1200)
        self.assertEqual(result['requests'],13)
    def test_capped_total_count_does_not_hide_older_results(self):
        api=API(self.rows(2400));original=api.json
        def capped(path):
            value=original(path);value['total_count']=min(value['total_count'],1000);return value
        api.json=capped
        result=self.run_scan(api,2399,max_requests=40)
        self.assertTrue(result['enumeration_complete']);self.assertEqual(len(result['runs']),2400)
    def test_budget_is_hard_and_remainder_can_resume(self):
        api=API(self.rows(1200));first=self.run_scan(api,1199,max_requests=8)
        self.assertLessEqual(first['requests'],8);self.assertFalse(first['enumeration_complete'])
        self.assertEqual(len(first['runs']),600)
        second=scan_run_windows(api,9,first['pending_windows'],max_requests=8)
        self.assertTrue(second['enumeration_complete'])
        self.assertEqual({r['id'] for r in first['runs']+second['runs']},set(range(1,1201)))
    def test_budget_cannot_return_partial_window_as_complete(self):
        result=self.run_scan(API(self.rows(500)),499,max_requests=3)
        self.assertFalse(result['runs']);self.assertFalse(result['enumeration_complete'])
    def test_single_second_overflow_is_visible_not_infinite(self):
        rows=self.rows(1001)
        for row in rows:row['created_at']=printed(self.start)
        result=self.run_scan(API(rows),0)
        self.assertEqual(result['requests'],1);self.assertFalse(result['enumeration_complete'])
        self.assertIn('one second',result['unresolved'][0]['reason'])
    def test_truncated_later_page_never_advances_window(self):
        api=API(self.rows(150));api.break_page=2;result=self.run_scan(api,149)
        self.assertFalse(result['runs']);self.assertTrue(result['pending_windows']);self.assertTrue(result['unresolved'])
    def test_changed_count_never_advances(self):
        api=API(self.rows(150));original=api.json
        def changed(path):
            r=original(path)
            if 'page=2' in path:r['total_count']+=1
            return r
        api.json=changed
        result=self.run_scan(api,149);self.assertFalse(result['runs']);self.assertTrue(result['unresolved'])
    def test_duplicate_identity_rejected(self):
        rows=self.rows(3);rows[1]['id']=rows[0]['id']
        result=self.run_scan(API(rows),3);self.assertTrue(result['unresolved']);self.assertFalse(result['runs'])
    def test_overlap_invalid_bound_and_unzoned_time_rejected(self):
        window={'start':printed(self.start),'end':printed(self.start+10)}
        for windows,budget in [([window,window],20),([window],0),([window],True),
            ([{'start':'2026-11-17T00:00:00','end':window['end']}],20)]:
            with self.assertRaises(ValueError):scan_run_windows(API([]),9,windows,max_requests=budget)
    def test_no_dispatch_capability_is_needed(self):
        api=API(self.rows(1));self.run_scan(api,1)
        self.assertTrue(all(path.startswith('actions/workflows/9/runs?branch=main&created=') for path in api.calls))

if __name__=='__main__':unittest.main()

import copy,unittest
from unittest.mock import patch
from progress_record import NAME,latest_progress,checkpoint_name
import test_progress_record as fixtures


class Selection(unittest.TestCase):
    def setUp(self):
        self.f=fixtures.Progress();self.f.setUp();self.api=self.f.f.api
        self.current={'started_at':'2026-11-17T01:01:00Z'}
    def page(self,rows,*,page=1,total=None,day='20261117'):
        self.f.f.records['actions/artifacts?name='+NAME+'-'+day+'&per_page=100&page='+str(page)]={
            'total_count':len(rows) if total is None else total,'artifacts':rows}
    def run_lookup(self,**kwargs):
        return latest_progress(self.api,self.f.f.repo,self.f.baseline,self.f.f.main,
                               current_job=self.current,**kwargs)
    def test_real_authenticated_checkpoint_and_read_only_lookup(self):
        self.page([self.f.artifact]);value=self.run_lookup()
        self.assertTrue(value['discovery_complete']);self.assertEqual(value['progress']['artifact']['id'],42)
        self.assertTrue(all(m in ('GET','GET_BYTES') for m,_ in self.api.calls))
    def test_smaller_artifact_id_can_be_the_newest_checkpoint(self):
        old=dict(self.f.artifact,id=999,created_at='2026-11-17T01:00:00Z')
        self.page([old,self.f.artifact]);value=self.run_lookup()
        self.assertEqual(value['progress']['artifact']['id'],42)
        self.assertNotIn(('GET','actions/artifacts/999'),self.api.calls)
    def test_later_execution_with_lower_workflow_run_number_is_selected(self):
        self.f.f.publisher['run_number']=8
        self.f.record['run_anchor']={'run':11,'number':11}
        self.f.record['run_sequence']['frontier']=10
        self.f.f.records['actions/runs/11']=dict(self.f.f.publisher,id=11,run_number=11)
        self.f.pack()
        older=dict(self.f.artifact,id=999,created_at='2026-11-17T01:00:00Z')
        self.page([older,self.f.artifact]);value=self.run_lookup()
        self.assertTrue(value['discovery_complete'])
        self.assertEqual(value['progress']['publisher']['run_number'],8)
        self.assertEqual(value['progress']['record']['run_sequence']['frontier'],10)
    def test_newest_checkpoint_on_later_page_is_read(self):
        older=[dict(self.f.artifact,id=i,created_at='2026-11-17T01:00:00Z') for i in range(100,200)]
        self.page(older,total=101);self.page([self.f.artifact],page=2,total=101)
        self.assertEqual(self.run_lookup()['progress']['artifact']['id'],42)
    def test_whole_current_day_is_inspected_before_previous_day(self):
        self.current['started_at']='2026-11-18T00:01:00Z'
        self.page([],day='20261118');self.page([self.f.artifact])
        value=self.run_lookup();self.assertEqual(len(value['searched_buckets']),2)
        self.assertTrue(value['discovery_complete'])
    def test_complete_empty_since_baseline_can_initialize(self):
        self.page([]);value=self.run_lookup()
        self.assertIsNone(value['progress']);self.assertTrue(value['discovery_complete'])
        self.assertIn('baseline',value['fallback'])
    def test_page_bound_is_not_empty_history(self):
        self.page([],total=301);value=self.run_lookup()
        self.assertFalse(value['discovery_complete']);self.assertNotIn('fallback',value)
        self.assertIn('page bound',str(value['unresolved']))
    def test_missing_rows_or_changed_total_never_select_earlier_page(self):
        first=[dict(self.f.artifact,id=i) for i in range(100,200)]
        for second,total in (([],101),([self.f.artifact],102)):
            self.page(first,total=101);self.page(second,page=2,total=total)
            self.assertFalse(self.run_lookup()['discovery_complete'])
    def test_duplicate_identity_across_pages_is_not_complete(self):
        rows=[dict(self.f.artifact,id=i) for i in range(100,200)]
        self.page(rows,total=101);self.page([rows[0]],page=2,total=101)
        self.assertFalse(self.run_lookup()['discovery_complete'])
    def test_invalid_latest_does_not_fall_back_to_older_checkpoint(self):
        bad=dict(self.f.artifact,id=999,created_at='2026-11-17T01:00:02Z')
        self.page([self.f.artifact,bad]);value=self.run_lookup()
        self.assertIsNone(value['progress']);self.assertFalse(value['discovery_complete'])
        self.assertNotIn(('GET','actions/artifacts/42'),self.api.calls)
    def test_failed_bucket_read_is_unresolved(self):
        value=self.run_lookup();self.assertFalse(value['discovery_complete'])
        self.assertNotIn('fallback',value)
    def test_date_bound_is_unresolved_and_never_resets_state(self):
        self.current['started_at']='2026-11-19T01:01:00Z'
        self.page([],day='20261119');self.page([],day='20261118')
        value=self.run_lookup(max_days=2)
        self.assertFalse(value['discovery_complete']);self.assertIn('date bound',str(value['unresolved']))
        self.assertEqual(len(self.api.calls),2)
    def test_timestamp_tie_is_not_broken_by_artifact_id(self):
        second=dict(self.f.artifact,id=100)
        self.page([self.f.artifact,second])
        loaded={'artifact':self.f.artifact,'job':self.f.f.job}
        with patch('progress_record.read_progress',side_effect=[loaded,dict(loaded,artifact=second)]):
            value=self.run_lookup()
        self.assertFalse(value['discovery_complete']);self.assertIn('same-second',str(value['unresolved']))
        self.assertIn('artifact IDs: 42, 100',str(value['unresolved']))
    def test_tie_authentication_bound(self):
        self.page([dict(self.f.artifact,id=i) for i in range(100,104)])
        with patch('progress_record.read_progress') as read:
            value=self.run_lookup()
        read.assert_not_called();self.assertFalse(value['discovery_complete'])
    def test_changed_ordering_metadata_or_overlapping_executor_stops(self):
        self.page([self.f.artifact])
        for changes in ({'created_at':'2026-11-17T01:00:02Z'},{}):
            loaded={'artifact':dict(self.f.artifact,**changes),'job':dict(self.f.f.job)}
            if not changes:loaded['job']['completed_at']='2026-11-17T01:02:00Z'
            with patch('progress_record.read_progress',return_value=loaded):
                self.assertFalse(self.run_lookup()['discovery_complete'])
    def test_name_uses_original_job_start_date_in_utc(self):
        self.assertEqual(checkpoint_name('2026-11-17T18:30:00-08:00'),NAME+'-20261118')


if __name__=='__main__':unittest.main()

import copy, unittest
from existing_search import search_existing
from run_windows import stamp, printed
from test_run_windows import API as WindowAPI

START=stamp('2026-11-17T00:00:00Z')
OP={'repository':'owner/repo','number':7,'head':'a'*40,'merge':'b'*40,
    'workflow':'kernel-lean.yml','ref':'main'}


def row(i, *, event='workflow_dispatch', head='b'*40, conclusion='success'):
    return {'id':i+1,'workflow_id':9,'created_at':printed(START+i),'repository':{'full_name':'owner/repo'},
            'head_repository':{'full_name':'owner/repo'},'head_sha':head,'head_branch':'main',
            'event':event,'path':'.github/workflows/kernel-lean.yml','status':'completed','conclusion':conclusion}


class API(WindowAPI):
    def __init__(self,rows):
        super().__init__(rows);self.current={r['id']:copy.deepcopy(r) for r in rows}
        self.comparisons={};self.fail_path=None
    def json(self,path):
        if path==self.fail_path:raise OSError('temporarily unavailable')
        if path=='actions/workflows/kernel-lean.yml':
            self.calls.append(path);return {'id':9,'path':'.github/workflows/kernel-lean.yml'}
        if path.startswith('actions/runs/'):
            self.calls.append(path);return copy.deepcopy(self.current[int(path.rsplit('/',1)[1])])
        if path.startswith('compare/'):
            self.calls.append(path);return copy.deepcopy(self.comparisons[path.rsplit('...',1)[1]])
        return super().json(path)


class Search(unittest.TestCase):
    def run_search(self,api,seconds=1200,cursor=None,**kw):
        return search_existing(api,OP,printed(START),'b'*40,False,
                               now=START+seconds,cursor=cursor,**kw)
    def test_exact_thousand_finishes_across_bounded_wakes(self):
        api=API([row(i,event='schedule') for i in range(1000)])
        first=self.run_search(api,999)
        self.assertEqual(first['classification']['state'],'incomplete_enumeration')
        self.assertTrue(first['search']['pending_windows'])
        self.assertFalse(first['search']['identities'])
        before=len(api.calls)
        second=self.run_search(api,1005,cursor=first['search'])
        self.assertEqual(second['classification']['state'],'no_confirmed_run_check_intents')
        self.assertFalse(second['search']['pending_windows'])
        self.assertLessEqual(len(api.calls)-before,11)
    def test_large_catchup_drains_instead_of_repeating_first_window(self):
        api=API([row(i,event='schedule') for i in range(2400)])
        cursor=None
        for wake in range(10):
            before=len(api.calls);result=self.run_search(api,2400+wake,cursor=cursor)
            self.assertLessEqual(len(api.calls)-before,11)
            cursor=result['search']
            if result['classification']['state']=='no_confirmed_run_check_intents':break
        else:self.fail('existing-run search did not drain')
        self.assertGreater(wake,0)
        self.assertFalse(cursor['identities'])
    def test_partial_listing_never_proves_absence(self):
        api=API([row(i,event='schedule') for i in range(1000)])
        result=self.run_search(api,999)
        self.assertFalse(result['classification']['dispatch_authorized'])
        self.assertEqual(result['classification']['state'],'incomplete_enumeration')
    def test_new_run_in_previous_boundary_second_blocks_dispatch(self):
        api=API([]);first=self.run_search(api,0)
        created=row(0,conclusion=None);created['status']='in_progress'
        api.rows.append(created);api.current[1]=copy.deepcopy(created)
        second=self.run_search(api,0,cursor=first['search'])
        self.assertEqual(second['classification']['state'],'existing_run_in_progress')
        self.assertIn('actions/runs/1',api.calls)
    def test_saved_success_is_not_used_when_actual_run_now_failed(self):
        api=API([row(0)]);first=self.run_search(api,1)
        self.assertEqual(first['classification']['state'],'verification_passed')
        self.assertNotIn('status',first['search']['identities'][0])
        api.current[1]['conclusion']='failure'
        second=self.run_search(api,2,cursor=first['search'])
        self.assertEqual(second['classification']['state'],'existing_runs_need_attention')
    def test_queued_then_success_requires_actual_fresh_get(self):
        initial=row(0,conclusion=None);initial['status']='queued'
        api=API([initial]);first=self.run_search(api,1)
        api.current[1].update(status='completed',conclusion='success')
        before=len(api.calls);second=self.run_search(api,2,cursor=first['search'])
        self.assertEqual(second['classification']['verification_witness'],1)
        self.assertIn('actions/runs/1',api.calls[before:])
    def test_positive_witness_can_prove_coverage_before_enumeration_finishes(self):
        api=API([row(i,event='schedule') for i in range(1000)])
        api.rows[0]=row(0);api.current[1]=row(0)
        result=self.run_search(api,999)
        self.assertEqual(result['classification']['state'],'verification_passed')
        self.assertFalse(result['classification']['enumeration_complete'])
        self.assertEqual(result['classification']['verification_witness'],1)
        self.assertFalse(result['classification']['dispatch_authorized'])
    def test_rotation_finds_fresh_success_without_calling_failed_runs_verified(self):
        api=API([row(0),row(1,conclusion='failure'),row(2,conclusion='failure')])
        first=self.run_search(api,3)
        self.assertEqual(first['classification']['state'],'existing_runs_need_attention')
        second=self.run_search(api,4,cursor=first['search'])
        self.assertEqual(second['classification']['verification_witness'],1)
        self.assertEqual(second['classification']['known_matching_run_ids'],[3,2,1])
        self.assertEqual(second['classification']['other_runs_not_rechecked'],[3,2])
    def test_missing_known_run_never_becomes_absence(self):
        api=API([row(0)]);first=self.run_search(api,1)
        api.fail_path='actions/runs/1'
        second=self.run_search(api,2,cursor=first['search'])
        self.assertEqual(second['classification']['state'],'existing_runs_need_attention')
        self.assertEqual(second['classification']['run_ids'],[1])
    def test_changed_current_identity_is_not_accepted(self):
        api=API([row(0)]);first=self.run_search(api,1)
        api.current[1]['head_sha']='c'*40
        second=self.run_search(api,2,cursor=first['search'])
        self.assertEqual(second['classification']['state'],'existing_runs_need_attention')
    def test_cursor_binding_and_injected_mutable_status_are_refused(self):
        api=API([row(0)]);first=self.run_search(api,1)
        variants=[]
        for key,value in [('operation_key','f'*64),('workflow_id',99),('exact_release',True),
                          ('through',printed(START+100))]:
            cursor=copy.deepcopy(first['search']);cursor[key]=value;variants.append(cursor)
        cursor=copy.deepcopy(first['search']);cursor['identities'][0]['conclusion']='success';variants.append(cursor)
        for cursor in variants:
            with self.subTest(cursor=cursor),self.assertRaises(ValueError):
                self.run_search(api,2,cursor=cursor)
    def test_immutable_older_commit_can_be_excluded_without_empty_commits_error(self):
        api=API([row(0,head='c'*40)])
        api.comparisons['c'*40]={'base_commit':{'sha':'b'*40},'status':'behind','behind_by':1,'commits':[]}
        result=self.run_search(api,1)
        self.assertEqual(result['classification']['state'],'no_confirmed_run_check_intents')
        self.assertFalse(result['search']['identities'])
    def test_bad_comparison_is_not_cached_as_an_immutable_fact(self):
        api=API([row(0,head='c'*40)])
        api.comparisons['c'*40]={'base_commit':{'sha':'b'*40},'status':'ahead','behind_by':0,'commits':[]}
        first=self.run_search(api,1)
        self.assertFalse(first['search']['comparisons'])
        self.assertEqual(first['classification']['state'],'incomplete_enumeration')
        api.comparisons['c'*40]['commits']=[{'sha':'c'*40}]
        second=self.run_search(api,2,cursor=first['search'])
        self.assertEqual(second['classification']['state'],'verification_passed')
    def test_exact_release_never_uses_a_different_head(self):
        api=API([row(0,head='c'*40)])
        result=search_existing(api,OP,printed(START),'c'*40,True,now=START+1)
        self.assertEqual(result['classification']['state'],'missing_exact_release_run')
        self.assertFalse(any(path.startswith('compare/') for path in api.calls))
    def test_incomplete_or_foreign_workflow_listing_never_proves_absence(self):
        for key in ('head_sha','path','repository','workflow_id'):
            malformed=row(0,event='schedule');malformed.pop(key)
            with self.subTest(key=key),self.assertRaises(ValueError):
                self.run_search(API([malformed]),1)
        malformed=row(0,event='schedule');malformed['workflow_id']=8
        with self.assertRaises(ValueError):self.run_search(API([malformed]),1)
    def test_cursor_cannot_persist_a_false_classification_or_extra_status(self):
        api=API([row(0)]);cursor=self.run_search(api,1)['search']
        cursor['classified']['1']=False
        with self.assertRaises(ValueError):self.run_search(api,2,cursor=cursor)

    def test_failed_window_is_retained_and_can_be_retried_read_only(self):
        api=API([row(i,event='schedule') for i in range(150)])
        api.break_page=2;first=self.run_search(api,151)
        self.assertTrue(first['search']['pending_windows'])
        self.assertEqual(first['classification']['state'],'incomplete_enumeration')
        api.break_page=None;second=self.run_search(api,152,cursor=first['search'])
        self.assertEqual(second['classification']['state'],'no_confirmed_run_check_intents')


if __name__=='__main__':unittest.main()

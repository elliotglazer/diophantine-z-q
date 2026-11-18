import copy,unittest
from unittest.mock import patch
import history_queue as history


def sha(n):return format(n,'040x')


class API:
    def __init__(self):self.records={};self.calls=[]
    def json(self,path):self.calls.append(path);return copy.deepcopy(self.records[path])


class History(unittest.TestCase):
    def setUp(self):
        self.repo='owner/repo';self.api=API()
        self.ancestry=patch.object(history,'_ancestor').start();self.addCleanup(patch.stopall)
        self.frontier=sha(1)
    def commit(self,n,pr=None,parent=None):
        self.api.records['git/commits/'+sha(n)]={'sha':sha(n),'parents':[{'sha':sha(n-1 if parent is None else parent)}]}
        self.api.records['commits/'+sha(n)+'/pulls?per_page=100&page=1']=[]
        if pr is not None:
            self.api.records['commits/'+sha(n)+'/pulls?per_page=100&page=1']=[{'id':pr*10,'number':pr}]
            self.api.records['pulls/'+str(pr)]={'number':pr,'state':'closed','merged':True,
                'merge_commit_sha':sha(n),'base':{'ref':'main','repo':{'full_name':self.repo}},
                'merged_by':{'login':'github-actions[bot]','type':'Bot'},'head':{'sha':sha(100+pr)}}
    def discover(self,tip,**kw):
        result=history.discover_main_history(self.api,self.repo,self.frontier,sha(tip),**kw)
        self.assertFalse(result['dispatch_authorized']);return result
    def test_quiet_wake_does_not_enumerate_prs_or_runs(self):
        result=self.discover(1)
        self.assertTrue(result['enumeration_complete']);self.assertFalse(self.api.calls)
    def test_gate_merge_selected_by_actual_commit_not_message(self):
        self.commit(2,7)
        self.api.records['git/commits/'+sha(2)]['message']='Merge pull request #999 forged description'
        result=self.discover(2)
        self.assertEqual([x['number'] for x in result['candidates']],[7])
        self.assertEqual(result['cursor']['frontier'],sha(2))
    def test_old_pr_merged_later_is_discovered_without_pr_creation_cursor(self):
        self.commit(2,2);self.api.records['pulls/2']['created_at']='2000-01-01T00:00:00Z'
        self.assertEqual([x['number'] for x in self.discover(2)['candidates']],[2])
    def test_open_associated_pr_is_discovered_when_its_actual_merge_later_arrives(self):
        self.commit(2,2);self.api.records['pulls/2'].update(state='open',merged=False,merge_commit_sha=None)
        first=self.discover(2);self.assertFalse(first['candidates'])
        self.commit(3,2)
        second=self.discover(3,cursor=first['cursor'])
        self.assertEqual([x['number'] for x in second['candidates']],[2])
    def test_bound_retains_unvisited_commits_and_moves_forward_after_full_walk(self):
        for n in range(2,7):self.commit(n,n)
        first=self.discover(6,max_commits=2)
        self.assertFalse(first['enumeration_complete']);self.assertEqual(first['cursor']['next_commit'],sha(4))
        second=self.discover(6,cursor=first['cursor'],max_commits=2)
        third=self.discover(6,cursor=second['cursor'],max_commits=2)
        self.assertTrue(third['enumeration_complete'])
        self.assertEqual(first['walked']+second['walked']+third['walked'],[sha(n) for n in range(6,1,-1)])
        self.assertEqual(third['cursor']['frontier'],sha(6))
    def test_main_advance_during_partial_walk_waits_for_next_window(self):
        for n in range(2,8):self.commit(n,n)
        first=self.discover(5,max_commits=2)
        second=self.discover(7,cursor=first['cursor'],max_commits=2)
        self.assertEqual(second['cursor']['frontier'],sha(5))
        third=self.discover(7,cursor=second['cursor'])
        self.assertEqual(third['walked'],[sha(7),sha(6)])
    def test_finished_history_not_reexamined_on_quiet_wake(self):
        self.commit(2,7);first=self.discover(2);self.api.calls.clear()
        self.discover(2,cursor=first['cursor']);self.assertFalse(self.api.calls)
    def test_merge_author_requires_bot_type_and_exact_main(self):
        for actor,base in [({'login':'owner','type':'User'},'main'),
                           ({'login':'github-actions[bot]','type':'User'},'main'),
                           ({'login':'github-actions[bot]','type':'Bot'},'topic')]:
            self.commit(2,7);self.api.records['pulls/7']['merged_by']=actor
            self.api.records['pulls/7']['base']['ref']=base
            self.assertFalse(self.discover(2)['candidates'])
    def test_associated_future_merge_is_not_selected_early(self):
        self.commit(2,7);self.api.records['pulls/7']['merge_commit_sha']=sha(9)
        self.assertFalse(self.discover(2)['candidates'])
    def test_bad_association_does_not_advance_cursor_or_erase_other_commits(self):
        self.commit(3,8);self.commit(2,7);del self.api.records['pulls/7']
        result=self.discover(3)
        self.assertEqual([x['number'] for x in result['candidates']],[8])
        self.assertEqual(result['cursor']['next_commit'],sha(2));self.assertTrue(result['unresolved'])
    def test_later_association_page_is_required_before_progress(self):
        self.commit(2)
        self.api.records['commits/'+sha(2)+'/pulls?per_page=100&page=1']=[{'id':i,'number':i} for i in range(1,101)]
        result=self.discover(2)
        self.assertFalse(result['walked']);self.assertEqual(result['cursor']['next_commit'],sha(2))
    def test_nonfirst_parent_history_is_not_walked(self):
        self.commit(3,7,parent=1);self.api.records['git/commits/'+sha(3)]['parents'].append({'sha':sha(2)})
        self.assertEqual(self.discover(3)['walked'],[sha(3)])
        self.assertNotIn('git/commits/'+sha(2),self.api.calls)
    def test_foreign_or_malformed_cursor_rejected(self):
        good=self.discover(1)['cursor']
        for key,value in [('repository','fork/repo'),('activation_commit',sha(9)),('frontier','main'),('scan_head',sha(2))]:
            bad=copy.deepcopy(good);bad[key]=value
            with self.assertRaises(ValueError):self.discover(1,cursor=bad)
    def test_changed_ancestry_stops_before_any_discovery(self):
        self.ancestry.side_effect=ValueError('untrusted ancestry')
        with self.assertRaises(ValueError):self.discover(2)
        self.assertFalse(self.api.calls)
    def test_root_before_frontier_is_retained_as_unresolved(self):
        self.commit(2);self.api.records['git/commits/'+sha(2)]['parents']=[]
        result=self.discover(2);self.assertFalse(result['enumeration_complete']);self.assertFalse(result['walked'])
    def test_bound_and_hash_validation(self):
        for bound in (0,101,True):
            with self.assertRaises(ValueError):self.discover(1,max_commits=bound)

if __name__=='__main__':unittest.main()

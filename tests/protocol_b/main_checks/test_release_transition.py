import copy, unittest
from release_transition import release_transition

class ReadAPI:
    def __init__(self,records):self.records=records;self.calls=[]
    def json(self,path):self.calls.append(path);return copy.deepcopy(self.records[path])

class ReleaseTransition(unittest.TestCase):
    def setUp(self):
        self.merge='a'*40;self.parent='b'*40
        self.records={
          'git/commits/'+self.merge:{'sha':self.merge,'tree':{'sha':'c'*40},'parents':[{'sha':self.parent},{'sha':'d'*40}]},
          'git/commits/'+self.parent:{'sha':self.parent,'tree':{'sha':'e'*40}},
          'git/trees/'+'c'*40:self.tree('c','docs','tree','040000','f'),
          'git/trees/'+'e'*40:self.tree('e','docs','tree','040000','1'),
          'git/trees/'+'f'*40:self.tree('f','current-manuscript.json','blob','100644','2'),
          'git/trees/'+'1'*40:self.tree('1','current-manuscript.json','blob','100644','3')}
        self.api=ReadAPI(self.records)
    def tree(self,sha,path,kind,mode,child):
        return {'sha':sha*40,'truncated':False,'tree':[{'path':path,'type':kind,'mode':mode,'sha':child*40}]}
    def result(self):
        result=release_transition(self.api,self.merge)
        self.assertFalse(result['dispatch_authorized']);self.assertTrue(all(p.startswith('git/') for p in self.api.calls))
        return result
    def test_changed_manifest_requires_exact_merge(self):
        r=self.result();self.assertTrue(r['exact_release_required']);self.assertEqual(r['first_parent'],self.parent)
    def test_unchanged_manifest_uses_blob_identity(self):
        self.records['git/trees/'+'f'*40]['tree'][0]['sha']='3'*40
        self.assertFalse(self.result()['exact_release_required'])
    def test_removed_manifest_is_not_treated_as_nonrelease(self):
        self.records['git/trees/'+'f'*40]['tree']=[]
        r=self.result();self.assertTrue(r['exact_release_required']);self.assertTrue(r['manifest_removed'])
    def test_added_manifest_requires_exact(self):
        self.records['git/trees/'+'1'*40]['tree']=[]
        self.assertTrue(self.result()['exact_release_required'])
    def test_complete_absence_on_both_sides(self):
        for key in ('c','e'):self.records['git/trees/'+key*40]['tree']=[]
        self.assertFalse(self.result()['exact_release_required'])
    def test_mode_change_is_conservative(self):
        row=self.records['git/trees/'+'f'*40]['tree'][0];row.update(sha='3'*40,mode='100755')
        self.assertTrue(self.result()['exact_release_required'])
    def test_one_parent_squash_is_supported(self):
        self.records['git/commits/'+self.merge]['parents']=[{'sha':self.parent}]
        self.assertTrue(self.result()['exact_release_required'])
    def test_root_or_octopus_is_ambiguous(self):
        for parents in ([],[{'sha':self.parent}]*3):
            self.records['git/commits/'+self.merge]['parents']=parents
            with self.assertRaisesRegex(ValueError,'ambiguous main'):self.result()
    def test_invalid_parent_identity(self):
        self.records['git/commits/'+self.merge]['parents'][0]['sha']='main'
        with self.assertRaisesRegex(ValueError,'Git identity'):self.result()
    def test_commit_identity_mismatch(self):
        self.records['git/commits/'+self.parent]['sha']='a'*40
        with self.assertRaisesRegex(ValueError,'commit identity'):self.result()
    def test_missing_request_is_not_absence(self):
        del self.records['git/trees/'+'f'*40]
        with self.assertRaises(KeyError):self.result()
    def test_truncation_refused_on_each_tree(self):
        for key in ('c','e','f','1'):
            value=self.records['git/trees/'+key*40];value['truncated']=True
            with self.assertRaisesRegex(ValueError,'incomplete'):self.result()
            value['truncated']=False
    def test_tree_identity_mismatch(self):
        self.records['git/trees/'+'f'*40]['sha']='0'*40
        with self.assertRaisesRegex(ValueError,'incomplete'):self.result()
    def test_symlink_and_submodule_refused(self):
        row=self.records['git/trees/'+'f'*40]['tree'][0]
        for kind,mode in [('blob','120000'),('commit','160000'),('tree','040000')]:
            row.update(type=kind,mode=mode)
            with self.assertRaisesRegex(ValueError,'regular file'):self.result()
    def test_directory_symlink_refused(self):
        self.records['git/trees/'+'c'*40]['tree'][0].update(type='blob',mode='120000')
        with self.assertRaisesRegex(ValueError,'directory'):self.result()
    def test_duplicate_paths_refused(self):
        value=self.records['git/trees/'+'f'*40];value['tree']*=2
        with self.assertRaisesRegex(ValueError,'ambiguous'):self.result()
    def test_nested_path_in_nonrecursive_tree_refused(self):
        self.records['git/trees/'+'f'*40]['tree'][0]['path']='bad/current-manuscript.json'
        with self.assertRaisesRegex(ValueError,'ambiguous'):self.result()
    def test_unrelated_file_does_not_change_classification(self):
        self.records['git/trees/'+'f'*40]['tree'].append({'path':'release-policy.md','type':'blob','mode':'100644','sha':'9'*40})
        self.assertTrue(self.result()['exact_release_required'])

if __name__=='__main__':unittest.main()

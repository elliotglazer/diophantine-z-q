import copy
import json
import unittest
from unittest.mock import patch
from deferred_source import validate_deferred_source, validate_deferred_chain


class DeferredSourceTests(unittest.TestCase):
    def setUp(self):
        head, merge = "a"*40, "b"*40
        self.args = ["owner/repo", 42,
            {"number": 7, "state": "closed", "merged": True, "head": {"sha": head},
             "merge_commit_sha": merge, "base": {"ref": "main", "repo": {"full_name": "owner/repo"}},
             "merged_by": {"login": "github-actions[bot]", "type": "Bot"}, "node_id": "PR_7"},
            {"id": 9, "name": "Protocol B / review", "head_sha": head, "status": "completed", "conclusion": "success",
             "app": {"id": 42}, "details_url": "https://github.com/owner/repo/actions/runs/123",
             "output": {"text": json.dumps({"schema": "protocol-b-decisions/v1", "head": head})}},
            {"id": 123, "repository": {"full_name": "owner/repo"}, "path": ".github/workflows/protocol-b.yml",
             "event": "issue_comment", "status": "completed", "run_attempt": 1},
            {"number": 7, "head": head, "check": 9, "conclusion": "success", "name": "Protocol B / review", "mode": "live"},
            {"number": 7, "head": head},
            {"data": {"enablePullRequestAutoMerge": {"pullRequest": {"id": "PR_7"}}}}]

    def refuse(self, index, key, value, reason):
        args = copy.deepcopy(self.args)
        args[index][key] = value
        result = validate_deferred_source(*args)
        self.assertEqual(result, {"eligible": False, "reason": reason, "operations": []})

    def test_confirmed_source_plans_two_main_operations_without_mutation(self):
        before = copy.deepcopy(self.args)
        result = validate_deferred_source(*self.args)
        self.assertTrue(result["eligible"])
        self.assertEqual([x["workflow"] for x in result["operations"]], ["research-checks.yml", "kernel-lean.yml"])
        self.assertEqual({x["ref"] for x in result["operations"]}, {"main"})
        self.assertEqual(self.args, before)

    def test_open_or_unconfirmed_merge_refused(self):
        for key, value in [("state", "open"), ("merged", False), ("merged", 1), ("merge_commit_sha", "b"*8), ("number", True)]:
            with self.subTest(key=key, value=value): self.refuse(2,key,value,"unconfirmed_merge")

    def test_wrong_repository_or_branch_refused(self):
        for base in [{"ref":"other", "repo":{"full_name":"owner/repo"}}, {"ref":"main", "repo":{"full_name":"fork/repo"}}]:
            self.refuse(2,"base",base,"wrong_base")

    def test_human_and_lookalike_actors_refused(self):
        for actor in [{"login":"owner","type":"User"}, {"login":"github-actions[bot]","type":"User"}, None]:
            self.refuse(2,"merged_by",actor,"not_workflow_merge")

    def test_wrong_app_missing_app_and_stale_head_refused(self):
        for key,value in [("app",None),("app",{"id":43}),("name","Protocol B / test review"),("head_sha","c"*40),
                          ("status","in_progress"),("conclusion","neutral")]:
            self.refuse(3,key,value,"no_exact_head_app_acceptance")

    def test_invalid_publisher_link_refused(self):
        for link in ["https://example.com/owner/repo/actions/runs/123", "https://github.com/owner/repo/actions/runs/123?x=1",
                     "https://github.com/fork/repo/actions/runs/123", "http://github.com/owner/repo/actions/runs/123"]:
            self.refuse(3,"details_url",link,"invalid_publisher_link")

    def test_unrelated_or_running_publisher_refused(self):
        for key,value in [("id",124),("path",".github/workflows/forged.yml"),("repository",{"full_name":"fork/repo"})]:
            self.refuse(4,key,value,"wrong_publisher")
        self.refuse(4,"status","in_progress","publisher_still_running")

    def test_stale_or_failed_original_decision_refused(self):
        for key,value in [("check",8),("head","c"*40),("number",8),("conclusion","failure"),("mode","test")]:
            self.refuse(5,key,value,"decision_mismatch")

    def test_missing_or_ambiguous_auto_merge_receipt_refused(self):
        self.refuse(7,"data",None,"auto_merge_request_unconfirmed")
        self.refuse(7,"errors",[{"message":"Unknown failure"}],"auto_merge_request_unconfirmed")
        self.refuse(6,"head","c"*40,"deferred_receipt_mismatch")

    def test_wrong_stored_app_head_refused(self):
        self.refuse(3,"output",{"text":json.dumps({"schema":"protocol-b-decisions/v1","head":"c"*40})},"invalid_app_record")


class PublicationChainTests(unittest.TestCase):
    def setUp(self):
        fixture = DeferredSourceTests()
        fixture.setUp()
        args = copy.deepcopy(fixture.args)
        self.repo, self.app_id, self.pr = args[:3]
        self.pr['merged_at'] = '2026-11-17T12:10:00Z'
        self.requester = dict(zip(('check','publisher','decision','deferred','auto_result'), args[3:]))
        self.requester['publisher']['created_at'] = '2026-11-17T12:00:00Z'
        self.accepted = copy.deepcopy(self.requester)
        self.accepted.pop('auto_result')
        self.accepted['publisher'].update(id=124, created_at='2026-11-17T12:05:00Z')
        self.accepted['check'].update(id=10,details_url='https://github.com/owner/repo/actions/runs/124')
        self.accepted['decision']['check'] = 10

    def result(self):
        return validate_deferred_chain(self.repo,self.app_id,self.pr,self.accepted,self.requester)

    def test_later_acceptance_retains_original_request_identity(self):
        result = self.result()
        self.assertTrue(result['eligible'])
        self.assertEqual(len(result['operations']),2)
        for operation in result['operations']:
            self.assertEqual(operation['publisher_run'],124)
            self.assertEqual(operation['requester_run'],123)
            self.assertEqual(operation['requester_check'],9)

    def test_no_invention_of_a_missing_original_receipt(self):
        self.requester.pop('auto_result')
        self.assertEqual(self.result()['reason'],'auto_merge_request_unconfirmed')

    def test_failed_or_stale_later_acceptance_cannot_inherit_an_old_success(self):
        for key,value in [('head_sha','c'*40),('conclusion','failure'),('app',None)]:
            with self.subTest(key=key), patch.dict(self.accepted['check'],{key:value}):
                self.assertFalse(self.result()['eligible'])

    def test_wrong_requester_identity_or_chronology_is_refused(self):
        with patch.dict(self.requester['decision'],{'number':8}):
            self.assertFalse(self.result()['eligible'])
        with patch.dict(self.requester['publisher'],{'created_at':'2026-11-17T12:11:00Z'}):
            self.assertEqual(self.result()['reason'],'publication_chronology')
        with patch.dict(self.pr,{'merged_at':None}):
            self.assertEqual(self.result()['reason'],'publication_chronology')

    def test_unmerged_pr_or_active_publisher_cannot_dispatch(self):
        with patch.dict(self.pr,{'merged':False}):
            self.assertFalse(self.result()['eligible'])
        with patch.dict(self.requester['publisher'],{'status':'in_progress'}):
            self.assertFalse(self.result()['eligible'])


if __name__ == "__main__": unittest.main()

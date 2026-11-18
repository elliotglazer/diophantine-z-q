import hashlib
import subprocess
import unittest
from unittest.mock import patch
from github_api import API, GitHubResponseError, response_parts
import test_dispatch_recovery as dispatcher_fixture


PATH = 'actions/workflows/kernel-lean.yml/dispatches'
BODY = {'ref': 'main', 'return_run_details': True}


class TransportResponses(unittest.TestCase):
    def test_status_and_request_id_survive_without_arbitrary_headers(self):
        body = b'{"message":"Invalid request"}'
        wire = (b'HTTP/2.0 422 Unprocessable Entity\r\nX-GitHub-Request-Id: ABC:123\r\n'
                b'Set-Cookie: not-retained\r\nAuthorization: not-retained\r\n\r\n' + body)
        with patch('github_api.subprocess.run', return_value=subprocess.CompletedProcess([], 1, wire)) as call:
            with self.assertRaises(GitHubResponseError) as caught:
                API('owner/repo').post_once(PATH, BODY)
        self.assertEqual(call.call_count, 1)
        self.assertIn('--include', call.call_args.args[0])
        self.assertEqual(caught.exception.response_evidence, {
            'http_status': 422, 'request_id': 'ABC:123', 'api_message': 'Invalid request',
            'response_sha256': hashlib.sha256(body).hexdigest()})
        self.assertNotIn('not-retained', str(caught.exception.response_evidence))

    def test_lf_headers_and_empty_success_are_accepted(self):
        with patch('github_api.subprocess.run', return_value=subprocess.CompletedProcess([], 0,
                b'HTTP/1.1 204 No Content\nX-GitHub-Request-Id: A\n\n')) as call:
            self.assertIsNone(API('owner/repo').post_once(PATH, BODY))
        self.assertEqual(call.call_count, 1)

    def test_missing_or_malformed_status_cannot_be_called_a_success(self):
        for wire in (b'{"workflow_run_id":9}', b'HTTP/2.0 200 OK', b'HTTP/2.0 999 Unknown\n\n{}'):
            with self.subTest(wire=wire), patch('github_api.subprocess.run',
                    return_value=subprocess.CompletedProcess([], 0, wire)) as call:
                with self.assertRaises(GitHubResponseError) as caught:
                    API('owner/repo').post_once(PATH, BODY)
                self.assertIsNone(caught.exception.response_evidence['http_status'])
                self.assertEqual(call.call_count, 1)

    def test_non_success_status_is_retained_even_if_cli_exit_is_zero(self):
        with patch('github_api.subprocess.run', return_value=subprocess.CompletedProcess([], 0,
                b'HTTP/2.0 503 Service Unavailable\n\nupstream unavailable')):
            with self.assertRaises(GitHubResponseError) as caught:
                API('owner/repo').post_once(PATH, BODY)
        self.assertEqual(caught.exception.response_evidence['http_status'], 503)

    def test_timeout_is_never_retried(self):
        with patch('github_api.subprocess.run', side_effect=subprocess.TimeoutExpired('gh', 120)) as call:
            with self.assertRaises(subprocess.TimeoutExpired):
                API('owner/repo').post_once(PATH, BODY)
        self.assertEqual(call.call_count, 1)

    def test_get_binary_transport_is_unchanged(self):
        wire = b'PK\x03\x04\x00artifact\r\n\r\n'
        with patch('github_api.subprocess.run', return_value=subprocess.CompletedProcess([], 0, wire)) as call:
            self.assertEqual(API('owner/repo').bytes('actions/artifacts/9/zip'), wire)
        self.assertNotIn('--include', call.call_args.args[0])

    def test_message_is_bounded_and_non_json_body_is_not_copied(self):
        import json
        error = GitHubResponseError('POST', 422, {}, json.dumps({'message': 'x'*2000}).encode())
        self.assertEqual(len(error.response_evidence['api_message']), 1000)
        error = GitHubResponseError('POST', 502, {}, b'<html>large proxy response</html>')
        self.assertEqual(set(error.response_evidence), {'http_status', 'response_sha256'})

    def test_http_failure_receipts_keep_unknown_effect_and_never_retry(self):
        for status in (400, 401, 403, 404, 409, 422, 429, 500, 502):
            with self.subTest(status=status):
                case = dispatcher_fixture.Dispatcher()
                case.setUp()
                try:
                    def reject(path, body):
                        case.check_saved_boundary(path, body)
                        case.api.posts.append((path, body))
                        raise GitHubResponseError('POST', status, {'x-github-request-id': 'R'},
                                                  b'{"message":"request failed"}')
                    case.api.post_once = reject
                    result = case.run_dispatch()
                    self.assertEqual(len(case.api.posts), 2)
                    self.assertEqual(len({path for path, _ in case.api.posts}), 2)
                    for receipt in result['receipts']:
                        self.assertEqual(receipt['status'], 'effect_needs_reconciliation')
                        self.assertIsNone(receipt['request_sent'])
                        self.assertEqual(receipt['response_evidence']['http_status'], status)
                        self.assertEqual(receipt['response_evidence']['request_id'], 'R')
                finally:
                    case.doCleanups()


if __name__ == '__main__':
    unittest.main()

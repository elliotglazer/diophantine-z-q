"""GitHub CLI transport with one process invocation per request and no write retry."""
import json
import hashlib
import re
import subprocess
from urllib.parse import unquote


class GitHubResponseError(RuntimeError):
    """Retain response evidence without classifying a failed write as absent."""
    def __init__(self, method, status, headers, body):
        self.response_evidence = {
            'http_status': status,
            'response_sha256': hashlib.sha256(body).hexdigest(),
        }
        request_id = headers.get('x-github-request-id')
        if request_id:
            self.response_evidence['request_id'] = request_id[:200]
        try:
            message = json.loads(body).get('message')
            if isinstance(message, str):
                self.response_evidence['api_message'] = message[:1000]
        except (ValueError, AttributeError, UnicodeError):
            pass
        super().__init__('GitHub '+method+' failed'+
                         (' with HTTP '+str(status) if status is not None else '')+
                         '; inspect the retained operation, do not infer absence')


def response_parts(raw):
    """Parse gh --include output; unrecognized output proves no response status."""
    marker = b'\r\n\r\n' if b'\r\n\r\n' in raw else b'\n\n'
    header, separator, body = raw.partition(marker)
    lines = header.splitlines()
    match = re.fullmatch(rb'HTTP/[0-9.]+ ([1-5][0-9]{2})(?: .*)?', lines[0]) if lines else None
    if not separator or not match:
        return None, {}, raw
    headers = {}
    for line in lines[1:]:
        name, colon, value = line.partition(b':')
        if colon and name.lower() == b'x-github-request-id':
            headers['x-github-request-id'] = value.strip().decode('ascii', errors='replace')
    return int(match.group(1)), headers, body


class API:
    def __init__(self, repository):
        if re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository) is None:
            raise ValueError('Invalid repository identity')
        self.repository=repository
    def _call(self,path,method='GET',data=None):
        if (not isinstance(path,str) or path.startswith('/') or any(x in path for x in ('\\','\n','\r'))
                or ':' in path.split('?',1)[0] or '..' in unquote(path.split('?',1)[0]).split('/')):
            raise ValueError('API path must stay in the selected repository')
        endpoint='repos/'+self.repository+('/'+path if path else '')
        args=['gh','api',endpoint,'-H','X-GitHub-Api-Version: 2026-03-10','--method',method]
        if method == 'POST': args.append('--include')
        raw=None
        if data is not None:
            args+=['--input','-'];raw=json.dumps(data,separators=(',',':')).encode()
        # No shell, no provider call, no token printed or passed on the command line.
        # A timed-out POST has an unknown effect and must never be called again here.
        result=subprocess.run(args,input=raw,capture_output=True,timeout=120,check=False)
        if method == 'POST':
            status, headers, body = response_parts(result.stdout)
            if result.returncode or status is None or not 200 <= status < 300:
                raise GitHubResponseError(method, status, headers, body)
            return body
        if result.returncode:
            raise RuntimeError('GitHub '+method+' failed; inspect the retained operation, do not infer absence')
        return result.stdout
    def require_rate_reserve(self,reserve=200):
        result=subprocess.run(['gh','api','rate_limit'],capture_output=True,timeout=30,check=False)
        if result.returncode:raise RuntimeError('Cannot read remaining GitHub request budget; no dispatch')
        value=json.loads(result.stdout).get('resources',{}).get('core',{})
        remaining=value.get('remaining')
        if type(remaining) is not int or remaining<reserve:
            raise RuntimeError('GitHub request budget below recovery reserve; no dispatch')
        return remaining
    def json(self,path):return json.loads(self._call(path))
    def bytes(self,path):return self._call(path)
    def post_once(self,path,data):
        if path not in ('actions/workflows/research-checks.yml/dispatches','actions/workflows/kernel-lean.yml/dispatches'):
            raise ValueError('Only the two main checks can be dispatched')
        if data!={'ref':'main','return_run_details':True}:
            raise ValueError('Main dispatch must request the actual run identity')
        raw=self._call(path,'POST',data)
        return json.loads(raw) if raw.strip() else None

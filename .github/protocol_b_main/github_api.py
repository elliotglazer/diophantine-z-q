"""GitHub CLI transport with one process invocation per request and no write retry."""
import json
import re
import subprocess
from urllib.parse import unquote


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
        raw=None
        if data is not None:
            args+=['--input','-'];raw=json.dumps(data,separators=(',',':')).encode()
        # No shell, no provider call, no token printed or passed on the command line.
        # A timed-out POST has an unknown effect and must never be called again here.
        result=subprocess.run(args,input=raw,capture_output=True,timeout=120,check=False)
        if result.returncode:
            raise RuntimeError('GitHub '+method+' failed; inspect the retained operation, do not infer absence')
        return result.stdout
    def json(self,path):return json.loads(self._call(path))
    def bytes(self,path):return self._call(path)
    def post_once(self,path,data):
        if path not in ('actions/workflows/research-checks.yml/dispatches','actions/workflows/kernel-lean.yml/dispatches'):
            raise ValueError('Only the two main checks can be dispatched')
        if data!={'ref':'main','return_run_details':True}:
            raise ValueError('Main dispatch must request the actual run identity')
        raw=self._call(path,'POST',data)
        return json.loads(raw) if raw.strip() else None

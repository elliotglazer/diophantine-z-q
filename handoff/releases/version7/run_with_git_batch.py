"""Run the unchanged packager with a persistent, hash-checked Git blob reader.

Only `git -C REPO cat-file blob OID` calls are batched. Every response is
checked against its Git object ID; all normal SHA-256 plan and ZIP checks run.
"""
import argparse,hashlib,json,re,runpy,subprocess,sys
from pathlib import Path

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path,required=True)
    parser.add_argument('script',type=Path)
    parser.add_argument('args',nargs=argparse.REMAINDER)
    options=parser.parse_args()
    original=subprocess.check_output
    processes={};count=0
    def output(command,*args,**kwargs):
        nonlocal count
        if not (isinstance(command,list) and len(command)==6 and command[1]=='-C'
                and command[3:5]==['cat-file','blob'] and not args and not kwargs):
            return original(command,*args,**kwargs)
        oid=command[5]
        if not re.fullmatch('[0-9a-f]{40}',oid):raise ValueError('Not a full Git object ID')
        repository=str(Path(command[2]).resolve())
        if repository not in processes:
            processes[repository]=subprocess.Popen([command[0],'-C',repository,'cat-file','--batch'],
                stdin=subprocess.PIPE,stdout=subprocess.PIPE)
        process=processes[repository]
        process.stdin.write(oid.encode()+b'\n');process.stdin.flush()
        header=process.stdout.readline().split()
        if len(header)!=3 or header[:2]!=[oid.encode(),b'blob']:raise ValueError('Unexpected Git response')
        size=int(header[2])
        if not 0<=size<=256*1024**2:raise ValueError('Unexpected blob size')
        raw=process.stdout.read(size)
        if len(raw)!=size or process.stdout.read(1)!=b'\n':raise ValueError('Truncated Git object')
        if hashlib.sha1(b'blob '+str(size).encode()+b'\0'+raw).hexdigest()!=oid:
            raise ValueError('Git object hash mismatch')
        count+=1
        return raw
    subprocess.check_output=output
    sys.argv=[str(options.script),*options.args]
    sys.path.insert(0,str(options.script.resolve().parent))
    success=False
    try:
        runpy.run_path(str(options.script),run_name='__main__')
        success=True
    finally:
        subprocess.check_output=original
        for process in processes.values():
            process.stdin.close()
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:process.kill();process.wait()
        options.record.write_text(json.dumps({'status':'PASS' if success else 'FAILED',
            'blobReads':count,'gitProcesses':len(processes),'everyGitObjectHashVerified':True,
            'packagerSourceSha256':hashlib.sha256(options.script.read_bytes()).hexdigest(),
            'runtimeAdapterSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2)+'\n')

if __name__=='__main__':main()

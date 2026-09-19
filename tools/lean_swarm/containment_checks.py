from pathlib import Path
import json,os,socket,subprocess,sys,time,uuid
sys.path.insert(0,str(Path(__file__).resolve().parent))
from runtime import Controller,atomic_json
from state import Store
import argparse
parser=argparse.ArgumentParser(description='Local cgroup fault check; no real model calls.')
parser.add_argument('--config',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
R=args.output.resolve();R.mkdir(parents=True,exist_ok=False)
s=Store(R/'control.sqlite3');cfg=json.loads(args.config.read_text())
project='containment-'+uuid.uuid4().hex;s.init_project(project,cfg);c=Controller(s,R,project)
probe=R/'probe.py';probe.write_text('''import os,time,sys
from pathlib import Path
r=Path(sys.argv[1])
if os.fork()==0:
 os.setsid()
 if os.fork()==0:
  (r/'descendant.pid').write_text(str(os.getpid()))
  while True:
   (r/'candidate.lean').write_text('tick '+str(time.time()));time.sleep(.03)
 os._exit(0)
time.sleep(60)
''')
def start(work):
 work.mkdir();unit='lean-swarm-'+uuid.uuid4().hex+'.service'
 subprocess.run(['sudo','-n','systemd-run','--quiet','--unit='+unit,'--service-type=exec','-p','User='+str(os.getuid()),'-p','Group='+str(os.getgid()),'-p','KillMode=control-group','-p','RuntimeMaxSec=30','-p','NoNewPrivileges=yes','-p','ProtectSystem=strict','-p','ReadWritePaths='+str(work),'/usr/bin/python3',str(probe),str(work)],check=True)
 end=time.monotonic()+5
 while not (work/'descendant.pid').exists():
  assert time.monotonic()<end;time.sleep(.05)
 return unit

def inactive(work):
 pid=int((work/'descendant.pid').read_text());p=Path('/proc')/str(pid)/'stat'
 return not p.exists() or p.read_text().rsplit(') ',1)[1][0]=='Z'

w=R/('freeze-'+uuid.uuid4().hex);u=start(w)
try:
 capture=c._freeze_capture(u,w/'candidate.lean',R/'snapshot.lean')
 first=(w/'candidate.lean').read_bytes();time.sleep(.2)
 assert first==(w/'candidate.lean').read_bytes() and first==(R/'snapshot.lean').read_bytes()
 stop=c._stop_unit(u);time.sleep(.2);assert inactive(w)
 assert first==(w/'candidate.lean').read_bytes()
 print('PASS freeze_snapshot_detached_descendant_shutdown',flush=True)
finally:c._stop_unit(u)

payload={'id':'orphan','model':'luna','depends_on':[],'source':'test','target_name':'Demo.test','target_path':'tests/Test.lean'}
s.add_tasks(project,[payload]);claim=s.claim(project,socket.gethostname()+':999999999:0')
w2=R/('recover-'+uuid.uuid4().hex);u2=start(w2)
s.record_runtime(claim['attempt_id'],{'unit':u2,'workspace':str(w2)})
try:
 recovered=c.recover();assert recovered==['orphan'];assert inactive(w2)
 assert s.list_tasks(project)[0]['status']=='INTERRUPTED'
 s.retry(project,'orphan');retry=s.claim(project,'self-test-retry');assert retry
 s.finish(retry['attempt_id'],'FAILED',{'test_only':True})
 print('PASS dead_dispatcher_recovery_stops_real_execution_before_retry',flush=True)
finally:c._stop_unit(u2)
atomic_json(R/'result.json',{'freeze_snapshot_no_late_writes':True,'detached_descendant_stopped':True,'dead_owner_recovery_stops_execution_before_retry':True,'candidate_snapshot_sha256':capture['sha256'],'active_real_models_used':False})
print('LIVE_CHECKS_COMPLETE',flush=True)

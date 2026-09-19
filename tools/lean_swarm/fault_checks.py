from pathlib import Path
import json,os,sys,time,uuid
sys.path.insert(0,str(Path(__file__).resolve().parent))
from runtime import Controller,atomic_json,BEGIN,END
from state import Store
import argparse
parser=argparse.ArgumentParser(description='Local cgroup fault check; no real model calls.')
parser.add_argument('--config',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
R=args.output.resolve();R.mkdir(parents=True,exist_ok=False)
fake=R/'fake_codex.py'
fake.write_text('''#!/usr/bin/python3
import os,time,json
from pathlib import Path
p=Path.cwd()/'tests/Swarm/TimeoutProbe.lean'
s=p.read_text().replace('  sorry','  trivial')
if os.fork()==0:
 os.setsid()
 if os.fork()==0:
  (Path.cwd()/'.detached.pid').write_text(str(os.getpid()))
  while True:
   p.write_text(s.replace('  trivial','  trivial -- '+str(time.time())))
   time.sleep(.03)
 os._exit(0)
time.sleep(60)
''');fake.chmod(0o755)
cfg=json.loads(args.config.read_text());cfg['codex']=str(fake)
s=Store(R/'test.sqlite3');s.init_project('timeout-fault',cfg)
task={'id':'timeout','model':'luna','depends_on':[],'source':'import Mathlib\nnamespace TimeoutProbe\ntheorem target : True :=\n'+BEGIN+'\nby\n  sorry\n'+END+'\nend TimeoutProbe\n','target_name':'TimeoutProbe.target','target_path':'tests/Swarm/TimeoutProbe.lean','timeout_seconds':5}
s.add_tasks('timeout-fault',[task]);c=Controller(s,R,'timeout-fault');rows=c.run(jobs=1)
a=s.list_attempts('timeout-fault')[0];assert rows[0]['status']=='TIMEOUT',rows
assert a['result']['capture']['frozen_before_capture']
work=Path(a['metadata']['workspace']);candidate=work/'PoincareConjecture/tests/Swarm/TimeoutProbe.lean';frozen=R/'attempts'/a['id']/'frozen.lean'
assert frozen.read_bytes()==candidate.read_bytes();time.sleep(.3);assert frozen.read_bytes()==candidate.read_bytes()
assert not a['result']['containment']['cgroup_populated']
s.retry('timeout-fault','timeout');claim=s.claim('timeout-fault','fault-test');assert claim;s.finish(claim['attempt_id'],'FAILED',{'no_execution':'test ended'})
report={'status':'PASS','timeout_state':'TIMEOUT','frozen_before_capture':True,'no_writes_after_capture':True,'detached_process_group_empty':True,'slot_reusable_only_after_stop':True,'real_model_calls':0,'attempt_seconds':a['result']['elapsed_seconds']}
atomic_json(R/'report.json',report)
print(json.dumps(report,indent=2),flush=True)

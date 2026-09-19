from pathlib import Path
import json,re,os,subprocess,concurrent.futures,time,sys,hashlib
import argparse
parser=argparse.ArgumentParser(description='Compile the exact reference import closure used by ParallelMath adapters; no model calls.')
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--config',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--cached-objects',type=Path)
parser.add_argument('--extra-module',action='append',default=[],help='Additional pinned reference input module; may be repeated')
args=parser.parse_args()
R=args.repo.resolve();O=args.output.resolve();O.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(R/'tools/lean_swarm'));from runtime import seed_artifact_namespace,detach_object_links
cfg=json.loads(args.config.read_text())
env=dict(os.environ,PATH=cfg['lean_bin']+':'+os.environ['PATH'])
basepath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R/'PoincareConjecture',env=env,text=True).strip()
old=args.cached_objects.resolve() if args.cached_objects else O/'unused-cache';out=O/'reference-objects';out.mkdir(exist_ok=True);logs=O/'reference-logs';logs.mkdir(exist_ok=True)
baseline=str(old)+':'+basepath
roots={'MorganTianLib':R/'formalized-sources/MorganTian','DoCarmoLib':R/'formalized-sources/DoCarmo','Shared':R/'shared','HatcherLib':R/'formalized-sources/Hatcher'}
for ns in roots:seed_artifact_namespace(out,ns+'/Probe.lean',baseline)
G={};S={}
def inspect(m):
 if m in G:return
 p=roots[m.split('.')[0]]/Path(*m.split('.')).with_suffix('.lean');assert p.exists(),str(p)
 deps=[]
 for l in p.read_text().splitlines():
  a=re.match(r'^(?:public\s+)?import\s+(.+)',l)
  if a:
   deps.extend(d for d in a.group(1).split('--')[0].split() if d.split('.')[0] in roots)
 G[m]=deps;S[m]=p
 for d in deps:inspect(d)
targets=['MorganTianLib.Ch02.ForwardDifference','MorganTianLib.Ch03.RicciFlow.EvolvingEpsilonNeck','HatcherLib.Ch1.Circle','HatcherLib.Ch1.Sphere','Shared.MetricGeometry.LengthSpace']
targets += args.extra_module
for t in targets:inspect(t)
(O/'reference-graph.json').write_text(json.dumps(G,indent=2))
env['LEAN_PATH']=str(out)+':'+basepath;env['LEAN_NUM_THREADS']='2'
results={};done=set();pending=set(G);started=time.monotonic()
def build(m):
 src=S[m];sha=hashlib.sha256(src.read_bytes()).hexdigest();rel=Path(*m.split('.'));dest=(out/rel).with_suffix('.olean');oldfile=(old/rel).with_suffix('.olean');stamp=oldfile.with_suffix('.source-sha256')
 if oldfile.exists() and stamp.exists() and stamp.read_text()==sha:
  return {'module':m,'exit_code':0,'cached':True,'sha256':sha}
 dest.parent.mkdir(parents=True,exist_ok=True);detach_object_links(dest)
 t=time.monotonic();options=[] if m.startswith('HatcherLib.') else ['-Dbackward.isDefEq.respectTransparency=false','-DsynthInstance.maxHeartbeats=400000']
 t=time.monotonic();v=subprocess.run([cfg['lean_bin']+'/lean','-j2',*options,'-DautoImplicit=false','-o',str(dest),str(src)],cwd=roots[m.split('.')[0]],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
 (logs/(m+'.log')).write_text(v.stdout)
 if v.returncode:print('BUILD_FAIL',m,v.stdout[-2200:],flush=True)
 return {'module':m,'exit_code':v.returncode,'cached':False,'sha256':sha,'seconds':round(time.monotonic()-t,3)}
print('REFERENCE_INPUT_CLOSURE',len(G),'modules',flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 active={}
 while pending or active:
  ready=sorted(m for m in pending if set(G[m])<=done)
  for m in ready[:max(0,4-len(active))]:active[pool.submit(build,m)]=m;pending.remove(m)
  if not active:raise RuntimeError('dependency graph stalled')
  finished,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in finished:
   m=active.pop(f);r=f.result();results[m]=r
   if r['exit_code']:raise SystemExit('STOPPED_ON_REFERENCE_BUILD_FAILURE')
   done.add(m)
   if len(done)%25==0 or len(done)==len(G):print('REFERENCE_PROGRESS',len(done),'/',len(G),flush=True)
report={'status':'PASS','targets':targets,'source_modules':len(G),'results':results,'seconds':round(time.monotonic()-started,2)}
(O/'reference-build-report.json').write_text(json.dumps(report,indent=2))
cfg['lean_path']=str(out)+':'+basepath;cfg['min_available_memory_mb']=8192
(O/'swarm.references.local.json').write_text(json.dumps(cfg,indent=2))
cfg['lean_path']=basepath;(O/'swarm.main.local.json').write_text(json.dumps(cfg,indent=2))
print('REFERENCE_INPUTS_READY',flush=True)

"""Build only the reference epsilon-neck import closure into a private object directory."""
from pathlib import Path
import json,re,os,subprocess,concurrent.futures,time,hashlib,argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--config',required=True,type=Path)
parser.add_argument('--output',required=True,type=Path)
parser.add_argument('--check-adapters',action='store_true')
args=parser.parse_args();cfg=json.loads(args.config.read_text());R=Path(cfg['repo'])
root=args.output.resolve();out=root/'objects';logs=root/'logs';out.mkdir(parents=True,exist_ok=True);logs.mkdir(exist_ok=True)
roots={'MorganTianLib':R/'formalized-sources/MorganTian','DoCarmoLib':R/'formalized-sources/DoCarmo','Shared':R/'shared'}
graph={};sources={}
def inspect(m):
 if m in graph:return
 path=roots[m.split('.')[0]]/Path(*m.split('.')).with_suffix('.lean');assert path.exists(),str(path)
 deps=[]
 for line in path.read_text().splitlines():
  a=re.match(r'^(?:public\s+)?import\s+(.+)',line)
  if a:
   for d in a.group(1).split('--')[0].split():
    if d.split('.')[0] in roots:deps.append(d)
 graph[m]=deps;sources[m]=path
 for d in deps:inspect(d)
inspect('MorganTianLib.Ch02.EpsilonNeck')
(root/'dependency-graph.json').write_text(json.dumps(graph,indent=2))
print('REFERENCE_DEPENDENCY_MODULES',len(graph),flush=True)
# A cache generation is tied to the entire local source closure and compiler.
version=subprocess.check_output([cfg['lean_bin']+'/lean','--version'],text=True).strip()
expected=(R/'PoincareConjecture/lean-toolchain').read_text().strip().rsplit(':v',1)[1]
assert 'version '+expected+',' in version,'unexpected Lean toolchain'
source_hashes={m:hashlib.sha256(p.read_bytes()).hexdigest() for m,p in sources.items()}
identity={'lean':version,'source_hashes':source_hashes,
          'mathlib_revision':subprocess.check_output(['git','-C',str(Path(cfg['mathlib_source']).parent),'rev-parse','HEAD'],text=True).strip()}
pin=json.loads((R/'PoincareConjecture/lake-manifest.json').read_text())
mathlib=next(x for x in pin['packages'] if x['name']=='mathlib')
assert identity['mathlib_revision']==mathlib['rev'],'unexpected Mathlib revision'
manifest=root/'source-generation.json'
if manifest.exists():
    assert json.loads(manifest.read_text())==identity,'Source generation changed: choose a new output directory; old evidence was retained'
else:
    prior=root/'build-report.json'
    if prior.exists():
        old=json.loads(prior.read_text()).get('results',{})
        assert all(old.get(m,{}).get('sha256')==h for m,h in source_hashes.items()),'Prior cache does not match the full current source closure; choose a new directory'
    manifest.write_text(json.dumps(identity,indent=2)+'\n')
env=dict(os.environ,LEAN_PATH=str(out)+':'+cfg['lean_path'],LEAN_NUM_THREADS='2')
completed=set();pending=set(graph);results={};start=time.monotonic()
def compile_module(m):
 target=out/Path(*m.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 sha=hashlib.sha256(sources[m].read_bytes()).hexdigest()
 stamp=target.with_suffix('.source-sha256')
 if target.exists() and stamp.exists() and stamp.read_text()==sha:
  return {'module':m,'exit_code':0,'cached':True,'sha256':sha,'seconds':0}
 t=time.monotonic()
 cmd=[cfg['lean_bin']+'/lean','-j2','-Dbackward.isDefEq.respectTransparency=false','-DsynthInstance.maxHeartbeats=400000','-DautoImplicit=false','-o',str(target),str(sources[m])]
 v=subprocess.run(cmd,cwd=roots[m.split('.')[0]],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
 (logs/(m+'.log')).write_text(v.stdout)
 r={'module':m,'exit_code':v.returncode,'cached':False,'sha256':sha,'seconds':round(time.monotonic()-t,2)}
 if v.returncode==0:stamp.write_text(sha)
 else:print('REFERENCE_BUILD_FAILURE',m,v.stdout[-3000:],flush=True)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
 active={}
 while pending or active:
  ready=sorted(m for m in pending if set(graph[m])<=completed)
  for m in ready[:max(0,3-len(active))]:
   active[pool.submit(compile_module,m)]=m;pending.remove(m)
  if not active:raise RuntimeError('reference dependency cycle')
  done,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in done:
   m=active.pop(f)
   try:r=f.result()
   except Exception as exc:r={'module':m,'exit_code':-1,'error':str(exc)}
   results[m]=r
   if r['exit_code']:
    (root/'build-report.json').write_text(json.dumps({'status':'FAIL','results':results},indent=2));raise SystemExit('Reference check stopped on dependency failure')
   completed.add(m)
   if len(completed)%20==0 or len(completed)==len(graph):print('REFERENCE_CHECKED',len(completed),'/',len(graph),flush=True)
(root/'build-report.json').write_text(json.dumps({'status':'PASS','target':'MorganTianLib.Ch02.EpsilonNeck','modules':len(graph),'seconds':round(time.monotonic()-start,2),'results':results},indent=2))
print('REFERENCE_SOURCE_IMPORT_READY',flush=True)

assert source_hashes=={m:hashlib.sha256(p.read_bytes()).hexdigest() for m,p in sources.items()},'Reference sources changed during build'
if args.check_adapters:
    from runtime import parse_axioms
    targets=[('ReferenceShapes.lean','native_neck_reference_shapes'),
             ('MorganTianBridge.lean','reference_epsilonNeckStructure_smoothCollar')]
    evidence=[]
    for filename,target in targets:
        src=R/'PoincareConjecture/tests/NeckAdapter'/filename
        text=src.read_text();qualified='PoincareConjecture.Topology.FiberSaturation.SmoothNeck.'+target
        audit=root/('Audit_'+filename)
        audit.write_text(text+'\n#print axioms '+qualified+'\n')
        result=subprocess.run([cfg['lean_bin']+'/lean','-j2',str(audit)],cwd=root,env=env,
                              text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
        (logs/(filename+'.check.log')).write_text(result.stdout)
        assert result.returncode==0,result.stdout
        used=parse_axioms(result.stdout,qualified)
        evidence.append({'file':str(src.relative_to(R)),'target':qualified,'status':'PASS',
                         'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'axioms':used})
    (root/'adapter-recheck.json').write_text(json.dumps({'status':'PASS','lean':version,'tasks':evidence,
        'reference_modules':len(graph),'model_calls':0},ensure_ascii=False,indent=2)+'\n')
    print('ACTUAL_REFERENCE_ADAPTERS_PASS',len(evidence),flush=True)

#!/usr/bin/env python3
"""Build/recheck the fixed inputs used by Transport proofs. No model calls.

Creates only a private build directory. Its config may contain local paths and
must not be committed. All checked proofs stay in the user's ordinary repo.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,required=True)
    parser.add_argument('--config',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--cached-objects',type=Path)
    args=parser.parse_args();repo=args.repo.resolve();out=args.output.resolve()
    out.mkdir(parents=True,exist_ok=True)
    command=[sys.executable,str(repo/'tools/lean_swarm/build_math_references.py'),
        '--repo',str(repo),'--config',str(args.config.resolve()),'--output',str(out/'references'),
        '--extra-module','MorganTianLib.Ch03.RicciFlow.DistanceVariation']
    if args.cached_objects:command.extend(['--cached-objects',str(args.cached_objects.resolve())])
    subprocess.run(command,check=True)
    cfg=json.loads((out/'references/swarm.references.local.json').read_text())
    sys.path.insert(0,str(repo/'tools/lean_swarm'))
    from runtime import seed_artifact_namespace,detach_object_links
    objects=out/'checked-inputs';objects.mkdir(exist_ok=True);baseline=cfg['lean_path']
    env=dict(os.environ,PATH=cfg['lean_bin']+':'+os.environ.get('PATH',''),
             LEAN_PATH=str(objects)+':'+baseline,LEAN_NUM_THREADS='2')
    checked=set();stack=set();records=[]
    def compile_input(module):
        if module in checked or not module.startswith('ReferenceBridges.'):return
        if module in stack:raise ValueError('reference-adapter import cycle: '+module)
        stack.add(module);relative=Path(*module.split('.')).with_suffix('.lean')
        source=repo/'PoincareConjecture'/relative
        for dep in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):compile_input(dep)
        seed_artifact_namespace(objects,str(relative),baseline)
        target=(objects/relative).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        detach_object_links(target)
        process=subprocess.run([cfg['lean_bin']+'/lean','-j2','-DmaxHeartbeats=800000',
            '-o',str(target),str(source)],cwd=repo/'PoincareConjecture',env=env,text=True,
            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
        (objects/(module+'.log')).write_text(process.stdout)
        if process.returncode:raise RuntimeError(module+' failed:\n'+process.stdout[-5000:])
        records.append({'module':module,'source':str(source.relative_to(repo)),
            'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'exit_code':0})
        checked.add(module);stack.remove(module)
    for module in ['ReferenceBridges.Quantitative.EpsilonSpeedComparison',
                   'ReferenceBridges.Quantitative.EpsilonMetricComparison',
                   'ReferenceBridges.ParallelMath.FiniteExtinctionObstruction']:
        compile_input(module)
    cfg['lean_path']=str(objects)+':'+baseline
    (out/'swarm.transport.local.json').write_text(json.dumps(cfg,indent=2)+'\n')
    (out/'input-checks.json').write_text(json.dumps(records,indent=2)+'\n')
    print('TRANSPORT_INPUTS_READY',out/'swarm.transport.local.json')
if __name__=='__main__':main()

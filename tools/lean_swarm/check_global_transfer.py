#!/usr/bin/env python3
"""Rebuild local transfer interfaces and independently check their frozen goals.

Requires a pinned reference cache prepared by build_math_references.py. Calls no
models and reads no authentication state. All new objects go to --output.
"""
from pathlib import Path
import argparse,json,os,re,subprocess,sys,hashlib

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',required=True,type=Path)
    parser.add_argument('--config',required=True,type=Path)
    parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args();repo=args.repo.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    sys.path.insert(0,str(repo/'tools/lean_swarm'))
    from runtime import seed_artifact_namespace,detach_object_links,checked
    cfg=json.loads(args.config.read_text());cfg['repo']=str(repo)
    cfg['package_dir']='PoincareConjecture';package=repo/cfg['package_dir']
    env=dict(os.environ,PATH=cfg['lean_bin']+':'+os.environ.get('PATH',''),LEAN_NUM_THREADS='2')
    base=cfg['lean_path'];objects=out/'local-objects'
    for ns in ['PoincareConjecture','ReferenceBridges']:
        seed_artifact_namespace(objects,ns+'/Seed.lean',base)
    env['LEAN_PATH']=str(objects)+':'+base
    seen=set();active=set();receipts=[]
    def build(module):
        if module in seen:return
        if module in active:raise ValueError('local dependency cycle: '+module)
        active.add(module)
        relative=Path(*module.split('.')).with_suffix('.lean');source=package/relative
        if not source.is_file():raise FileNotFoundError(source)
        for line in source.read_text().splitlines():
            found=re.match(r'^(?:public\s+)?import\s+(.+)',line)
            if found:
                for dependency in found.group(1).split('--')[0].split():
                    if dependency.startswith(('PoincareConjecture.','ReferenceBridges.')):build(dependency)
        target=(objects/relative).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        detach_object_links(target)
        log=checked([cfg['lean_bin']+'/lean','-j2','-DmaxHeartbeats=800000','-o',str(target),str(source)],cwd=package,env=env,timeout=180)
        (out/(module+'.log')).write_text(log)
        receipts.append({'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()})
        seen.add(module);active.remove(module)
        print('LOCAL_SOURCE_CHECKED',module,flush=True)
    # Explicitly rebuild the actual metric wrappers, never trust their old cached elaboration.
    build('ReferenceBridges.GlobalTransfer.Core')
    cfg['lean_path']=str(objects)+':'+base
    config=out/'swarm.global-transfer.local.json';config.write_text(json.dumps(cfg,indent=2)+'\n')
    (out/'local-source-build.json').write_text(json.dumps(receipts,indent=2)+'\n')
    cards=repo/'reports/parallel/global-transfer-mapreduce/canonical-tasks.json'
    if not cards.is_file():raise FileNotFoundError(cards)
    subprocess.run([sys.executable,str(repo/'tools/lean_swarm/verify_cards.py'),
        '--config',str(config),'--cards',str(cards),'--output',str(out/'target-recheck.json')],cwd=repo,env=env,check=True)
    for name in ['Sanity.lean','MetricSelectionSanity.lean']:
        source=repo/'reports/parallel/global-transfer-mapreduce'/name
        output=checked([cfg['lean_bin']+'/lean','-j2',str(source)],env=env,cwd=source.parent,timeout=180)
        (out/(name+'.log')).write_text(output)
    print('GLOBAL_TRANSFER_INDEPENDENT_CHECKS_PASS',flush=True)
if __name__=='__main__':main()

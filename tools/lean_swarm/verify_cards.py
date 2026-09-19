#!/usr/bin/env python3
"""Recheck integrated fixed-goal task files without calling any model."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,tempfile
from runtime import checked,reconstruct,parse_axioms,validate_task,seed_artifact_namespace,detach_object_links

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config',required=True,type=Path)
    parser.add_argument('--cards',required=True,type=Path,nargs='+')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();cfg=json.loads(args.config.read_text())
    package=Path(cfg['repo'])/cfg['package_dir'];env=dict(os.environ)
    env['PATH']=cfg['lean_bin']+':'+env.get('PATH','');env['LEAN_NUM_THREADS']='2'
    version=checked([cfg['lean_bin']+'/lean','--version']).strip()
    expected=(package/'lean-toolchain').read_text().strip().rsplit(':v',1)[1]
    assert 'version '+expected+',' in version,(version,expected)
    tasks={};order=[];visiting=set();seen=set()
    for path in args.cards:
        for task in json.loads(path.read_text()):
            validate_task(task);assert task['id'] not in tasks,'duplicate task ID';tasks[task['id']]=task
    def visit(task_id):
        assert task_id not in visiting,'dependency cycle'
        if task_id in seen:return
        visiting.add(task_id)
        for dep in tasks[task_id]['depends_on']:visit(dep)
        visiting.remove(task_id);seen.add(task_id);order.append(tasks[task_id])
    for task_id in tasks:visit(task_id)
    reports=[]
    with tempfile.TemporaryDirectory(prefix='lean-swarm-recheck-') as directory:
        artifacts=Path(directory);env['LEAN_PATH']=str(artifacts)+':'+cfg['lean_path']
        for task in order:
            src=package/task['target_path'];text=src.read_text();assert reconstruct(task['source'],text)==text
            seed_artifact_namespace(artifacts,task['target_path'],cfg['lean_path'])
            output=artifacts/Path(task['target_path']).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
            detach_object_links(output)
            checked([cfg['lean_bin']+'/lean','-j2','-DmaxHeartbeats=800000','-o',str(output),str(src)],env=env)
            audit=artifacts/('Audit_'+task['id'].replace('-','_')+'.lean')
            audit.write_text(text+'\n#print axioms '+task['target_name']+'\n')
            result=checked([cfg['lean_bin']+'/lean','-j2',str(audit)],env=env)
            axioms=parse_axioms(result,task['target_name'])
            reports.append({'id':task['id'],'target':task['target_name'],'path':task['target_path'],
                            'status':'PASS','sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'axioms':axioms})
            print('PASS',task['id'],flush=True)
    report={'status':'PASS','lean':version,'tasks':reports,'model_calls':0}
    if args.output:args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False,indent=2))
if __name__=='__main__':main()

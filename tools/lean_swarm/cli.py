#!/usr/bin/env python3
"""Local CLI; all production invocations share one per-user SQLite registry."""
from __future__ import annotations
import argparse,json,os
from pathlib import Path
import signal,sys
from state import Store
from runtime import Controller,validate_task
from policy import parse_limit, resolve_effort
STATE_ROOT=Path(os.environ.get('LEAN_SWARM_STATE_ROOT', str(Path.home()/'.local/state/lean-swarm')))

def model_limit(value: str) -> int:
    try:
        return parse_limit(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc

# Backward-compatible import used by old scripts.
grok_limit = model_limit

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('init');p.add_argument('project');p.add_argument('config',type=Path)
    p=sub.add_parser('enqueue');p.add_argument('project');p.add_argument('tasks',type=Path)
    p=sub.add_parser('run');p.add_argument('project');p.add_argument('--jobs',type=model_limit,default=0,help='unlimited (default), or an explicit worker budget')
    p.add_argument('--watch',action='store_true',help='Remain available for newly ready tasks until interrupted')
    p.add_argument('--handoff-root',type=Path,action='append',default=[],help='Observe/adopt existing research batch without restarting it')
    p.add_argument('--verification-plan',type=Path,help='Trusted research target mapping for parallel independent compilation')
    p.add_argument('--integrate',action='store_true',help='Commit checked new files to integration only')
    p=sub.add_parser('status');p.add_argument('project')
    p=sub.add_parser('limits');p.add_argument('--luna',type=model_limit,default=0);p.add_argument('--grok',type=model_limit,default=0,help='unlimited (default), 0, or a positive model cap')
    p=sub.add_parser('pause-model');p.add_argument('model',choices=['luna','grok']);p.add_argument('--reason',required=True)
    p=sub.add_parser('events');p.add_argument('project');p.add_argument('--after',type=int,default=0)
    p=sub.add_parser('resume-model');p.add_argument('model',choices=['luna','grok'])
    p=sub.add_parser('retry');p.add_argument('project');p.add_argument('task')
    p=sub.add_parser('recover');p.add_argument('project')
    p=sub.add_parser('integrate');p.add_argument('project');p.add_argument('task')
    p=sub.add_parser('reverify');p.add_argument('project');p.add_argument('task');p.add_argument('--reason',help='Explicit coordinator reason; original FAILED evidence and frozen hash remain checked')
    p=sub.add_parser('adopt');p.add_argument('project');p.add_argument('batch_root',type=Path)
    p=sub.add_parser('research-status');p.add_argument('project');p.add_argument('--poll',action='store_true')
    p=sub.add_parser('research-verify');p.add_argument('job_id');p.add_argument('targets',type=Path)
    p=sub.add_parser('research-approve');p.add_argument('job_id');p.add_argument('--manifest',required=True);p.add_argument('--reviewer',required=True);p.add_argument('--notes',required=True)
    p=sub.add_parser('research-integrated');p.add_argument('job_id');p.add_argument('commit')
    args=parser.parse_args();STATE_ROOT.mkdir(parents=True,exist_ok=True,mode=0o700);os.chmod(STATE_ROOT,0o700)
    store=Store(STATE_ROOT/'control.sqlite3')
    if args.command=='init':
        config=json.loads(args.config.read_text())
        required=['repo','integration_branch','package_dir','lean_bin','lean_path','mathlib_source','codex','grok']
        if any(k not in config for k in required):parser.error('missing config field; see README')
        if config['integration_branch'] in ('main','master','upstream/main'):parser.error('use a dedicated integration branch')
        resolve_effort({'model':'luna'},config)
        store.init_project(args.project,config);print('REGISTERED',args.project)
    elif args.command=='enqueue':
        tasks=json.loads(args.tasks.read_text())
        for task in tasks:validate_task(Store._task(task))
        store.add_tasks(args.project,tasks);print('ENQUEUED',len(tasks))
    elif args.command=='limits':
        store.set_limits(args.luna,args.grok);print('GLOBAL_MANAGED_LIMITS',json.dumps({'luna':'unlimited' if args.luna==0 else args.luna,'grok': 'unlimited' if args.grok == 0 else args.grok}))
    elif args.command=='pause-model':store.pause_model(args.model,args.reason)
    elif args.command=='events':print(json.dumps(store.list_events(after=args.after,project_id=args.project),ensure_ascii=False,indent=2))
    elif args.command=='resume-model':store.resume_model(args.model)
    elif args.command=='retry':store.retry(args.project,args.task)
    elif args.command=='status':
        print(json.dumps([{k:v for k,v in row.items() if k!='payload'} for row in store.list_tasks(args.project)],indent=2))
    elif args.command in ('adopt','research-status','research-verify','research-approve','research-integrated'):
        from research_queue import ResearchQueue
        queue=ResearchQueue(store,STATE_ROOT)
        if args.command=='adopt':result=queue.import_batch(args.project,args.batch_root)
        elif args.command=='research-status':
            if args.poll:queue.poll(args.project)
            result=queue.list_jobs(args.project)
        elif args.command=='research-verify':result=queue.verify(args.job_id,json.loads(args.targets.read_text()))
        elif args.command=='research-approve':result=queue.approve(args.job_id,args.manifest,args.reviewer,args.notes)
        else:result=queue.record_integrated(args.job_id,args.commit)
        print(json.dumps(result,ensure_ascii=False,indent=2))
    else:
        controller=Controller(store,STATE_ROOT,args.project)
        def interrupt(signum,frame):controller.stop.set()
        signal.signal(signal.SIGINT,interrupt);signal.signal(signal.SIGTERM,interrupt)
        if args.command=='run':
            if args.watch or args.handoff_root or args.verification_plan:
                from supervisor import Supervisor
                plan=json.loads(args.verification_plan.read_text()) if args.verification_plan else {}
                rows=Supervisor(controller,args.handoff_root,plan).run(args.jobs,args.integrate,args.watch)
            else:
                rows=controller.run(args.jobs,args.integrate)
            print(json.dumps([{k:v for k,v in row.items() if k!='payload'} for row in rows],indent=2))
            if any(r['status'] not in ('INTEGRATED','VERIFIED') for r in rows):return 2
        elif args.command=='recover':print(json.dumps(controller.recover()))
        elif args.command=='integrate':print(controller.integrate(args.task))
        elif args.command=='reverify':controller.reverify(args.task,args.reason)
    return 0

if __name__=='__main__':
    try:sys.exit(main())
    except (ValueError,RuntimeError,KeyError) as exc:print('ERROR:',exc,file=sys.stderr);sys.exit(1)

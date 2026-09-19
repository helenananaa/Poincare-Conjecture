#!/usr/bin/env python3
"""Local CLI; all production invocations share one per-user SQLite registry."""
from __future__ import annotations
import argparse,json,os
from pathlib import Path
import signal,sys
from state import Store
from runtime import Controller,validate_task
STATE_ROOT=Path.home()/'.local/state/lean-swarm'

def grok_limit(value: str) -> int:
    """Zero is the persistent no-quota sentinel; worker resource budgets remain separate."""
    if value.lower() in ("unlimited", "none"):
        return 0
    try:
        result = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("use unlimited, 0, or a positive integer") from exc
    if not 0 <= result < 2**63:
        raise argparse.ArgumentTypeError("use unlimited, 0, or a nonnegative SQLite integer")
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('init');p.add_argument('project');p.add_argument('config',type=Path)
    p=sub.add_parser('enqueue');p.add_argument('project');p.add_argument('tasks',type=Path)
    p=sub.add_parser('run');p.add_argument('project');p.add_argument('--jobs',type=int,default=4)
    p.add_argument('--integrate',action='store_true',help='Commit checked new files to integration only')
    p=sub.add_parser('status');p.add_argument('project')
    p=sub.add_parser('limits');p.add_argument('--luna',type=int,default=4);p.add_argument('--grok',type=grok_limit,default=0,help='unlimited (default), 0, or a positive model cap')
    p=sub.add_parser('resume-model');p.add_argument('model',choices=['luna','grok'])
    p=sub.add_parser('retry');p.add_argument('project');p.add_argument('task')
    p=sub.add_parser('recover');p.add_argument('project')
    p=sub.add_parser('integrate');p.add_argument('project');p.add_argument('task')
    p=sub.add_parser('reverify');p.add_argument('project');p.add_argument('task')
    args=parser.parse_args();STATE_ROOT.mkdir(parents=True,exist_ok=True,mode=0o700);os.chmod(STATE_ROOT,0o700)
    store=Store(STATE_ROOT/'control.sqlite3')
    if args.command=='init':
        config=json.loads(args.config.read_text())
        required=['repo','integration_branch','package_dir','lean_bin','lean_path','mathlib_source','codex','grok']
        if any(k not in config for k in required):parser.error('missing config field; see README')
        if config['integration_branch'] in ('main','master','upstream/main'):parser.error('use a dedicated integration branch')
        store.init_project(args.project,config);print('REGISTERED',args.project)
    elif args.command=='enqueue':
        tasks=json.loads(args.tasks.read_text())
        for task in tasks:validate_task(task)
        store.add_tasks(args.project,tasks);print('ENQUEUED',len(tasks))
    elif args.command=='limits':
        store.set_limits(args.luna,args.grok);print('GLOBAL_MANAGED_LIMITS',json.dumps({'luna':args.luna,'grok': 'unlimited' if args.grok == 0 else args.grok}))
    elif args.command=='resume-model':store.resume_model(args.model)
    elif args.command=='retry':store.retry(args.project,args.task)
    elif args.command=='status':
        print(json.dumps([{k:v for k,v in row.items() if k!='payload'} for row in store.list_tasks(args.project)],indent=2))
    else:
        controller=Controller(store,STATE_ROOT,args.project)
        def interrupt(signum,frame):controller.stop.set()
        signal.signal(signal.SIGINT,interrupt);signal.signal(signal.SIGTERM,interrupt)
        if args.command=='run':
            rows=controller.run(args.jobs,args.integrate)
            print(json.dumps([{k:v for k,v in row.items() if k!='payload'} for row in rows],indent=2))
            if any(r['status'] not in ('INTEGRATED','VERIFIED') for r in rows):return 2
        elif args.command=='recover':print(json.dumps(controller.recover()))
        elif args.command=='integrate':print(controller.integrate(args.task))
        elif args.command=='reverify':controller.reverify(args.task)
    return 0

if __name__=='__main__':
    try:sys.exit(main())
    except (ValueError,RuntimeError,KeyError) as exc:print('ERROR:',exc,file=sys.stderr);sys.exit(1)

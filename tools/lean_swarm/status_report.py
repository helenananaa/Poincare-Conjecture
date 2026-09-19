#!/usr/bin/env python3
"""Read-only queue and concurrency report; no agents, no claims, no state changes."""
from pathlib import Path
import argparse,collections,json,sqlite3,time

def summarize(tasks,attempts,now=None):
    now=time.time() if now is None else now
    by_id={(t['project_id'],t['task_id']):t for t in tasks}
    projects={}
    for t in tasks:
        p=projects.setdefault(t['project_id'],{'states':{},'ready':[],'blocked':[]})
        p['states'][t['status']]=p['states'].get(t['status'],0)+1
        if t['status']=='QUEUED':
            deps=json.loads(t['payload_json']).get('depends_on',[])
            missing=[d for d in deps if by_id.get((t['project_id'],d),{}).get('status')!='INTEGRATED']
            p['blocked' if missing else 'ready'].append({'id':t['task_id'],'waiting_for':missing})
    active=[];intervals=[]
    for a in attempts:
        r=json.loads(a['result_json']);m=json.loads(a['metadata_json'])
        phase=r.get('timing',{})
        if not phase and m.get('folder'):
            f=Path(m['folder'])/'timing.json'
            if f.is_file():
                try:phase=json.loads(f.read_text())
                except (OSError,json.JSONDecodeError):phase={}
        start=phase.get('service_started_unix');end=phase.get('service_stopped_unix')
        if a['status']=='RUNNING':
            active.append({'project':a['project_id'],'task':a['task_id'],'reserved_seconds':round(now-a['started_at'],1),
                'phase':'preparing' if start is None else 'agent_or_capture' if end is None else 'verifying',
                'unit':m.get('unit')})
        if start is not None and end is not None:intervals.append((start,end))
    events=sorted([(s,1) for s,e in intervals]+[(e,-1) for s,e in intervals])
    count=peak=0
    for _,delta in events:count+=delta;peak=max(peak,count)
    return {'generated_unix':now,'projects':projects,'active_managed_attempts':active,
        'new_instrumented_completed_service_interval_peak':peak,
        'completed_intervals_with_new_timing':len(intervals),
        'notes':'RUNNING reservations are not simultaneous model inference. Phase is derived from controller records, not live systemd inspection. Old runs lack exact service timing. External/manual/scout sessions are not included.'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--project');p.add_argument('--db',type=Path,default=Path.home()/'.local/state/lean-swarm/control.sqlite3');a=p.parse_args()
    c=sqlite3.connect(a.db.resolve().as_uri()+'?mode=ro',uri=True);c.row_factory=sqlite3.Row
    if a.project:
        tasks=[dict(r) for r in c.execute('select * from tasks where project_id=?',(a.project,))]
        attempts=[dict(r) for r in c.execute('select * from attempts where project_id=?',(a.project,))]
    else:
        tasks=[dict(r) for r in c.execute('select * from tasks')];attempts=[dict(r) for r in c.execute('select * from attempts')]
    result=summarize(tasks,attempts);result['managed_model_caps']={r['model']:'unlimited' if r['max_active']==0 else r['max_active'] for r in c.execute('select * from limits')};c.close()
    print(json.dumps(result,ensure_ascii=False,indent=2))
if __name__=='__main__':main()

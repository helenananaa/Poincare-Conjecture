#!/usr/bin/env python3
"""Read-only queue and concurrency report; no agents, no claims, no state changes."""
from pathlib import Path
import argparse,collections,json,sqlite3,time

def summarize(tasks,attempts,now=None,gates=()):
    now=time.time() if now is None else now
    by_id={(t['project_id'],t['task_id']):t for t in tasks}
    projects={}
    for t in tasks:
        p=projects.setdefault(t['project_id'],{'states':{},'ready':[],'blocked':[]})
        p['states'][t['status']]=p['states'].get(t['status'],0)+1
        if t['status']=='QUEUED':
            payload=json.loads(t['payload_json'])
            deps=payload.get('depends_on',[])
            missing=[d for d in deps if by_id.get((t['project_id'],d),{}).get('status')!='INTEGRATED']
            missing += ['gate:'+g for g in payload.get('integrated_gates',[]) if g not in gates]
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
    tables={r['name'] for r in c.execute("SELECT name FROM sqlite_master WHERE type='table'")}
    gates={r['gate_id'] for r in c.execute('SELECT gate_id FROM acceptance_gates')} if 'acceptance_gates' in tables else set()
    research=[]
    if 'research_jobs' in tables:
        sql='SELECT job_id,project_id,task_id,model,effort,status FROM research_jobs'
        research=[dict(r) for r in c.execute(sql+' WHERE project_id=?',(a.project,))] if a.project else [dict(r) for r in c.execute(sql)]
    result=summarize(tasks,attempts,gates=gates)
    result['research_jobs']=research
    result['research_states']=dict(collections.Counter(r['status'] for r in research))
    result['accepted_research_gate_count']=len(gates)
    result['paused_models']={r['model']:r['reason'] for r in c.execute('SELECT * FROM paused_models')}
    result['notes']='Queue slots and process stages are not measurements of model inference. Fixed-proof and research records are separate in the same registry. Research REVIEW_REQUIRED is not proved or integrated. Unregistered external sessions are not counted.'
    result['managed_model_caps']={r['model']:'unlimited' if r['max_active']==0 else r['max_active'] for r in c.execute('select * from limits')};c.close()
    print(json.dumps(result,ensure_ascii=False,indent=2))
if __name__=='__main__':main()

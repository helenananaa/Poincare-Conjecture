"""Concurrency regressions; use real threads/SQLite, no model or Lean calls."""
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import TestCase
import threading,time
from runtime import Controller
from state import Store

def task(name,depends=(),priority=0):
 return {'id':name,'model':'grok','depends_on':list(depends),'source':'theorem t : True := by trivial','target_name':'t','target_path':name+'.lean','priority':priority}

class PipelineTests(TestCase):
 def test_integrator_does_not_block_unrelated_worker(self):
  with TemporaryDirectory() as tmp:
   store=Store(Path(tmp)/'s.db');store.init_project('p',{'repo':tmp,'integration_branch':'integration'})
   store.set_limits(4,0);store.add_tasks('p',[task('a'),task('b'),task('consumer',['a'])])
   claim=store.claim('p','pre');store.finish(claim['attempt_id'],'VERIFIED',{})
   c=Controller(store,Path(tmp)/'state','p');started=threading.Event();b_ran=threading.Event();events=[]
   def execute(claim):
    if claim['task_id']=='b':
     self.assertTrue(started.wait(2));b_ran.set()
    events.append('execute:'+claim['task_id']);store.finish(claim['attempt_id'],'VERIFIED',{})
   def integrate(tid):
    if tid=='a':
     started.set()
     if not b_ran.wait(2):raise AssertionError('dispatcher blocked behind integrator')
    events.append('integrate:'+tid);store.mark_integrated('p',tid,'commit-'+tid)
   c.execute=execute;c.integrate=integrate
   rows=c.run(jobs=2,integrate=True)
   self.assertTrue(all(r['status']=='INTEGRATED' for r in rows))
   self.assertLess(events.index('execute:b'),events.index('integrate:a'))
   self.assertLess(events.index('integrate:a'),events.index('execute:consumer'))
 def test_more_than_eight_grok_workers_can_run(self):
  with TemporaryDirectory() as tmp:
   s=Store(Path(tmp)/'s.db');s.init_project('p',{'repo':tmp,'integration_branch':'integration'});s.set_limits(4,0)
   s.add_tasks('p',[task(f't{i:02}') for i in range(12)])
   c=Controller(s,Path(tmp)/'state','p');barrier=threading.Barrier(12);lock=threading.Lock();active=peak=0
   def execute(claim):
    nonlocal active,peak
    with lock:active+=1;peak=max(active,peak)
    barrier.wait(4)
    with lock:active-=1
    s.finish(claim['attempt_id'],'VERIFIED',{})
   c.execute=execute;rows=c.run(12,False)
   self.assertEqual(peak,12);self.assertTrue(all(r['status']=='VERIFIED' for r in rows))
 def test_failed_integration_does_not_unlock_child(self):
  with TemporaryDirectory() as tmp:
   s=Store(Path(tmp)/'s.db');s.init_project('p',{'repo':tmp,'integration_branch':'integration'});s.set_limits(4,0)
   s.add_tasks('p',[task('a'),task('child',['a']),task('independent')]);c=Controller(s,Path(tmp)/'state','p')
   c.execute=lambda claim:s.finish(claim['attempt_id'],'VERIFIED',{})
   def integrate(t):
    if t=='a':raise RuntimeError('expected gate rejection')
    s.mark_integrated('p',t,'ok')
   c.integrate=integrate;rows={r['id']:r['status'] for r in c.run(4,True)}
   self.assertEqual(rows,{'a':'VERIFIED','child':'QUEUED','independent':'INTEGRATED'})
 def test_priority_does_not_bypass_dependency(self):
  with TemporaryDirectory() as tmp:
   s=Store(Path(tmp)/'s.db');s.init_project('p',{});s.set_limits(4,0)
   s.add_tasks('p',[task('aa-low'),task('zz-critical'),task('child',['zz-critical'],1000)])
   first=s.claim('p','x');self.assertEqual(first['task_id'],'zz-critical')
   self.assertEqual(s.claim('p','x')['task_id'],'aa-low');self.assertIsNone(s.claim('p','x'))
 def test_explicit_priority_and_validation(self):
  with TemporaryDirectory() as tmp:
   s=Store(Path(tmp)/'s.db');s.init_project('p',{});s.set_limits(4,0)
   s.add_tasks('p',[task('a'),task('z',priority=5)])
   self.assertEqual(s.claim('p','x')['task_id'],'z')
   for bad in [True,1.5,1001,'9']:
    with self.assertRaises(ValueError):s.add_tasks('p',[task('bad',priority=bad)])
 def test_worktree_metadata_lock_not_integration_lock(self):
  with TemporaryDirectory() as tmp:
   s=Store(Path(tmp)/'s.db');s.init_project('p',{'repo':tmp,'integration_branch':'integration'})
   c=Controller(s,Path(tmp)/'state','p');self.assertNotEqual(c.worktree_lock,c.gitlock)

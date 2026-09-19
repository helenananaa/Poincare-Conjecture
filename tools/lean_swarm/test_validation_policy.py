"""Resource-policy tests: Lake is a recording stub, never a real compiler."""
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import TestCase
import os,re,subprocess,sys

REPO=Path(__file__).resolve().parents[2]
GATE=REPO/'scripts/validate-lean-changes.sh'
CHECKER=REPO/'PoincareConjecture/tests/check_complementary_frontier.py'

class ValidationResourcePolicyTests(TestCase):
    def setUp(self):
        self.temp=TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.trace=self.root/'lake-calls.txt'
        bins=self.root/'fake-bin';bins.mkdir()
        lake=bins/'lake'
        lake.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$LAKE_TRACE"\nexit 0\n')
        lake.chmod(0o755)
        self.env=dict(os.environ,PATH=str(bins)+':'+os.environ['PATH'],LAKE_TRACE=str(self.trace))
        for path in re.findall(r'^\s*\[[A-Za-z]+\]="([^"]+)"',GATE.read_text(),re.M):
            (self.root/path).mkdir(parents=True,exist_ok=True)
        for path in ('PoincareConjecture','shared','formalized-sources'):
            (self.root/path).mkdir(exist_ok=True)
        self.git('init','-q')
        self.git('-c','user.name=Validation Test','-c','user.email=validation-test@example.invalid',
                 'commit','-q','--allow-empty','-m','fixture')
        self.base=self.git('rev-parse','HEAD').strip()

    def git(self,*args):
        return subprocess.check_output(['git',*args],cwd=self.root,env=self.env,text=True,stderr=subprocess.STDOUT)

    def gate(self,*args):
        return subprocess.run(['bash',str(GATE),*args],cwd=self.root,env=self.env,
                              text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=15)

    def calls(self):
        return self.trace.read_text().splitlines() if self.trace.exists() else []

    def changed_main(self):
        (self.root/'PoincareConjecture/Example.lean').write_text('theorem example_true : True := by trivial\n')

    def test_missing_base_fails_before_any_build(self):
        p=subprocess.run([sys.executable,str(CHECKER)],cwd=self.root,env=self.env,
                         text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=5)
        self.assertEqual(p.returncode,2)
        self.assertIn('--base-ref',p.stdout)
        self.assertEqual(self.calls(),[])

    def test_fresh_requires_separate_explicit_opt_in(self):
        p=subprocess.run([sys.executable,str(CHECKER),'--base-ref',self.base,'--fresh'],
                         cwd=self.root,env=self.env,text=True,stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT,timeout=5)
        self.assertEqual(p.returncode,2)
        self.assertIn('--allow-full-rebuild',p.stdout)
        self.assertEqual(self.calls(),[])

    def test_all_packages_refused_without_opt_in(self):
        p=self.gate('--all')
        self.assertEqual(p.returncode,2,p.stdout)
        self.assertIn('disabled by default',p.stdout)
        self.assertEqual(self.calls(),[])

    def test_report_only_lean_file_cannot_trigger_full_build(self):
        (self.root/'reports').mkdir()
        (self.root/'reports/Sanity.lean').write_text('-- report fixture\n')
        p=self.gate(self.base)
        self.assertEqual(p.returncode,2,p.stdout)
        self.assertEqual(self.calls(),[])

    def test_incremental_main_build_uses_existing_cache(self):
        self.changed_main()
        p=self.gate(self.base)
        self.assertEqual(p.returncode,0,p.stdout)
        self.assertEqual(self.calls(),['build'])

    def test_cache_download_is_explicit_only(self):
        self.changed_main()
        p=self.gate(self.base,'--fetch-cache')
        self.assertEqual(p.returncode,0,p.stdout)
        self.assertEqual(self.calls(),['exe cache get','build'])

    def test_explicit_full_request_remains_available(self):
        p=self.gate('--all','--allow-full-rebuild')
        self.assertEqual(p.returncode,0,p.stdout)
        self.assertGreater(len(self.calls()),10)
        self.assertTrue(all(call=='build' for call in self.calls()))

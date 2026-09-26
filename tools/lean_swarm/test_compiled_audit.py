from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib,unittest
from compiled_audit import prepare_compiled_audit

class CompiledAuditTests(unittest.TestCase):
    def setUp(self):
        self.tmp=TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.source=self.root/'source.lean'
        self.source.write_text('theorem proof : True := by trivial\n')
        self.hash=hashlib.sha256(self.source.read_bytes()).hexdigest()
        self.objects=self.root/'objects';self.objects.mkdir()
        self.module=self.objects/'Probe.olean';self.module.write_bytes(b'test object')
    def make(self):
        return prepare_compiled_audit(self.source,self.objects,'Probe.lean','proof',self.hash)
    def test_probe_imports_only_just_compiled_module(self):
        audit=self.make();audit.verify()
        self.assertEqual(audit.audit_text,'import Probe\n#print axioms proof\n')
        self.assertNotIn('theorem',audit.audit.read_text())
    def test_missing_output_rejected(self):
        self.module.unlink()
        with self.assertRaises(ValueError):self.make()
    def test_source_changed_before_audit_rejected(self):
        self.source.write_text('changed')
        with self.assertRaises(ValueError):self.make()
    def test_source_changed_during_audit_rejected(self):
        audit=self.make();self.source.write_text('changed')
        with self.assertRaises(ValueError):audit.verify()
    def test_output_changed_rejected(self):
        audit=self.make();self.module.write_bytes(b'changed')
        with self.assertRaises(ValueError):audit.verify()
    def test_companion_changed_rejected(self):
        companion=Path(str(self.module)+'.private');companion.write_bytes(b'old')
        audit=self.make();companion.write_bytes(b'new')
        with self.assertRaises(ValueError):audit.verify()
    def test_probe_changed_rejected(self):
        audit=self.make();audit.audit.write_text('import Other\n')
        with self.assertRaises(ValueError):audit.verify()
    def test_output_symlink_rejected(self):
        target=self.root/'other.olean';target.write_bytes(b'other')
        self.module.unlink();self.module.symlink_to(target)
        with self.assertRaises(ValueError):self.make()
    def test_invalid_import_and_target_rejected(self):
        for relative,target in [('..\u002fProbe.lean','proof'),('Probe.lean','proof\n#eval 1'),('a-b.lean','proof')]:
            with self.assertRaises(ValueError):
                prepare_compiled_audit(self.source,self.objects,relative,target,self.hash)
    def test_companion_removed_rejected(self):
        companion=Path(str(self.module)+'.private');companion.write_bytes(b'old')
        audit=self.make();companion.unlink()
        with self.assertRaises(ValueError):audit.verify()

if __name__=='__main__':unittest.main()

"""Regression tests for controller review fixes, without model or Lean calls."""
import json, tempfile, unittest
from pathlib import Path
from research_queue import ResearchQueue
from runtime import parse_axioms

class ReviewHardeningTests(unittest.TestCase):
    def test_later_axiom_report_cannot_be_hidden(self):
        output = "'Target' depends on axioms: [propext]\n'Target' depends on axioms: [BadAxiom]\n"
        with self.assertRaises(ValueError): parse_axioms(output, 'Target')

    def test_legacy_completion_timestamp(self):
        with tempfile.TemporaryDirectory() as root:
            p=Path(root)/'process-result.json'
            p.write_text(json.dumps({'exit':0, 'started':1, 'ended':2}))
            result=ResearchQueue._result_info(p)
            self.assertTrue(result['known']); self.assertTrue(result['successful'])

    def test_timestamp_absence_is_not_success(self):
        with tempfile.TemporaryDirectory() as root:
            p=Path(root)/'process-result.json';p.write_text(json.dumps({'exit':0}))
            self.assertFalse(ResearchQueue._result_info(p)['known'])

    def test_efforts_reject_lower_levels(self):
        for effort in ('minimal','low','medium'):
            with self.assertRaises(ValueError): ResearchQueue._effort(effort)
        for effort in ('high','xhigh','max'):
            self.assertEqual(ResearchQueue._effort(effort),effort)

if __name__ == '__main__': unittest.main()

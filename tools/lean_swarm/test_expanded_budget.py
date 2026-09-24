"""User-authorized resource expansion must preserve validation and defaults."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import Mock
from runtime import Controller, validate_task
from test_runtime import task

class ExpandedBudgetTests(unittest.TestCase):
    def test_worker_budget_expansion_and_bad_values(self):
        for seconds in [5, 1800, 3600, 7200, 14400, 43200]:
            validate_task(dict(task(), timeout_seconds=seconds))
        for seconds in [True, 4, 43201, -1, 7200.0, '7200']:
            with self.subTest(seconds=seconds), self.assertRaises(ValueError):
                validate_task(dict(task(), timeout_seconds=seconds))

    def test_compile_budget_defaults_and_validation(self):
        with TemporaryDirectory() as directory:
            root=Path(directory); store=Mock()
            cfg={'repo':directory,'lean_bin':'/usr/bin','lean_path':''}
            store.get_project.return_value=cfg
            self.assertEqual(Controller(store,root,'test').compile_timeout_seconds,180)
            for seconds in [1200, 1800, 43200]:
                store.get_project.return_value=dict(cfg,compile_timeout_seconds=seconds)
                self.assertEqual(Controller(store,root,'test').compile_timeout_seconds,seconds)
            for seconds in [True, 0, 43201, '1800', 1.5]:
                store.get_project.return_value=dict(cfg,compile_timeout_seconds=seconds)
                with self.assertRaises(ValueError): Controller(store,root,'test')

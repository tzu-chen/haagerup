"""Mock-only checks: no Lean, resource guard, or live queue is started."""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location(
    'c8_build_all', Path(__file__).with_name('c8_build_all.py'))
batch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(batch)


class BatchSafetyTests(unittest.TestCase):
    def run_batch(self, results, arguments):
        files = [batch.C8 / 'ExampleA.lean', batch.C8 / 'ExampleB.lean']
        with patch.object(batch, 'topo_order', return_value=files), \
             patch.object(batch, 'deps', return_value=[]), \
             patch.object(batch.subprocess, 'run', side_effect=results) as run, \
             patch.object(sys, 'argv', ['c8_build_all.py', *arguments]), \
             patch.dict(os.environ, {}, clear=True), \
             contextlib.redirect_stdout(io.StringIO()), \
             contextlib.redirect_stderr(io.StringIO()):
            try:
                batch.main()
                code = 0
            except SystemExit as error:
                code = error.code
        return code, run

    @staticmethod
    def result(code, text=''):
        return subprocess.CompletedProcess([], code, stdout=text, stderr='')

    def test_resource_stop_overrides_keep_going(self):
        code, run = self.run_batch([self.result(125, 'c8q: resource review required')],
                                  ['--memory-mib', '1024', '--keep-going'])
        self.assertEqual(code, 125)
        self.assertEqual(run.call_count, 1)

    def test_invalid_request_stops_batch(self):
        code, run = self.run_batch([self.result(2)],
                                  ['--memory-mib', '1024', '--keep-going'])
        self.assertEqual(code, 2)
        self.assertEqual(run.call_count, 1)

    def test_ordinary_failure_may_continue_but_is_not_success(self):
        code, run = self.run_batch([self.result(1, 'error: type mismatch'), self.result(0)],
                                  ['--memory-mib', '1024', '--keep-going'])
        self.assertEqual(code, 1)
        self.assertEqual(run.call_count, 2)
        self.assertIn('--memory-mib', run.call_args.args[0])

    def test_missing_estimate_launches_nothing(self):
        code, run = self.run_batch([], ['--keep-going'])
        self.assertEqual(code, 2)
        run.assert_not_called()

    def test_dry_run_needs_no_estimate_and_launches_nothing(self):
        code, run = self.run_batch([], ['--dry-run'])
        self.assertEqual(code, 0)
        run.assert_not_called()


if __name__ == '__main__':
    unittest.main()

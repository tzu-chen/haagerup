"""Mock-only queue safety tests: no Lean, subprocess, or live queue is started."""

import importlib.util
import itertools
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SPEC = importlib.util.spec_from_file_location('c8q_under_test', Path(__file__).with_name('c8q.py'))
c8q = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c8q)


class FakeProcess:
    pid = 123456

    def __init__(self, codes, on_exit=None):
        self.codes = iter(codes)
        self.last = None
        self.on_exit = on_exit

    def poll(self):
        self.last = next(self.codes, self.last)
        if self.last is not None and self.on_exit:
            self.on_exit()
        return self.last


class QueueSafetyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        values = dict(QUEUE=base, REQUESTS=base / 'requests', RUNNING=base / 'running',
                      DONE=base / 'done', STOP=base / 'STOP',
                      MEMORY_STOP=base / 'MEMORY_STOP.json', MEMORY_MIB=None, MAX_PARALLEL=1)
        patcher = mock.patch.multiple(c8q, **values)
        patcher.start()
        self.addCleanup(patcher.stop)
        c8q.ensure_dirs()

    def queue(self, rid, budget=1024):
        req = dict(id=rid, path=str(Path(self.temp.name) / f'{rid}.lean'),
                   build=True, label='', submitted=1, client_pid=1)
        if budget is not None:
            req['memory_mib'] = budget
        path = c8q.REQUESTS / f'{rid}.json'
        c8q.write_json(path, req)
        return path

    def run_mocked(self, outcomes):
        outcomes = iter(outcomes)
        launched = []

        def popen(command, **kwargs):
            codes, text, on_exit = next(outcomes)
            launched.append(command)
            kwargs['stdout'].write(text + '\n')
            kwargs['stdout'].flush()
            return FakeProcess(codes, on_exit)

        clock = itertools.count(100, 10)
        with mock.patch.object(c8q.subprocess, 'Popen', side_effect=popen), \
                mock.patch.object(c8q.time, 'sleep'), \
                mock.patch.object(c8q.time, 'time', side_effect=lambda: next(clock)), \
                mock.patch.object(c8q, 'other_sessions_hold_slot', return_value=False):
            status = c8q.runner()
        return status, launched

    def test_explicit_budget_required_and_not_clamped(self):
        with self.assertRaises(ValueError):
            c8q.declared_memory_mib({})
        for value in (0, 639, 4097, -1, 1024.5, True, '', 'auto'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                c8q.validate_memory_mib(value)
        self.assertEqual(c8q.declared_memory_mib({'memory_mib': 640}), 640)
        with mock.patch.object(c8q, 'MEMORY_MIB', '2048'):
            self.assertEqual(c8q.declared_memory_mib({}), 2048)
            self.assertEqual(c8q.declared_memory_mib({'memory_mib': 1024}), 1024)
        with self.assertRaises(SystemExit) as caught:
            c8q.submit(Path(self.temp.name) / 'unused.lean', True, '')
        self.assertEqual(caught.exception.code, 125)
        self.assertEqual(list(c8q.REQUESTS.iterdir()), [])

    def test_resource_exit_and_wrapped_lean_failures(self):
        for code in (125, 137, -9, 134, -6, 143, -15, 139, -11):
            with self.subTest(code=code):
                self.assertIsNotNone(c8q.resource_failure_reason(code, ''))
        for code in (137, 134, 139):
            self.assertIsNotNone(c8q.resource_failure_reason(1, f'error: Lean exited with code {code}'))
        self.assertIsNotNone(c8q.resource_failure_reason(1, 'std::bad_alloc'))
        self.assertIsNotNone(c8q.resource_failure_reason(0, 'Resource guard stopping job: test'))
        self.assertIsNone(c8q.resource_failure_reason(1, 'error: type mismatch'))
        self.assertIsNone(c8q.resource_failure_reason(1, 'Refusing: Both numerical job slots are occupied'))

    def test_first_memory_failure_blocks_second_and_restart(self):
        self.queue('a')
        second = self.queue('b')
        status, launched = self.run_mocked([([1], 'error: Lean exited with code 137', None)])
        self.assertEqual(status, 125)
        self.assertEqual(len(launched), 1)
        self.assertTrue(second.exists())
        self.assertTrue(c8q.STOP.exists())
        self.assertTrue(c8q.MEMORY_STOP.exists())
        result = json.loads((c8q.DONE / 'a.json').read_text())
        self.assertEqual(result['exit_code'], 125)
        self.assertEqual(result['process_exit_code'], 1)
        self.assertEqual(result['memory_mib'], 1024)
        self.assertNotIn('attempts', result)
        latch = c8q.MEMORY_STOP.read_bytes()
        c8q.STOP.write_text('keep this stop marker')
        with mock.patch.object(c8q.subprocess, 'Popen') as popen:
            self.assertEqual(c8q.runner(), 125)
            popen.assert_not_called()
        self.assertEqual(c8q.STOP.read_text(), 'keep this stop marker')
        self.assertEqual(c8q.MEMORY_STOP.read_bytes(), latch)
        self.assertEqual(c8q.wait('b', 0), 125)
        with self.assertRaises(SystemExit) as caught:
            c8q.submit(Path(self.temp.name) / 'c.lean', True, '', 1024)
        self.assertEqual(caught.exception.code, 125)

    def test_other_already_active_job_finishes_after_latch(self):
        self.queue('a')
        self.queue('b')
        third = self.queue('c')
        with mock.patch.object(c8q, 'MAX_PARALLEL', 2):
            status, launched = self.run_mocked([
                ([137], 'memory failure', None),
                ([None, 0], 'successful independent active job', None),
            ])
        self.assertEqual(status, 125)
        self.assertEqual(len(launched), 2)
        self.assertTrue(third.exists())
        self.assertEqual(json.loads((c8q.DONE / 'b.json').read_text())['exit_code'], 0)

    def test_capacity_retry_preserves_logs_and_declared_budget(self):
        self.queue('a', 1536)
        old_log = c8q.DONE / 'a.log'
        old_log.write_text('historical evidence')
        status, launched = self.run_mocked([
            ([1], 'Refusing: Both numerical job slots are occupied', None),
            ([0], 'successful retry', lambda: c8q.STOP.touch()),
        ])
        self.assertEqual(status, 0)
        self.assertEqual(len(launched), 2)
        result = json.loads((c8q.DONE / 'a.json').read_text())
        logs = result['attempt_logs']
        self.assertEqual(len(set(logs)), 2)
        self.assertIn('Refusing:', Path(logs[0]).read_text())
        self.assertIn('successful retry', Path(logs[1]).read_text())
        self.assertEqual(old_log.read_text(), 'historical evidence')
        for command in launched:
            self.assertEqual(command[command.index('--memory-mib') + 1], '1536')
        self.assertFalse(c8q.MEMORY_STOP.exists())

    def test_old_pending_request_without_budget_never_launches(self):
        self.queue('a', budget=None)
        second = self.queue('b')
        status, launched = self.run_mocked([])
        self.assertEqual(status, 125)
        self.assertEqual(launched, [])
        self.assertTrue(second.exists())
        self.assertEqual(c8q.print_result('a'), 125)


if __name__ == '__main__':
    unittest.main()

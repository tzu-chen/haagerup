"""Launcher regression tests; no research workloads, compiler runs, or locks.

Run with: python -m unittest discover -s tests -p test_resource_guard_migration.py
The global guard must be installed. All process handoffs and guarded research
entry points are intercepted before work starts.
"""

from contextlib import ExitStack
import hashlib
import os
from pathlib import Path
import resource
import runpy
import signal
import subprocess
import sys
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
GUARD = Path.home() / '.local/bin/research-safe-run'
OLD_HASH = '277670ce0b7773afce64b56c8a266b7cb6fe47e056c79d5e9e84262b8674673f'


class Handoff(Exception):
    pass


class ReachedWork(Exception):
    pass


class ResourceGuardMigrationTests(unittest.TestCase):
    def test_legacy_forwarder_preserves_arguments_and_cwd(self):
        shim = runpy.run_path(str(ROOT / 'hi_cft_safe_run.py'))
        arguments = ['--limit-mib', '256', '--', 'python', 'a b.py', '--flag']
        before = Path.cwd()
        with patch.object(sys, 'argv', ['hi_cft_safe_run.py', *arguments]), \
                patch.object(os, 'execv', side_effect=Handoff) as execute:
            with self.assertRaises(Handoff):
                shim['main']()
        execute.assert_called_once_with(str(GUARD), [str(GUARD), *arguments])
        self.assertEqual(Path.cwd(), before)

    def test_missing_global_guard_fails_without_local_fallback(self):
        shim = runpy.run_path(str(ROOT / 'hi_cft_safe_run.py'))
        with patch.object(os, 'execv', side_effect=FileNotFoundError('missing')) as execute:
            with self.assertRaisesRegex(SystemExit, 'Cannot execute global resource guard'):
                shim['main']()
        self.assertEqual(execute.call_count, 1)

    def test_helper_imports_use_global_source(self):
        shim = runpy.run_path(str(ROOT / 'hi_cft_safe_run.py'))
        self.assertEqual(shim['LOCK'], Path('/tmp/research_numerical.lock'))
        for name in ('open_shared_lock', 'available_bytes', 'cgroup_headroom', 'group_rss'):
            self.assertEqual(Path(shim[name].__code__.co_filename).resolve(), GUARD.resolve())

    def test_old_guard_archive_keeps_exact_historical_digest(self):
        archive = ROOT / 'resource_guard_history' / f'hi_cft_safe_run_{OLD_HASH}.py.txt'
        self.assertEqual(hashlib.sha256(archive.read_bytes()).hexdigest(), OLD_HASH)

    def test_lean_and_graph_launch_through_global_guard(self):
        source = ROOT / 'lean/HaagerupIzumi/Analytic/GammaIntegral.lean'
        cases = [
            ('lean/safe_lean.py', [str(source), '-o', '/tmp/test-module.olean']),
            ('lean/safe_lean.py', ['--build', str(source)]),
            ('lean/docs/build_dependency_graph.py', ['--from-cache', '--extract-only']),
        ]
        for filename, args in cases:
            with self.subTest(filename=filename, args=args):
                module = runpy.run_path(str(ROOT / filename))
                with patch.object(sys, 'argv', [filename, *args]), \
                        patch.object(os, 'execv', side_effect=Handoff) as execute:
                    with self.assertRaises(Handoff):
                        module['main']()
                self.assertEqual(execute.call_args.args,
                                 (str(GUARD), [str(GUARD), '--', sys.executable,
                                              str(ROOT / filename), '--guarded', *args]))

    def test_parent_guards_accept_global_and_reject_impostors(self):
        source = ROOT / 'lean/HaagerupIzumi/Analytic/GammaIntegral.lean'
        cases = [
            ('lean/safe_lean.py', 'main', ['--guarded', str(source)], 'lean'),
            ('lean/docs/build_dependency_graph.py', 'main', ['--guarded'], 'graph'),
            ('c8_revision_20260927/authenticate_inputs.py', 'main',
             ['--output', 'unused-guard-test.json'], 'signal'),
            ('c8_reviewability_20260927/finite_witnesses.py', 'main',
             ['--output', 'unused-guard-test.json'], 'signal'),
            ('c8_reviewability_20260927/check_gate4_packet.py', 'guard', [], 'signal'),
        ]
        parents = [GUARD, ROOT / 'hi_cft_safe_run.py', Path('/tmp/impostor/research-safe-run')]
        read_bytes = Path.read_bytes
        for filename, entry, args, boundary in cases:
            module = runpy.run_path(str(ROOT / filename))
            for parent in parents:
                with self.subTest(filename=filename, parent=parent):
                    def fake_read(path):
                        if str(path) == f'/proc/{os.getppid()}/cmdline':
                            return b'python3\0' + os.fsencode(parent) + b'\0'
                        return read_bytes(path)

                    with ExitStack() as stack:
                        stack.enter_context(patch.object(sys, 'argv', [filename, *args]))
                        stack.enter_context(patch.object(Path, 'read_bytes', fake_read))
                        stack.enter_context(patch.object(resource, 'getrlimit',
                                                         return_value=(512 * 1024**2,) * 2))
                        stack.enter_context(patch.object(os, 'sched_getaffinity', return_value={0, 1}))
                        if boundary == 'lean':
                            stack.enter_context(patch.object(subprocess, 'check_output', side_effect=ReachedWork))
                        elif boundary == 'graph':
                            stack.enter_context(patch.dict(module[entry].__globals__,
                                                           extract=lambda: (_ for _ in ()).throw(ReachedWork())))
                        else:
                            stack.enter_context(patch.object(signal, 'signal', side_effect=ReachedWork))
                        expected = ReachedWork if parent == GUARD else (SystemExit, ValueError)
                        with self.assertRaises(expected):
                            module[entry]()

    def test_expired_memory_exception_still_refuses(self):
        module = runpy.run_path(str(ROOT / 'hi_cft_third_window_run.py'))
        with self.assertRaisesRegex(ValueError, 'inactive or expiring'):
            module['read_policy'](module['epoch'](module['END']) + 1)

    def test_witness_hashing_allows_only_canonical_external_guard(self):
        module = runpy.run_path(str(ROOT / 'c8_reviewability_20260927/finite_witnesses.py'))
        expected = hashlib.sha256(GUARD.read_bytes()).hexdigest()
        self.assertEqual(module['sha'](GUARD), expected)
        self.assertEqual(module['SOURCE_HASHES'][str(GUARD.resolve())], expected)
        with self.assertRaisesRegex(ValueError, 'outside repository'):
            module['sha']('/tmp/impostor/research-safe-run')


if __name__ == '__main__':
    unittest.main()

#!/usr/bin/env python3
"""Build every module under lean/HaagerupIzumi/C8 (and its CFT prerequisites) in
dependency order through the root-coordinated compile queue (lean/tools/c8q.py).

Usage (root agent only, from the repository root):
    python3 lean/tools/c8_build_all.py --memory-mib REVIEWED_MIB [--skip-built]
    python3 lean/tools/c8_build_all.py --dry-run

Each module is submitted with `c8q.py build`. A reviewed memory estimate is
required, either here or through an explicit C8Q_MEMORY_MIB environment value.
Resource failures always stop the batch, including with --keep-going.
It does not run Lean itself: the queue admits each job through the resource guard.
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'lean'
C8 = LEAN / 'HaagerupIzumi' / 'C8'
IMPORT_RE = re.compile(r'(?m)^(?:public\s+)?import\s+(HaagerupIzumi(?:\.[^\s]+)*)')


def module_path(name):
    return LEAN.joinpath(*name.split('.')).with_suffix('.lean')


def deps(path):
    return [module_path(m) for m in IMPORT_RE.findall(path.read_text())]


def topo_order(roots):
    order, seen, stack = [], set(), set()

    def visit(p):
        if p in seen:
            return
        if p in stack:
            raise SystemExit(f'import cycle at {p}')
        stack.add(p)
        for d in deps(p):
            if not d.exists():
                raise SystemExit(f'{p} imports missing module {d}')
            visit(d)
        stack.discard(p)
        seen.add(p)
        order.append(p)

    for r in roots:
        visit(r)
    return order


def olean_of(path):
    return LEAN / '.lake' / 'build' / 'lib' / 'lean' / path.relative_to(LEAN).with_suffix('.olean')


def built(path):
    """Up to date: the olean is newer than the source and than every imported project olean."""
    olean = olean_of(path)
    if not olean.exists() or olean.stat().st_mtime < path.stat().st_mtime:
        return False
    for d in deps(path):
        od = olean_of(d)
        if not od.exists() or od.stat().st_mtime > olean.stat().st_mtime:
            return False
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--skip-built', action='store_true')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--keep-going', action='store_true',
                    help='continue after ordinary proof errors; never after resource failures')
    ap.add_argument('--memory-mib', type=int,
                    help='reviewed per-job memory estimate forwarded to the compile queue')
    ap.add_argument('roots', nargs='*')
    args = ap.parse_args()
    if not args.dry_run:
        budget = args.memory_mib
        if budget is None:
            try:
                budget = int(os.environ.get('C8Q_MEMORY_MIB', ''))
            except ValueError:
                ap.error('supply --memory-mib or C8Q_MEMORY_MIB after reviewing allocation needs')
        if budget <= 0:
            ap.error('the reviewed memory estimate must be positive')
    roots = [Path(r).resolve() for r in args.roots] or sorted(
        p for p in C8.rglob('*.lean') if 'Scratch' not in p.name)
    order = topo_order(roots)
    failed = set()
    for p in order:
        rel = p.relative_to(ROOT)
        bad = [d for d in deps(p) if d in failed]
        if bad:
            failed.add(p)
            print(f'SKIP {rel} (depends on failed {bad[0].relative_to(ROOT)})', flush=True)
            continue
        if args.skip_built and built(p):
            print(f'skip (built) {rel}', flush=True)
            continue
        print(f'build {rel}', flush=True)
        if args.dry_run:
            continue
        command = [sys.executable, str(LEAN / 'tools' / 'c8q.py'), 'build', str(rel),
                   '--timeout', '3000']
        if args.memory_mib is not None:
            command.extend(['--memory-mib', str(args.memory_mib)])
        r = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        tail = r.stdout.splitlines()[-1] if r.stdout.splitlines() else ''
        if r.returncode != 0:
            failed.add(p)
            # c8q reserves 125 for resource stops and 2 for invalid requests.
            # Continuing either would repeat the same unsafe or invalid launch.
            if r.returncode in (125, 2):
                print(r.stdout, end='' if r.stdout.endswith('\n') else '\n')
                if r.stderr:
                    print(r.stderr, file=sys.stderr, end='' if r.stderr.endswith('\n') else '\n')
                raise SystemExit(r.returncode)
            errs = [l for l in r.stdout.splitlines() if 'error' in l][:4]
            print('  FAILED: ' + ' | '.join(errs)[:900], flush=True)
            if not args.keep_going:
                raise SystemExit(f'FAILED: {rel}')
            continue
        print('  ' + tail, flush=True)
    print(f'{len(order) - len(failed)} of {len(order)} modules built; failed: '
          f'{[str(f.relative_to(ROOT)) for f in failed]}', flush=True)
    if failed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()

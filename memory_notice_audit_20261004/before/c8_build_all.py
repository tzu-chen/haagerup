#!/usr/bin/env python3
"""Build every module under lean/HaagerupIzumi/C8 (and its CFT prerequisites) in
dependency order through the root-coordinated compile queue (lean/tools/c8q.py).

Usage (root agent only, from the repository root):
    python3 lean/tools/c8_build_all.py [--skip-built] [--dry-run]

Each module is submitted with `c8q.py build`; the script stops at the first failure.
It does not run Lean itself: the queue admits each job through the resource guard.
"""

import argparse
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
                    help='record failures, skip their dependents, and continue')
    ap.add_argument('roots', nargs='*')
    args = ap.parse_args()
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
        r = subprocess.run([sys.executable, str(LEAN / 'tools' / 'c8q.py'), 'build', str(rel),
                            '--timeout', '3000'], cwd=ROOT, capture_output=True, text=True)
        tail = r.stdout.splitlines()[-1] if r.stdout.splitlines() else ''
        if r.returncode != 0:
            failed.add(p)
            errs = [l for l in r.stdout.splitlines() if 'error' in l][:4]
            print('  FAILED: ' + ' | '.join(errs)[:900], flush=True)
            if not args.keep_going:
                raise SystemExit(f'FAILED: {rel}')
            continue
        print('  ' + tail, flush=True)
    print(f'{len(order) - len(failed)} of {len(order)} modules built; failed: '
          f'{[str(f.relative_to(ROOT)) for f in failed]}', flush=True)


if __name__ == '__main__':
    main()

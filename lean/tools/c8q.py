#!/usr/bin/env python3
"""Root-coordinated Lean compile queue for the c=8 formalization.

Subagents must not admit numerical jobs themselves (see AGENTS.md and
~/.codex/AGENTS.md).  They submit Lean files here; a single runner started by
the root agent admits each request through ~/.local/bin/research-safe-run
(--wait) and lean/safe_lean.py, at most MAX_PARALLEL at a time (env C8Q_MAX_PARALLEL, default 1, so
that other sessions keep a guard slot), each with a C8Q_MEMORY_MIB reservation.

Client usage (from anywhere):
    python3 lean/tools/c8q.py check  lean/HaagerupIzumi/C8/Foo.lean
    python3 lean/tools/c8q.py build  lean/HaagerupIzumi/C8/Foo.lean
    python3 lean/tools/c8q.py wait   <request-id>
    python3 lean/tools/c8q.py status

`check` elaborates one file (no .olean written).  `build` registers the
module's Lake artifacts so that other files can import it; its own imports
must already be built.  Both block for up to --timeout seconds (default 540,
below the 600 s tool limit).  If the job has not finished, the command prints
the request id and exits with status 75; use `wait <id>` to keep waiting.

Runner usage (root only):
    python3 lean/tools/c8q.py runner
"""

import argparse
import json
import os
import secrets
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / 'lean'
QUEUE = Path(f'/tmp/haagerup-c8q-{os.getuid()}')
REQUESTS = QUEUE / 'requests'
RUNNING = QUEUE / 'running'
DONE = QUEUE / 'done'
STOP = QUEUE / 'STOP'
GUARD = Path.home() / '.local/bin/research-safe-run'
MAX_PARALLEL = int(os.environ.get('C8Q_MAX_PARALLEL', '1'))
MEMORY_MIB = int(os.environ.get('C8Q_MEMORY_MIB', '3584'))
JOB_TIMEOUT = 2400
MAX_PRINT_LINES = 600


def ensure_dirs():
    for d in (REQUESTS, RUNNING, DONE):
        d.mkdir(parents=True, exist_ok=True)


def write_json(path, data):
    tmp = path.with_name(path.name + '.' + secrets.token_hex(4) + '.tmp')
    tmp.write_text(json.dumps(data, indent=1, sort_keys=True))
    os.replace(tmp, path)


def resolve_source(arg):
    p = Path(arg)
    if not p.is_absolute():
        cand = (Path.cwd() / p).resolve()
        if not cand.exists():
            cand = (ROOT / p).resolve()
        p = cand
    p = p.resolve()
    if not p.is_file() or p.suffix != '.lean':
        sys.exit(f'c8q: not a Lean source file: {p}')
    try:
        p.relative_to(LEAN_DIR)
    except ValueError:
        sys.exit('c8q: only files inside the lean/ project are accepted')
    return p


def submit(path, build, label):
    ensure_dirs()
    rid = time.strftime('%H%M%S') + '-' + secrets.token_hex(3)
    req = {'id': rid, 'path': str(path), 'build': build, 'label': label,
           'submitted': time.time(), 'client_pid': os.getpid()}
    write_json(REQUESTS / f'{time.time_ns()}-{rid}.json', req)
    return rid


def print_result(rid):
    meta = json.loads((DONE / f'{rid}.json').read_text())
    log = Path(meta['log']).read_text(errors='replace').splitlines()
    if len(log) > MAX_PRINT_LINES:
        head = log[:MAX_PRINT_LINES // 2]
        tail = log[-MAX_PRINT_LINES // 2:]
        log = head + [f'... [{len(log) - MAX_PRINT_LINES} lines omitted; full log: {meta["log"]}] ...'] + tail
    print('\n'.join(log))
    mode = 'build' if meta['build'] else 'check'
    print(f'c8q: {mode} {meta["path"]} -> exit {meta["exit_code"]} '
          f'(queued {meta["started"] - meta["submitted"]:.0f}s, ran {meta["finished"] - meta["started"]:.0f}s); '
          f'log {meta["log"]}')
    return meta['exit_code']


def wait(rid, timeout):
    deadline = time.time() + timeout
    while time.time() < deadline:
        if (DONE / f'{rid}.json').exists():
            return print_result(rid)
        time.sleep(2)
    position = queue_position(rid)
    print(f'c8q: request {rid} not finished after {timeout:.0f}s ({position}). '
          f'Run: python3 lean/tools/c8q.py wait {rid}')
    return 75


def queue_position(rid):
    if any(p.name.startswith(rid) for p in RUNNING.glob('*.json')):
        return 'running'
    pending = sorted(REQUESTS.glob('*.json'))
    for i, p in enumerate(pending):
        if p.name.endswith(f'-{rid}.json'):
            return f'queued, position {i + 1} of {len(pending)}'
    return 'unknown state'


def status():
    ensure_dirs()
    running = [json.loads(p.read_text()) for p in RUNNING.glob('*.json')]
    pending = [json.loads(p.read_text()) for p in sorted(REQUESTS.glob('*.json'))]
    print(f'runner stop flag: {STOP.exists()}')
    print(f'running ({len(running)}):')
    for r in running:
        print(f"  {r['id']} {'build' if r['build'] else 'check'} {r['path']} "
              f"started {time.time() - r.get('started', time.time()):.0f}s ago")
    print(f'pending ({len(pending)}):')
    for r in pending:
        print(f"  {r['id']} {'build' if r['build'] else 'check'} {r['path']} "
              f"waiting {time.time() - r['submitted']:.0f}s")
    slots = Path(f'/tmp/research-safe-run-{os.getuid()}')
    for meta in sorted(slots.glob('slot-*.json')):
        try:
            m = json.loads(meta.read_text())
            print(f"guard {meta.name}: cwd {m.get('cwd')} status {m.get('status')} memory {m.get('memory_mib')} MiB")
        except Exception:
            pass


BUSY_MARKERS = ('Both numerical job slots are occupied', 'Host memory cannot cover',
                'The shared memory budget is fully reserved', 'The shared CPU budget',
                'Not enough unreserved CPUs', 'cgroup headroom', 'legacy or exclusive')
MEMORY_FLOOR_MIB = 640
MEMORY_CAP_MIB = 4096


def peak_history():
    """Maximum sampled peak (MiB) of completed guarded runs, by source path."""
    peaks = {}
    for meta_path in DONE.glob('*.json'):
        try:
            meta = json.loads(meta_path.read_text())
            text = Path(meta['log']).read_text(errors='replace')
        except (OSError, ValueError, KeyError):
            continue
        for line in text.splitlines():
            if 'sampled peak scope memory' in line:
                try:
                    value = float(line.split('memory')[1].split('MiB')[0])
                except (IndexError, ValueError):
                    continue
                peaks[meta['path']] = max(peaks.get(meta['path'], 0.0), value)
    return peaks


def estimate_mib(req, peaks):
    """Declared reservation: the revised estimate after a breach, else 1.3x the largest
    measured peak of this file (floor MEMORY_FLOOR_MIB, cap MEMORY_CAP_MIB)."""
    if req.get('memory_mib'):
        return int(req['memory_mib'])
    peak = peaks.get(req['path'])
    if peak is None:
        return MEMORY_FLOOR_MIB
    return int(min(MEMORY_CAP_MIB, max(MEMORY_FLOOR_MIB, 1.3 * peak + 1)))


def child_pids(pid):
    try:
        text = Path(f'/proc/{pid}/task/{pid}/children').read_text()
        return [int(x) for x in text.split()]
    except OSError:
        return []


def other_sessions_hold_slot(active):
    """True if a guard slot is held by a job that this runner did not start."""
    ours = set()
    for proc, *_ in active.values():
        ours.update(child_pids(proc.pid))
    slot_dir = Path(f'/tmp/research-safe-run-{os.getuid()}')
    for meta_path in slot_dir.glob('slot-*.json'):
        try:
            meta = json.loads(meta_path.read_text())
        except (OSError, ValueError):
            return True
        if meta.get('status') == 'running' and meta.get('guard_pid') not in ours:
            return True
    return False


def runner():
    """Admit queued Lean jobs through the guard without --wait.  A request the guard refuses
    for lack of capacity is requeued (other requests may proceed meanwhile).  A job stopped for
    exceeding its declared reservation is requeued once per doubling with a revised estimate
    (never blindly with the same budget)."""
    ensure_dirs()
    STOP.unlink(missing_ok=True)
    active = {}
    print(f'c8q runner: queue {QUEUE}, max parallel {MAX_PARALLEL}, adaptive reservations', flush=True)
    while True:
        for rid, (proc, req, logf, run_path, req_name) in list(active.items()):
            code = proc.poll()
            if code is None:
                continue
            logf.close()
            text = Path(req['log']).read_text(errors='replace')
            run_path.unlink(missing_ok=True)
            del active[rid]
            refused = code != 0 and 'Refusing:' in text and any(m in text for m in BUSY_MARKERS) \
                and 'Resource guard: slot' not in text
            breached = 'job memory exceeded its cgroup reservation' in text or code in (137, -9)
            if refused or (breached and req['mem_used'] < MEMORY_CAP_MIB):
                req.pop('started', None)
                req['attempts'] = req.get('attempts', 0) + 1
                req['not_before'] = time.time() + (3 if refused else 1)
                if breached:
                    req['memory_mib'] = min(MEMORY_CAP_MIB, max(2048, 2 * req['mem_used']))
                    print(f"c8q runner: {rid} exceeded {req['mem_used']} MiB; requeued with "
                          f"{req['memory_mib']} MiB", flush=True)
                write_json(REQUESTS / req_name, req)
                continue
            req['exit_code'] = code
            req['finished'] = time.time()
            write_json(DONE / f'{rid}.json', req)
            print(f"c8q runner: done {rid} exit {code} {req['path']} "
                  f"({req['finished'] - req['started']:.0f}s, {req['mem_used']} MiB)", flush=True)
        if STOP.exists() and not active:
            print('c8q runner: stop flag seen, exiting', flush=True)
            return
        limit = MAX_PARALLEL
        if limit > 1 and active and other_sessions_hold_slot(active):
            limit = 1   # leave the second guard slot to other sessions
        if not STOP.exists() and len(active) < limit:
            busy_paths = {item[1]['path'] for item in active.values()}
            peaks = peak_history()
            now = time.time()
            for req_path in sorted(REQUESTS.glob('*.json')):
                if len(active) >= limit:
                    break
                try:
                    req = json.loads(req_path.read_text())
                except (OSError, ValueError):
                    continue
                if req['path'] in busy_paths or req.get('not_before', 0) > now:
                    continue
                rid = req['id']
                mem = estimate_mib(req, peaks)
                req['mem_used'] = mem
                req['started'] = time.time()
                req['log'] = str(DONE / f'{rid}.log')
                run_path = RUNNING / f'{rid}.json'
                write_json(run_path, req)
                req_name = req_path.name
                req_path.unlink(missing_ok=True)
                logf = open(req['log'], 'w')
                command = ['timeout', '-k', '30', str(JOB_TIMEOUT), str(GUARD),
                           '--memory-mib', str(mem), '--limit-mib', '6144', '--',
                           sys.executable, str(LEAN_DIR / 'safe_lean.py'), '--guarded',
                           *(['--build'] if req['build'] else []), req['path']]
                logf.write('$ ' + ' '.join(command) + '\n')
                logf.flush()
                proc = subprocess.Popen(command, cwd=str(ROOT), stdout=logf,
                                        stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
                active[rid] = (proc, req, logf, run_path, req_name)
                busy_paths.add(req['path'])
                if req.get('attempts', 0) == 0:
                    print(f"c8q runner: start {rid} {'build' if req['build'] else 'check'} "
                          f"{req['path']} ({mem} MiB)", flush=True)
                time.sleep(1)
        time.sleep(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='cmd', required=True)
    for name in ('check', 'build'):
        p = sub.add_parser(name)
        p.add_argument('file')
        p.add_argument('--timeout', type=float, default=540)
        p.add_argument('--label', default='')
    p = sub.add_parser('wait')
    p.add_argument('id')
    p.add_argument('--timeout', type=float, default=540)
    sub.add_parser('status')
    sub.add_parser('runner')
    args = parser.parse_args()
    if args.cmd in ('check', 'build'):
        path = resolve_source(args.file)
        rid = submit(path, args.cmd == 'build', args.label)
        print(f'c8q: submitted {args.cmd} {path} as {rid}', flush=True)
        sys.exit(wait(rid, args.timeout))
    if args.cmd == 'wait':
        sys.exit(wait(args.id, args.timeout))
    if args.cmd == 'status':
        status()
        return
    if args.cmd == 'runner':
        runner()


if __name__ == '__main__':
    main()

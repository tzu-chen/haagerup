#!/usr/bin/env python3
"""Root-coordinated Lean compile queue for the c=8 formalization.

Subagents must not admit numerical jobs themselves (see AGENTS.md and
~/.codex/AGENTS.md).  They submit Lean files here; a single runner started by
the root agent admits each request through ~/.local/bin/research-safe-run
and lean/safe_lean.py, at most MAX_PARALLEL at a time (env C8Q_MAX_PARALLEL,
default 1, so that other sessions keep a guard slot). Every request needs a
reviewed --memory-mib declaration or an explicitly set C8Q_MEMORY_MIB.
Resource failures stop admission persistently until reviewed; they are not retried.

Client usage (from anywhere):
    python3 lean/tools/c8q.py check lean/HaagerupIzumi/C8/Foo.lean --memory-mib REVIEWED_MIB
    python3 lean/tools/c8q.py build lean/HaagerupIzumi/C8/Foo.lean --memory-mib REVIEWED_MIB
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
import re
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
MEMORY_STOP = QUEUE / 'MEMORY_STOP.json'
GUARD = Path.home() / '.local/bin/research-safe-run'
MAX_PARALLEL = int(os.environ.get('C8Q_MAX_PARALLEL', '1'))
MEMORY_MIB = os.environ.get('C8Q_MEMORY_MIB')
JOB_TIMEOUT = 2400
MAX_PRINT_LINES = 600
RESOURCE_FAILURE = 125
MEMORY_FLOOR_MIB = 640
MEMORY_CAP_MIB = 4096


def validate_memory_mib(value):
    if isinstance(value, bool) or not re.fullmatch(r'[0-9]+', str(value)):
        raise ValueError('memory must be an integer MiB declaration')
    value = int(value)
    if not MEMORY_FLOOR_MIB <= value <= MEMORY_CAP_MIB:
        raise ValueError(f'memory must be {MEMORY_FLOOR_MIB}..{MEMORY_CAP_MIB} MiB; '
                         'out-of-range declarations are not clamped')
    return value


def declared_memory_mib(req):
    value = req.get('memory_mib', MEMORY_MIB)
    if value is None:
        raise ValueError('declare a reviewed --memory-mib or explicitly set C8Q_MEMORY_MIB; '
                         'there is no automatic estimate for this request')
    return validate_memory_mib(value)


def memory_stop_message():
    return (f'c8q: admission stopped by {MEMORY_STOP}; review the failed allocation and '
            'job design before explicitly clearing MEMORY_STOP.json and STOP. '
            'No automatic restart or memory increase is permitted.')


def resource_failure_reason(code, text):
    """Conservatively recognize guard stops and nested Lean crashes as well as exits."""
    if code in (124, 125, 137, -9, 134, -6, 143, -15, 139, -11):
        return f'guard/resource/signal exit {code}'
    lowered = text.lower()
    markers = ('resource guard stopping job:', 'job memory exceeded its cgroup reservation',
               'memoryerror', 'std::bad_alloc', 'out of memory', 'out-of-memory',
               'cannot allocate memory', 'failed to allocate', 'memory allocation failed')
    if any(marker in lowered for marker in markers):
        return 'allocation failure or resource guard stop in command output'
    if re.search(r'lean exited with code\s+(?:125|137|134|139|143)\b', lowered):
        return 'nested Lean resource/signal failure'
    return None


def latch_resource_failure(req, reason):
    # Keep the first incident and its evidence; never silently replace a live latch.
    if not MEMORY_STOP.exists():
        write_json(MEMORY_STOP, {'status': 'RESOURCE_REVIEW_REQUIRED', 'id': req['id'],
                   'path': req['path'], 'log': req.get('log'),
                   'memory_mib': req.get('mem_used'), 'reason': reason,
                   'process_exit_code': req.get('process_exit_code'), 'time': time.time()})
    STOP.touch(exist_ok=True)
    print(memory_stop_message(), file=sys.stderr, flush=True)


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


def submit(path, build, label, memory_mib=None):
    if MEMORY_STOP.exists():
        print(memory_stop_message(), file=sys.stderr)
        raise SystemExit(RESOURCE_FAILURE)
    try:
        budget = declared_memory_mib({} if memory_mib is None else {'memory_mib': memory_mib})
    except ValueError as exc:
        print(f'c8q: {exc}', file=sys.stderr)
        raise SystemExit(RESOURCE_FAILURE)
    ensure_dirs()
    rid = time.strftime('%H%M%S') + '-' + secrets.token_hex(3)
    req = {'id': rid, 'path': str(path), 'build': build, 'label': label,
           'submitted': time.time(), 'client_pid': os.getpid()}
    req['memory_mib'] = budget
    write_json(REQUESTS / f'{time.time_ns()}-{rid}.json', req)
    return rid


def print_result(rid):
    meta = json.loads((DONE / f'{rid}.json').read_text())
    if not meta.get('log') or 'started' not in meta:
        print(f'c8q: {rid}: {meta.get("resource_failure_reason", "request did not run")}',
              file=sys.stderr)
        return meta['exit_code']
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
        if MEMORY_STOP.exists():
            print(memory_stop_message(), file=sys.stderr)
            return RESOURCE_FAILURE
        time.sleep(2)
    if MEMORY_STOP.exists():
        print(memory_stop_message(), file=sys.stderr)
        return RESOURCE_FAILURE
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
    print(f'resource-review latch: {MEMORY_STOP.exists()}')
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
    for lack of capacity may be requeued. Resource failures persistently stop admission;
    already active jobs may finish, but no budget is increased automatically."""
    if MEMORY_STOP.exists():
        print(memory_stop_message(), file=sys.stderr)
        return RESOURCE_FAILURE
    ensure_dirs()
    STOP.unlink(missing_ok=True)
    active = {}
    print(f'c8q runner: queue {QUEUE}, max parallel {MAX_PARALLEL}, declared reservations', flush=True)
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
            reason = resource_failure_reason(code, text)
            if reason:
                req['process_exit_code'] = code
                req['status'] = 'RESOURCE_FAILURE'
                req['resource_failure_reason'] = reason
                latch_resource_failure(req, reason)
                code = RESOURCE_FAILURE
            elif refused:
                req.pop('started', None)
                req['attempts'] = req.get('attempts', 0) + 1
                req['not_before'] = time.time() + 3
                write_json(REQUESTS / req_name, req)
                continue
            req['exit_code'] = code
            req['finished'] = time.time()
            write_json(DONE / f'{rid}.json', req)
            print(f"c8q runner: done {rid} exit {code} {req['path']} "
                  f"({req['finished'] - req['started']:.0f}s, {req['mem_used']} MiB)", flush=True)
        if MEMORY_STOP.exists():
            STOP.touch(exist_ok=True)
        if STOP.exists() and not active:
            print('c8q runner: stop flag seen, exiting', flush=True)
            return RESOURCE_FAILURE if MEMORY_STOP.exists() else 0
        limit = MAX_PARALLEL
        if limit > 1 and active and other_sessions_hold_slot(active):
            limit = 1   # leave the second guard slot to other sessions
        if not STOP.exists() and not MEMORY_STOP.exists() and len(active) < limit:
            busy_paths = {item[1]['path'] for item in active.values()}
            now = time.time()
            for req_path in sorted(REQUESTS.glob('*.json')):
                if len(active) >= limit or STOP.exists() or MEMORY_STOP.exists():
                    break
                try:
                    req = json.loads(req_path.read_text())
                except (OSError, ValueError):
                    continue
                if req['path'] in busy_paths or req.get('not_before', 0) > now:
                    continue
                rid = req['id']
                try:
                    mem = declared_memory_mib(req)
                except ValueError as exc:
                    req.update(status='RESOURCE_FAILURE', exit_code=RESOURCE_FAILURE,
                               finished=time.time(), resource_failure_reason=str(exc))
                    write_json(DONE / f'{rid}.json', req)
                    req_path.unlink()
                    latch_resource_failure(req, str(exc))
                    break
                req['mem_used'] = mem
                req['memory_mib'] = mem  # Preserve this explicit declaration on capacity retries.
                req['started'] = time.time()
                attempt = req.get('attempts', 0) + 1
                req['log'] = str(DONE / f'{rid}-attempt-{attempt}-{secrets.token_hex(4)}.log')
                req.setdefault('attempt_logs', []).append(req['log'])
                run_path = RUNNING / f'{rid}.json'
                write_json(run_path, req)
                req_name = req_path.name
                req_path.unlink(missing_ok=True)
                logf = open(req['log'], 'x')
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
        p.add_argument('--memory-mib', type=int, default=None,
                       help='reviewed memory declaration, 640..4096 MiB (no automatic estimate)')
    p = sub.add_parser('wait')
    p.add_argument('id')
    p.add_argument('--timeout', type=float, default=540)
    sub.add_parser('status')
    sub.add_parser('runner')
    args = parser.parse_args()
    if args.cmd in ('check', 'build'):
        path = resolve_source(args.file)
        rid = submit(path, args.cmd == 'build', args.label, args.memory_mib)
        print(f'c8q: submitted {args.cmd} {path} as {rid}', flush=True)
        sys.exit(wait(rid, args.timeout))
    if args.cmd == 'wait':
        sys.exit(wait(args.id, args.timeout))
    if args.cmd == 'status':
        status()
        return
    if args.cmd == 'runner':
        sys.exit(runner())


if __name__ == '__main__':
    main()

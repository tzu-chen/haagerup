"""Run one bounded numerical process on the user's shared desktop.

Usage: python hi_cft_safe_run.py -- python calculation.py [args...]
Linux RLIMIT_AS is a hard *per-process* cap, not an aggregate cgroup cap.
This launcher permits a single threaded numerical program; no worker processes
or detached jobs. An additional process-group RSS/host-availability watchdog
protects against accidental subprocesses, but its sampling is not a hard cap.
"""

import argparse
import ctypes
import fcntl
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

GIB = 1024 ** 3
LOCK = Path('/tmp/haagerup_numerical.lock')


def available_bytes():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) * 1024
    raise RuntimeError('Cannot establish host available memory')


def cgroup_headroom():
    relative = Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1]
    root = Path('/sys/fs/cgroup').resolve()
    group = (root / relative.lstrip('/')).resolve()
    if not group.is_relative_to(root):
        raise RuntimeError('Cannot resolve the numerical job cgroup safely')
    headroom = float('inf')
    while True:
        maximum = group / 'memory.max'
        if maximum.exists():
            limit = maximum.read_text().strip()
            if limit != 'max':
                current = int((group / 'memory.current').read_text())
                headroom = min(headroom, int(limit) - current)
        if group == root:
            break
        group = group.parent
    return headroom


def group_rss(pgid):
    total = 0
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / 'stat').read_text().rsplit(')', 1)[1].split()
            if int(stat[2]) == pgid:
                total += int(stat[21]) * os.sysconf('SC_PAGE_SIZE')
        except (OSError, ValueError, IndexError):
            continue
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit-mib', type=int, default=6144,
                        help='May LOWER the hard address-space cap for checks')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == '--':
        command = command[1:]
    if not command or not 64 <= args.limit_mib <= 6144:
        parser.error('Supply a command and a limit between 64 and 6144 MiB')
    with LOCK.open('a+') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            sys.exit('Refusing: another bounded numerical job holds the shared lock')
        available = available_bytes()
        if available < 32 * GIB or cgroup_headroom() < 8 * GIB:
            sys.exit('Refusing: insufficient host or cgroup memory headroom')
        env = os.environ.copy()
        for name in ['OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
                     'NUMEXPR_NUM_THREADS', 'JULIA_NUM_THREADS', 'NUMBA_NUM_THREADS',
                     'VECLIB_MAXIMUM_THREADS', 'BLIS_NUM_THREADS']:
            env[name] = '2'
        env['OMP_MAX_ACTIVE_LEVELS'] = '1'
        limit = args.limit_mib * 1024 ** 2
        cpus = set(sorted(os.sched_getaffinity(0))[:2])
        parent_pid = os.getpid()

        def constrain():
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            os.sched_setaffinity(0, cpus)
            # Kill the direct numerical child if this watchdog disappears.
            if ctypes.CDLL(None, use_errno=True).prctl(1, signal.SIGKILL) != 0:
                raise OSError(ctypes.get_errno(), 'PR_SET_PDEATHSIG failed')
            if os.getppid() != parent_pid:
                os._exit(125)

        print(f'Resource guard: AS {args.limit_mib} MiB, group RSS watchdog 8 GiB, '
              f'2 CPUs/threads, host available {available/GIB:.1f} GiB',
              file=sys.stderr, flush=True)
        child = subprocess.Popen(command, env=env, start_new_session=True,
                                 preexec_fn=constrain)
        interrupted = False

        def stop(signum, frame):
            nonlocal interrupted
            interrupted = True

        signal.signal(signal.SIGTERM, stop)
        signal.signal(signal.SIGINT, stop)
        peak = 0
        reason = None
        while child.poll() is None:
            rss = group_rss(child.pid)
            peak = max(peak, rss)
            if interrupted:
                reason = 'interrupted'
            elif rss > 8 * GIB:
                reason = 'process-group RSS exceeded 8 GiB'
            elif available_bytes() < 32 * GIB:
                reason = 'host MemAvailable fell below 32 GiB'
            elif cgroup_headroom() < GIB:
                reason = 'cgroup headroom fell below 1 GiB'
            if reason:
                print('Resource guard stopping job: ' + reason, file=sys.stderr)
                try:
                    os.killpg(child.pid, signal.SIGTERM)
                    child.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                break
            time.sleep(0.25)
        code = child.wait()
        # No numerical descendants are permitted to outlive the job.
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        print(f'Resource guard: sampled peak group RSS {peak/GIB:.3f} GiB; '
              f'exit {code}', file=sys.stderr, flush=True)
        return 125 if reason else (code if code >= 0 else 128 - code)


if __name__ == '__main__':
    sys.exit(main())

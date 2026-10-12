"""Explicit, expiring memory exception for the third six-hour window.

The permanent guard is ~/.local/bin/research-safe-run. Only one process group
may hold its shared lock. This launcher permits no worker/detached processes
and keeps two threads/CPUs. Larger limits require a written allocation review.
The full AS cap plus host reserve plus margin must be available at launch;
swap never enters that calculation. Memory breaches kill only our group.
"""
import argparse
import ctypes
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

from hi_cft_safe_run import open_shared_lock, available_bytes, cgroup_headroom, group_rss

MIB = 1024**2
WINDOW = "20260915T170457Z_6h"
START = "2026-09-15T17:04:57Z"
END = "2026-09-15T23:04:57Z"
PROFILE = Path(__file__).with_name("hi_cft_third_window_resource_profile.json")
THREAD_VARIABLES = (
    "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS", "JULIA_NUM_THREADS", "NUMBA_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS", "BLIS_NUM_THREADS",
)


def epoch(value):
    return datetime.fromisoformat(value.replace("Z", "+00:00")).timestamp()


def read_policy(now=None):
    raw = PROFILE.read_bytes()
    if len(raw) > 16384:
        raise ValueError("Oversized resource profile")
    p = json.loads(raw)
    # An edited JSON file alone cannot extend this user-authorized window.
    if (p["window_id"], p["start_utc"], p["deadline_utc"]) != (WINDOW, START, END):
        raise ValueError("Resource profile is not the authorized six-hour window")
    exact = {
        "maximum_address_mib": 36864, "maximum_group_rss_mib": 34816,
        "host_reserve_mib": 12288, "launch_margin_mib": 2048,
        "cgroup_launch_reserve_mib": 4096, "cgroup_running_reserve_mib": 2048,
        "compute_threads": 2, "numerical_jobs": 1, "swap_is_capacity": False,
    }
    if any(type(p.get(k)) is not type(v) or p[k] != v for k, v in exact.items()):
        raise ValueError("Resource profile ceilings or persistent rules changed")
    now = time.time() if now is None else now
    if not epoch(START) <= now < epoch(END) - 5:
        raise ValueError("Temporary RAM authorization is inactive or expiring")
    return p, hashlib.sha256(raw).hexdigest()


def check_budget(p, address_mib, estimated_peak_mib, available, headroom):
    if not 64 <= estimated_peak_mib <= address_mib <= p["maximum_address_mib"]:
        raise ValueError("Require 64 <= estimated peak <= AS <= authorized ceiling")
    if estimated_peak_mib > p["maximum_group_rss_mib"]:
        raise ValueError("Estimated RSS exceeds the window ceiling")
    needed = (address_mib + p["host_reserve_mib"] + p["launch_margin_mib"]) * MIB
    if available < needed:
        raise ValueError("Host lacks full-AS headroom plus 12GiB reserve and 2GiB margin")
    if headroom < (address_mib + p["cgroup_launch_reserve_mib"]) * MIB:
        raise ValueError("Applicable cgroup lacks full-AS headroom and reserve")
    # Account for modest estimate uncertainty, but do not silently use the
    # entire window ceiling when a small process was planned.
    rss_mib = min(p["maximum_group_rss_mib"], address_mib,
                  max(512, math.ceil(1.25 * estimated_peak_mib) + 256))
    return rss_mib * MIB


def kill_group(child, grace):
    try:
        os.killpg(child.pid, signal.SIGTERM if grace > 0 else signal.SIGKILL)
    except ProcessLookupError:
        return
    if grace > 0:
        try:
            child.wait(timeout=grace)
        except subprocess.TimeoutExpired:
            pass
    # No descendant is permitted to outlive the numerical process.
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def selftest():
    p, _ = read_policy(epoch(START) + 1)
    refused = 0
    for now in (epoch(START) - 1, epoch(END) - 4, epoch(END) + 1):
        try:
            read_policy(now)
        except ValueError:
            refused += 1
        else:
            raise AssertionError("Inactive/expired window accepted")
    tests = [
        (40000, 30000, 64*1024*MIB, float("inf")),
        (3072, 4000, 64*1024*MIB, float("inf")),
        (32768, 30000, 40*1024*MIB, float("inf")),
        (3072, 2000, 64*1024*MIB, 4096*MIB),
    ]
    for args in tests:
        try:
            check_budget(p, *args)
        except ValueError:
            refused += 1
        else:
            raise AssertionError("Unsafe budget accepted")
    cap = check_budget(p, 32768, 30000, 50*1024*MIB, float("inf"))
    assert cap == 32768*MIB
    return {"unsafe_or_expired_cases_refused": refused,
            "reviewed_32GiB_case_cap_mib": cap//MIB,
            "no_large_allocation_or_child_process": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit-mib", type=int)
    parser.add_argument("--estimated-peak-mib", type=int)
    parser.add_argument("--estimate-note", type=Path)
    parser.add_argument("--audit-json", type=Path)
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.selftest:
        print(json.dumps(selftest(), indent=2))
        return 0
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or args.limit_mib is None or args.estimated_peak_mib is None:
        parser.error("Explicit command, address limit and peak estimate required")
    p, policy_hash = read_policy()
    note = None
    if args.estimate_note:
        raw = args.estimate_note.read_bytes()
        if not raw or len(raw) > 512*1024:
            parser.error("Allocation note must be nonempty and at most512KiB")
        note = {"path": str(args.estimate_note.resolve()),
                "sha256": hashlib.sha256(raw).hexdigest()}
    if args.limit_mib > 6144 and note is None:
        parser.error("A written allocation review is required above6GiB")
    if args.audit_json and not args.audit_json.parent.is_dir():
        parser.error("Audit output directory must exist")
    with open_shared_lock() as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("Refusing: another numerical job holds the shared lock")
        available = available_bytes()
        headroom = cgroup_headroom()
        rss_cap = check_budget(p, args.limit_mib, args.estimated_peak_mib,
                               available, headroom)
        # Recheck after lock acquisition. Refuse a stale profile at launch.
        _, second_hash = read_policy()
        if second_hash != policy_hash:
            raise ValueError("Resource profile changed during launch")
        env = os.environ.copy()
        for name in THREAD_VARIABLES:
            env[name] = "2"
        env["OMP_MAX_ACTIVE_LEVELS"] = "1"
        cpus = set(sorted(os.sched_getaffinity(0))[:2])
        parent_pid = os.getpid()
        limit = args.limit_mib*MIB

        def constrain():
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            os.sched_setaffinity(0, cpus)
            if ctypes.CDLL(None, use_errno=True).prctl(1, signal.SIGKILL) != 0:
                raise OSError(ctypes.get_errno(), "PR_SET_PDEATHSIG failed")
            if os.getppid() != parent_pid:
                os._exit(125)

        started = time.time()
        print(f"Window guard: AS{args.limit_mib}MiB, groupRSS{rss_cap/MIB:.0f}MiB, "
              f"host reserve12GiB, available{available/(1024*MIB):.2f}GiB, "
              f"2threads/CPUs, expires{END}", file=sys.stderr, flush=True)
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
        try:
            while child.poll() is None:
                rss = group_rss(child.pid)
                peak = max(peak, rss)
                now = time.time()
                if interrupted:
                    reason = "interrupted"
                elif now >= epoch(END) - 2:
                    reason = "authorized wall-clock deadline"
                elif rss > rss_cap:
                    reason = "reviewed process-group RSS budget exceeded"
                elif available_bytes() < p["host_reserve_mib"]*MIB:
                    reason = "host reserve below12GiB"
                elif cgroup_headroom() < p["cgroup_running_reserve_mib"]*MIB:
                    reason = "applicable cgroup reserve below2GiB"
                if reason:
                    # Resource pressure is stopped immediately; graceful
                    # deadline handling begins before authorization expires.
                    grace = min(1., max(0., epoch(END)-now-0.5))
                    if "reserve" in reason or "RSS" in reason:
                        grace = 0.
                    kill_group(child, grace)
                    break
                time.sleep(.1)
            code = child.wait()
        except BaseException:
            kill_group(child, 0.)
            child.wait()
            raise
        finally:
            kill_group(child, 0.)
        result = {
            "window_id": WINDOW, "deadline_utc": END,
            "start_utc": datetime.fromtimestamp(started, timezone.utc).isoformat(),
            "finish_utc": datetime.now(timezone.utc).isoformat(),
            "command": command, "address_mib": args.limit_mib,
            "estimated_peak_mib": args.estimated_peak_mib,
            "rss_watchdog_mib": rss_cap//MIB, "sampled_peak_rss_mib": peak/MIB,
            "launch_memavailable_mib": available/MIB,
            "launch_cgroup_headroom_mib": headroom/MIB if math.isfinite(headroom) else None,
            "estimate_note": note, "profile_sha256": policy_hash,
            "reason_stopped": reason, "child_returncode": code,
            "permanent_defaults_changed": False,
        }
        if args.audit_json:
            temporary = args.audit_json.with_name(args.audit_json.name+".tmp")
            temporary.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n")
            temporary.replace(args.audit_json)
        print(json.dumps(result, allow_nan=False), file=sys.stderr, flush=True)
        return 125 if reason else (code if code >= 0 else 128-code)


if __name__ == "__main__":
    sys.exit(main())

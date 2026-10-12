#!/usr/bin/env python3
"""Typeset this textbook only; never execute a numerical research command.

TeX shell escape is disabled. Each joined foreground pass has a 768 MiB
address-space limit, one CPU, a 120 s deadline, and host/cgroup headroom
checks. Scientific calculations must use the canonical research-safe-run.
"""
from pathlib import Path
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import resource
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build"
MIB = 1024 ** 2
GIB = 1024 ** 3


def source_hashes():
    paths = list(ROOT.glob("*.tex"))
    for directory in ("chapters", "figures", "solutions"):
        paths.extend((ROOT / directory).glob("*.tex"))
    # Included vector figures are typesetting inputs too.
    paths.extend((ROOT / "figures").glob("*.pdf"))
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def host_available():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("Cannot read actual host MemAvailable")


def cgroup_headroom():
    lines = Path("/proc/self/cgroup").read_text().splitlines()
    rel = next(line.split("::", 1)[1] for line in lines if "::" in line)
    base = Path("/sys/fs/cgroup").resolve()
    current = (base / rel.lstrip("/")).resolve()
    if not current.is_relative_to(base):
        raise RuntimeError("Unexpected cgroup path")
    room = float("inf")
    while True:
        maximum = current / "memory.max"
        usage = current / "memory.current"
        if maximum.exists():
            value = maximum.read_text().strip()
            if value != "max":
                room = min(room, int(value) - int(usage.read_text()))
        if current == base:
            return room
        current = current.parent


def process_rss(pid):
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1]) * 1024
    except FileNotFoundError:
        pass
    return 0


def build(passes):
    BUILD.mkdir(exist_ok=True)
    report = {
        "scope": "Document typesetting only; no research computation or certificate replay",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": source_hashes(),
        "limits": {"address_mib": 768, "rss_mib": 512, "cpus": 1,
                   "seconds_per_pass": 120, "host_reserve_gib": 8},
        "passes": [],
    }
    env = os.environ.copy()
    for key in ("MKTEXPK", "MKTEXTFM", "MKTEXMF"):
        env[key] = "0"
    for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                "NUMBA_NUM_THREADS", "JULIA_NUM_THREADS", "NUMEXPR_NUM_THREADS",
                "BLIS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
        env[key] = "1"
    affinity = {min(os.sched_getaffinity(0))}

    def constrain():
        resource.setrlimit(resource.RLIMIT_AS, (768 * MIB, 768 * MIB))
        resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        os.sched_setaffinity(0, affinity)

    def run_editorial_step(number, kind, command):
        if host_available() < 8 * GIB + 768 * MIB:
            raise RuntimeError("Host reserve insufficient for bounded typesetting")
        if cgroup_headroom() < 768 * MIB:
            raise RuntimeError("Cgroup headroom insufficient for bounded typesetting")
        log = BUILD / (f"pass_{number}.log" if kind == "pdflatex"
                       else f"index_{number}.log")
        start = time.monotonic()
        peak = 0
        minimum = host_available()
        reason = None
        with log.open("w") as stream:
            child = subprocess.Popen(
                command, cwd=ROOT, env=env,
                stdout=stream, stderr=subprocess.STDOUT,
                start_new_session=True, preexec_fn=constrain)
            try:
                while child.poll() is None:
                    peak = max(peak, process_rss(child.pid))
                    minimum = min(minimum, host_available())
                    if minimum < 8 * GIB:
                        reason = "host memory reserve"
                    elif cgroup_headroom() < 128 * MIB:
                        reason = "cgroup memory headroom"
                    elif peak > 512 * MIB:
                        reason = "typesetter RSS ceiling"
                    elif time.monotonic() - start > 120:
                        reason = "typesetting deadline"
                    if reason:
                        os.killpg(child.pid, signal.SIGKILL)
                        break
                    time.sleep(0.1)
                code = child.wait()
            finally:
                if child.poll() is None:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
        row = {"pass": number, "kind": kind, "exit_code": code,
               "seconds": round(time.monotonic() - start, 3),
               "sampled_peak_rss_mib": round(peak / MIB, 2),
               "minimum_host_available_gib": round(minimum / GIB, 3),
               "stop_reason": reason, "log": str(log.relative_to(ROOT))}
        report["passes"].append(row)
        (BUILD / "build_record.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(row), flush=True)
        if code or reason:
            print("\n".join(log.read_text().splitlines()[-30:]))
            raise SystemExit(code or 1)
    for number in range(1, passes + 1):
        run_editorial_step(number, "pdflatex",
            ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
             "-halt-on-error", "-file-line-error", "-output-directory=build",
             "haagerup_cft_textbook.tex"])
        run_editorial_step(number, "makeindex",
            ["makeindex", "-o", "build/haagerup_cft_textbook.ind",
             "-t", "build/haagerup_cft_textbook.ilg",
             "build/haagerup_cft_textbook.idx"])
    if source_hashes() != report["source_sha256"]:
        raise RuntimeError("Textbook sources or figure assets changed during compilation; rebuild the final edition")
    pdf = BUILD / "haagerup_cft_textbook.pdf"
    shutil.copyfile(pdf, ROOT / pdf.name)
    report["completed_utc"] = datetime.now(timezone.utc).isoformat()
    report["pdf_sha256"] = hashlib.sha256(pdf.read_bytes()).hexdigest()
    report["pdf_bytes"] = pdf.stat().st_size
    (BUILD / "build_record.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--passes", type=int, choices=range(1, 5), default=3)
    build(parser.parse_args().passes)

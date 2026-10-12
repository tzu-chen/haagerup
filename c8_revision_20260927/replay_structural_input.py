"""Replay an unchanged structural producer into a fresh revision output.

Reviewed selectors: potts, pf13_membership. Run only through
hi_cft_safe_run.py --limit-mib 2048, with an outer timeout of 600 seconds.
The original producer's pathlib constructor is intercepted only when it
requests its one hardcoded output. The original code and every input path
remain unchanged. The produced JSON must equal the frozen record after
removing timing/RSS fields, before an exclusive atomic output installation.

Allocation review: bounded grade-three sparse mode caches, at most120 S2
vectors and58 Cartan-zero S3 pivots; imported NumPy/SciPy only performs the
small lattice module initialization in these two producer paths. No floating
search, ambient grade-three basis, or worker is launched. Prior measured RSS
was98MiB (Potts) and117MiB (PF13 membership); conservative reviewed ceiling
is0.75GiB RSS, with a2GiB address limit. Root owns all executions.
"""

import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import resource
import sys


ROOT = Path(__file__).resolve().parents[1]
REVISION = ROOT / "c8_revision_20260927"
MAX_JSON = 8 * 1024 ** 2
PRODUCERS = {
    "potts": "hi_cft_20260923_proof_potts_exact",
    "pf13_membership": "hi_cft_20260923_proof_pf13_membership",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 ** 2), b""):
            digest.update(block)
    return digest.hexdigest()


def load(path):
    require(Path(path).stat().st_size <= MAX_JSON, "JSON exceeds reviewed cap")
    return json.loads(Path(path).read_text())


def stable(value):
    return {key: item for key, item in value.items()
            if key not in ("seconds", "peak_rss_KiB")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=sorted(PRODUCERS))
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    require(Path.cwd().resolve() == ROOT, "run from the repository root")
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    require(0 < cap <= 2 * 1024 ** 3, "requires address cap at most2GiB")
    require(len(os.sched_getaffinity(0)) <= 2, "requires at most two CPUs")
    for variable in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
        require(os.environ.get(variable) in ("1", "2"),
                "requires launcher thread cap: " + variable)

    name = PRODUCERS[args.kind]
    source, original = ROOT / (name + ".py"), ROOT / (name + ".json")
    output = Path(args.output).resolve()
    require(output.parent == REVISION and output.suffix == ".json",
            "output must be a JSON file directly in the revision directory")
    require(not output.exists(), "refusing to overwrite output")
    temporary = output.with_name(output.name + ".tmp")
    require(not temporary.exists(), "refusing to overwrite temporary output")
    frozen = load(ROOT / "hi_cft_20260923_c8two_proof_bundle.json")
    hashes = frozen["source_sha256"]
    require(str(source) in hashes and str(original) in hashes,
            "producer and original record must be frozen ledger inputs")
    require(sha(source) == hashes[str(source)], "producer changed since frozen ledger")
    require(sha(original) == hashes[str(original)], "original record changed")
    expected = load(original)
    counters = {"output_path_requests": 0, "output_writes": 0}

    class FreshOutput(type(Path())):
        def write_text(self, data, encoding=None, errors=None, newline=None):
            require(self == output, "unexpected output target")
            require(counters["output_path_requests"] == 1,
                    "output path must have been requested exactly once")
            require(counters["output_writes"] == 0, "second output write rejected")
            encoded = data.encode(encoding or "utf-8", errors or "strict")
            require(len(encoded) <= MAX_JSON, "output exceeds reviewed JSON cap")
            actual = json.loads(data)
            require(stable(actual) == stable(expected),
                    "replayed mathematical data differs from the frozen record")
            with temporary.open("xb") as stream:
                stream.write(encoded)
                stream.flush()
                os.fsync(stream.fileno())
            os.link(temporary, output)
            temporary.unlink()
            counters["output_writes"] += 1
            return len(data)

    def producer_path(*parts):
        requested = Path(*parts)
        if requested.resolve() == original:
            counters["output_path_requests"] += 1
            require(counters["output_path_requests"] == 1,
                    "unexpected repeated access to the hardcoded output path")
            return FreshOutput(output)
        return requested

    sys.path.insert(0, str(ROOT))
    producer = importlib.import_module(name)
    require(Path(producer.__file__).resolve() == source, "unexpected imported producer")
    require(producer.Path is Path, "producer pathlib constructor differs from reviewed source")
    producer.Path = producer_path
    producer.main()
    require(counters == {"output_path_requests": 1, "output_writes": 1},
            "output interception did not have exactly one request and write")
    require(sha(source) == hashes[str(source)] and sha(original) == hashes[str(original)],
            "original source or certificate changed during replay")
    require(stable(load(output)) == stable(expected), "installed replay record differs")
    print(json.dumps({
        "adapter_status": "unchanged_producer_exact_replay_passed",
        "kind": args.kind,
        "source": str(source), "source_sha256": sha(source),
        "original_certificate": str(original),
        "original_certificate_sha256": sha(original),
        "adapter_sha256": sha(__file__), "output": str(output),
        "output_interception": counters,
        "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }), flush=True)


if __name__ == "__main__":
    main()

"""Independently check all twelve Gate 4 residuals from portable text data.

Reads only --packet (gzip JSONL) and --relations (finite_witnesses.json).
No original database, VOA engine, numerical package, or external field code
is used. The original source hashes inside the header are provenance only.
Run through ~/.local/bin/research-safe-run with --limit-mib 1024. The checker rereads the
packet once per target, retaining one target residual and one source vector.
Expected RSS <192 MiB; internal refusal at384 MiB, alarm360 seconds. Each
line is at most8 MiB, each vector at most5000 states, packet at most256 MiB
uncompressed and64 MiB compressed. Fractions use the basis1,s,t,st.
"""

import argparse
from fractions import Fraction as Q
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
from time import monotonic


MIB = 1024 ** 2
ZERO = (Q(0),) * 4
FORMAT = "portable-gate4-saved-vectors-v1"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def boundary():
    need(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 384 * 1024,
         "384 MiB RSS review boundary")


def guard():
    need(0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024 * MIB,
         "use permanent launcher with address cap <=1024 MiB")
    need(len(os.sched_getaffinity(0)) <= 2, "at most two CPUs")
    parent = Path("/proc") / str(os.getppid())
    argv = (parent / "cmdline").read_bytes().split(b"\0")
    need(len(argv) > 1, "missing resource watchdog parent")
    launcher = Path(os.fsdecode(argv[1]))
    if not launcher.is_absolute():
        launcher = (parent / "cwd").resolve() / launcher
    need(launcher.resolve() == (Path.home() / ".local/bin/research-safe-run").resolve(),
         "global research-safe-run watchdog parent required")
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError("360 second cap")))
    signal.alarm(360)


def sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(MIB), b""):
            result.update(block)
            boundary()
    return result.hexdigest()


def compact(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def field(parts, max_bits=4096):
    need(len(parts) == 4 and all(isinstance(v, str) and len(v) <= 2600 for v in parts),
         "bounded four-component coefficient")
    value = tuple(Q(v) for v in parts)
    need(all(max(abs(v.numerator).bit_length(), v.denominator.bit_length()) <= max_bits
             for v in value), "coefficient bit limit")
    return value


def multiply(a, b):
    value = [Q(0)] * 4
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    common = i & j
                    value[i ^ j] += x * y * (13 if common & 1 else 1) * (-3 if common & 2 else 1)
    return tuple(value)


def vector(record):
    need(len(record) <= 5000, "5000-state vector cap")
    result = {}
    for momentum, oscillators, coefficients in record:
        need(len(momentum) == 8 and all(isinstance(x, int) for x in momentum), "momentum encoding")
        need(all(isinstance(x, int) and 0 <= x < 32 for x in oscillators), "oscillator encoding")
        state = (tuple(momentum), tuple(oscillators))
        c = field(coefficients, 2048)
        need(state not in result and any(c), "duplicate or zero coefficient")
        result[state] = c
    return result


def packet_rows(path, relations_sha):
    need(path.stat().st_size <= 64 * MIB, "compressed packet size cap")
    total, count = 0, 0
    with gzip.open(path, "rb") as stream:
        while True:
            line = stream.readline(8 * MIB + 1)
            if not line:
                break
            total += len(line)
            need(len(line) <= 8 * MIB and line.endswith(b"\n") and total <= 256 * MIB,
                 "JSONL record/total size cap")
            row = json.loads(line)
            if count == 0:
                need(row["format"] == FORMAT and row["kind"] == "header"
                     and row["vector_count"] == 33 and row["relations_sha256"] == relations_sha,
                     "packet header or relation binding")
                need(row["field_basis"] == ["1", "s", "t", "s*t"]
                     and row["field_relations"] == {"s^2": 13, "t^2": -3}, "field convention")
            else:
                i = count - 1
                expected = "target:" + str(i) if i < 12 else "normal:" + str(i - 12)
                need(row["kind"] == "vector" and row["name"] == expected,
                     "target-first canonical vector order")
                need(len(row["vector"]) == row["terms"] <= 5000 and row["bits"] <= 2048,
                     "vector size metadata")
                need(hashlib.sha256(compact(row["vector"])).hexdigest() == row["record_sha256"],
                     "original exact vector record digest")
                yield row
            count += 1
            boundary()
    need(count == 34, "one header and exactly33 vectors required")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True)
    parser.add_argument("--relations", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    guard()
    started = monotonic()
    packet, relations_path, output = map(Path, (args.packet, args.relations, args.output))
    need(not output.exists(), "refusing to overwrite output")
    need(relations_path.stat().st_size <= 8 * MIB, "relations size cap")
    relations_sha = sha(relations_path)
    relations = json.loads(relations_path.read_text())
    need(relations["format"] == "human-readable-finite-witnesses-v1"
         and relations["status"] == "all_requested_saved_data_checks_passed", "relations format")
    identities = relations["gate4"]["identities"]
    need(len(identities) == 12, "twelve relations required")
    answers = []
    for target_index, identity in enumerate(identities):
        need(identity["id"] == target_index, "relation numbering")
        coefficients = {}
        for j, parts in identity["normal_column_coefficients"]:
            need(isinstance(j, int) and 0 <= j < 21 and j not in coefficients, "normal column indices")
            coefficients[j] = field(parts)
        residual = None
        target_terms = None
        used = set()
        for row in packet_rows(packet, relations_sha):
            kind, index_text = row["name"].split(":")
            index = int(index_text)
            if kind == "target" and index == target_index:
                residual = vector(row["vector"])
                target_terms = len(residual)
                need(target_terms == identity["target_terms"], "target term agreement")
            elif kind == "normal" and index in coefficients:
                need(residual is not None, "target must precede normal columns")
                source = vector(row["vector"])
                for state, value in source.items():
                    product = multiply(coefficients[index], value)
                    result = tuple(a - b for a, b in zip(residual.get(state, ZERO), product))
                    if any(result):
                        residual[state] = result
                    else:
                        residual.pop(state, None)
                used.add(index)
                del source
        need(residual is not None and not residual and used == set(coefficients),
             "nonzero or incomplete projected residual")
        answers.append({"id": target_index, "target_terms": target_terms,
                        "columns_used": len(used), "full_fraction_residual_zero": True})
    result = {"format": "portable-gate4-residual-replay-v1", "status": "all_twelve_residuals_zero",
              "identities": answers, "packet_sha256": sha(packet), "relations_sha256": relations_sha,
              "checker_sha256": sha(Path(__file__)), "seconds": monotonic() - started,
              "resource_guard_sha256": sha(Path.home() / ".local/bin/research-safe-run"),
              "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              "scope": "Full exact residual replay using only portable saved vectors and their relation coefficients. Does not reconstruct ambient vertex modes, projector application, normal-word membership, raising premises, or rank witnesses."}
    with output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({key: result[key] for key in ("status", "seconds", "peak_rss_KiB")}), flush=True)


if __name__ == "__main__":
    main()

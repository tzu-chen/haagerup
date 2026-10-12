"""Export the33 Gate4 projected vectors to a portable capped gzip JSONL file.

Root-only guarded export; no mode products or solver. Reads the 2.8 MiB
exact SQLite file and finite_witnesses.json. Standard library only, <=8 MiB
decoded record, SQLite cache1 MiB, no vector cache. Expected RSS<64 MiB;
the shared helper refuses at384 MiB and360 seconds, AS<=1 GiB. Original
records are unchanged. Separate check_gate4_packet.py reads only the new
packet and relation JSON and independently recomputes all12 residuals.
"""

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sqlite3
import zlib

from check_gate4_packet import MIB, FORMAT, boundary, compact, guard, need, sha


ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--relations", default="c8_reviewability_20260927/finite_witnesses.json")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    guard()
    source = ROOT / "hi_cft_20260923_c8two_h4_singlet_exact.sqlite"
    relations_path, output = Path(args.relations).resolve(), Path(args.output).resolve()
    need(output.is_relative_to(ROOT) and not output.exists(), "output must be new and in repository")
    need(relations_path.stat().st_size <= 8 * MIB and source.stat().st_size <= 32 * MIB,
         "input size caps")
    need(not any(Path(str(source) + suffix).exists() for suffix in ("-journal", "-wal")),
         "source database must be closed")
    relations = json.loads(relations_path.read_text())
    need(relations["format"] == "human-readable-finite-witnesses-v1"
         and relations["status"] == "all_requested_saved_data_checks_passed", "relation packet status")
    need(len(relations["gate4"]["identities"]) == 12, "twelve source relations")
    used = {j for row in relations["gate4"]["identities"] for j, _ in row["normal_column_coefficients"]}
    need(used == set(range(21)), "all21 selected columns must occur")
    source_hash = sha(source)
    need(relations["source_sha256"][source.name] == source_hash,
         "exact database must match independently checked relation packet")
    header = {"format": FORMAT, "kind": "header", "vector_count": 33,
              "field_basis": ["1", "s", "t", "s*t"], "field_relations": {"s^2": 13, "t^2": -3},
              "relations_file": relations_path.name, "relations_sha256": sha(relations_path),
              "source_sha256": relations["source_sha256"],
              "exporter_sha256": sha(Path(__file__)),
              "checker_sha256": sha(Path(__file__).with_name("check_gate4_packet.py")),
              "scope": "Exact saved projected vectors only. Projector/ambient-mode interpretation remains an authenticated producer input."}
    total_bytes, total_terms = 0, 0
    with sqlite3.connect(source.as_uri() + "?mode=ro&immutable=1", uri=True) as db:
        db.execute("PRAGMA cache_size=-1024")
        db.execute("PRAGMA mmap_size=0")
        with output.open("xb") as raw_output:
            with gzip.GzipFile(filename="", fileobj=raw_output, mode="wb", mtime=0) as stream:
                stream.write(compact(header) + b"\n")
                for index in range(33):
                    original = "target:" + str(index) if index < 12 else "grade5:" + str(index - 12)
                    exported = "target:" + str(index) if index < 12 else "normal:" + str(index - 12)
                    found = db.execute("SELECT record,digest,terms,bits FROM vectors WHERE name=?", (original,)).fetchone()
                    need(found is not None, "missing exact vector")
                    blob, digest, terms, bits = found
                    decoder = zlib.decompressobj()
                    raw = decoder.decompress(blob, 8 * MIB + 1)
                    need(len(raw) <= 8 * MIB and decoder.eof and not decoder.unconsumed_tail
                         and not decoder.unused_data, "bounded complete zlib record")
                    need(hashlib.sha256(raw).hexdigest() == digest, "original record digest")
                    need(terms <= 5000 and bits <= 2048, "saved vector bounds")
                    record = json.loads(raw)
                    need(len(record) == terms and compact(record) == raw, "canonical vector record")
                    row = {"kind": "vector", "name": exported, "original_name": original,
                           "record_sha256": digest, "terms": terms, "bits": bits, "vector": record}
                    line = compact(row) + b"\n"
                    need(len(line) <= 8 * MIB, "JSONL line cap")
                    stream.write(line)
                    total_bytes += len(line)
                    total_terms += terms
                    need(total_bytes <= 256 * MIB, "uncompressed packet cap")
                    del record, row, line, raw
                    boundary()
    need(output.stat().st_size <= 64 * MIB, "compressed output cap")
    print(json.dumps({"status": "exported_33_projected_vectors", "vectors": 33,
                      "total_terms": total_terms, "uncompressed_vector_bytes": total_bytes,
                      "compressed_bytes": output.stat().st_size, "packet_sha256": sha(output)}), flush=True)


if __name__ == "__main__":
    main()

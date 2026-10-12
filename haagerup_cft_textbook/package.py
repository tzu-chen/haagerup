#!/usr/bin/env python3
"""Package the textbook sources and editorial records, without research execution."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import zipfile

from build import source_hashes

ROOT = Path(__file__).resolve().parent
PINNED = {}


def checked_bytes(path):
    payload = path.read_bytes()
    identity = (hashlib.sha256(payload).hexdigest(), len(payload))
    previous = PINNED.setdefault(path.resolve(), identity)
    if previous != identity:
        raise SystemExit("File changed after package validation: " + str(path))
    return payload


def digest(path):
    return hashlib.sha256(checked_bytes(path)).hexdigest()


def read_json(path):
    return json.loads(checked_bytes(path))


def main():
    audit = read_json(ROOT / "editorial/document_audit.json")
    record = read_json(ROOT / "build/build_record.json")
    sources = source_hashes()
    if audit["errors"]:
        raise SystemExit("Resolve the document audit before packaging")
    if audit.get("source_sha256") != sources:
        raise SystemExit("Rerun the document audit for the current sources and assets")
    if record.get("source_sha256") != sources:
        raise SystemExit("The PDF does not record the current TeX sources and figure assets; rebuild")
    for name, expected in sources.items():
        if digest(ROOT / name) != expected:
            raise SystemExit("Source changed after build comparison: " + name)
    pdf = ROOT / "haagerup_cft_textbook.pdf"
    if record.get("pdf_sha256") != digest(pdf):
        raise SystemExit("The delivered PDF differs from the recorded final build")
    navigation = read_json(ROOT / "editorial/pdf_audit.json")
    if navigation["errors"] or navigation["pdf_sha256"] != digest(pdf):
        raise SystemExit("Audit navigation in the current PDF before packaging")
    if any(row["exit_code"] or row["stop_reason"] for row in record["passes"]):
        raise SystemExit("The recorded build has an unsuccessful pass")
    # A code update must not silently inherit an earlier successful run.
    checks = [
        ("check_examples.py", "editorial/example_check_results.json"),
        ("check_order_three.py", "editorial/order_three_check_results.json"),
        ("check_core_tops.py", "editorial/core_top_check_results.json"),
        ("editorial/checker_history/20261005_initial_check_examples.py",
         "editorial/checker_history/20261005_initial_example_check_results.json"),
    ]
    for script_name, result_name in checks:
        result = read_json(ROOT / result_name)
        if result["script_sha256"] != digest(ROOT / script_name):
            raise SystemExit("Checker source does not match its run: " + script_name)
    plot = read_json(ROOT / "editorial/ising_calibration_plot_provenance.json")
    if plot["execution"]["script_sha256"] != digest(ROOT / "plot_ising_calibration.py"):
        raise SystemExit("Plot script differs from its recorded generation")
    for output in plot["outputs"]:
        if output["sha256"] != digest(ROOT / output["path"]):
            raise SystemExit("Plot asset differs from its recorded generation: " + output["path"])

    snapshot = read_json(ROOT / "editorial/scientific_source_snapshot.json")
    if (not snapshot.get("completed_utc") or not snapshot.get("scope")
            or not snapshot.get("groups") or snapshot.get("source_files", 0) <= 0):
        raise SystemExit("The final selected-source snapshot is missing its dated inventory")
    unique_records = {entry["path"]: entry for group in snapshot["groups"].values()
                      for entry in group}
    if len(unique_records) != snapshot["source_files"]:
        raise SystemExit("The selected-source snapshot count is inconsistent")
    for entry in unique_records.values():
        if (len(entry.get("sha256", "")) != 64
                or any(char not in "0123456789abcdef" for char in entry["sha256"])
                or not isinstance(entry.get("bytes"), int) or entry["bytes"] < 0):
            raise SystemExit("Invalid selected-source identity: " + entry["path"])

    paths = [ROOT / "README.txt"]
    paths.extend(ROOT.glob("*.tex"))
    paths.extend(ROOT.glob("*.py"))
    for directory in ("chapters", "figures", "solutions"):
        paths.extend((ROOT / directory).glob("*.tex"))
    for suffix in ("*.pdf", "*.svg"):
        paths.extend((ROOT / "figures").glob(suffix))
    for path in (ROOT / "editorial").rglob("*"):
        if path.is_file() and path.suffix in (".md", ".org", ".txt", ".json", ".py"):
            paths.append(path)
    paths.append(ROOT / "build/build_record.json")
    paths.append(ROOT / "build/haagerup_cft_textbook.log")
    # A file validated above remains required even if a later directory
    # listing no longer finds it. The delivered PDF is packaged separately.
    paths.extend(path for path in PINNED if path != pdf.resolve())
    paths = sorted(set(paths))
    for path in paths:
        if not path.is_file() or not path.resolve().is_relative_to(ROOT):
            raise SystemExit(f"Missing or out-of-tree source: {path}")

    now = datetime.now(timezone.utc)
    manifest = {
        "title": "Haagerup Symmetry and Conformal Field Theory",
        "packaged_utc": now.isoformat(),
        "scope": "Self-contained typesetting sources and editorial checks; research datasets are not included",
        "counts": {key: audit[key] for key in
                   ("main_chapters", "worked_examples", "exercises",
                    "exercises_with_dedicated_solutions")},
        "separate_pdf": {"file": pdf.name, "sha256": digest(pdf),
                         "bytes": PINNED[pdf.resolve()][1], "pages": navigation["pages"]},
        "files": {str(path.relative_to(ROOT)):
                  {"sha256": digest(path), "bytes": PINNED[path.resolve()][1]}
                  for path in paths},
    }
    manifest_path = ROOT / "manifest.json"
    manifest_payload = (json.dumps(manifest, indent=2) + "\n").encode()
    PINNED[manifest_path.resolve()] = (
        hashlib.sha256(manifest_payload).hexdigest(), len(manifest_payload))
    manifest_path.write_bytes(manifest_payload)
    paths.append(manifest_path)
    archive = ROOT / "haagerup_cft_textbook_sources.zip"
    temporary = ROOT / (archive.name + ".tmp")
    timestamp = (now.year, now.month, now.day, now.hour, now.minute, now.second)
    try:
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED,
                             compresslevel=6) as bundle:
            for path in paths:
                name = ROOT.name + "/" + str(path.relative_to(ROOT))
                info = zipfile.ZipInfo(name, date_time=timestamp)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                payload = checked_bytes(path)
                if path != manifest_path:
                    expected = manifest["files"][str(path.relative_to(ROOT))]["sha256"]
                    if hashlib.sha256(payload).hexdigest() != expected:
                        raise RuntimeError("Source changed during packaging: " + name)
                bundle.writestr(info, payload)
        with zipfile.ZipFile(temporary) as bundle:
            bad = bundle.testzip()
            if bad:
                raise RuntimeError("Archive integrity failure: " + bad)
            if len(bundle.namelist()) != len(paths):
                raise RuntimeError("Archive member count differs from source list")
        # The PDF is delivered alongside the ZIP rather than inside it.
        # Check its pinned identity before committing the new archive too.
        digest(pdf)
        temporary.replace(archive)
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps({"archive": str(archive), "bytes": archive.stat().st_size,
                      "sha256": digest(archive), "source_files": len(paths),
                      "pdf_sha256": digest(pdf)}, indent=2))


if __name__ == "__main__":
    main()

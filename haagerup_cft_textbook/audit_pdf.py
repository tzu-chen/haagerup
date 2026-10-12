#!/usr/bin/env python3
"""Inspect generated PDF navigation; no mathematical computation or web requests."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess

ROOT = Path(__file__).resolve().parent


def groups(text):
    """Read top-level TeX brace groups in a newlabel record."""
    result, start, depth = [], 0, 0
    for i, char in enumerate(text):
        if i and text[i - 1] == "\\":
            continue
        if char == "{":
            if depth == 0:
                start = i + 1
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                result.append(text[start:i])
    if depth:
        raise ValueError("Unbalanced auxiliary-file record")
    return result


def main():
    pdf = ROOT / "haagerup_cft_textbook.pdf"
    structure = ROOT / "build/pdf_structure.json"

    def constrain():
        resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
        resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})

    with structure.open("w") as output:
        subprocess.run(["qpdf", "--json", str(pdf)], stdout=output,
                       check=True, timeout=25, preexec_fn=constrain)
    data = json.loads(structure.read_text())
    objects = data["qpdf"][1]
    pages = {row["object"]: i + 1 for i, row in enumerate(data["pages"])}
    names = {}
    for row in objects.values():
        value = row.get("value", {})
        if isinstance(value, dict) and isinstance(value.get("/Names"), list):
            entries = value["/Names"]
            names.update(zip(entries[::2], entries[1::2]))

    def destination_page(value, depth=0):
        if depth > 10:
            return None
        if isinstance(value, list):
            return pages.get(value[0]) if value else None
        if isinstance(value, dict):
            return destination_page(value.get("/D"), depth + 1)
        if isinstance(value, str):
            if value in names:
                return destination_page(names[value], depth + 1)
            row = objects.get("obj:" + value)
            if row:
                return destination_page(row.get("value"), depth + 1)
        return None

    internal, external, errors = [], 0, []
    for key, row in objects.items():
        value = row.get("value", {})
        if not isinstance(value, dict) or value.get("/Subtype") != "/Link":
            continue
        action = value.get("/A", {})
        if action.get("/S") == "/GoTo":
            target = action.get("/D")
            internal.append(target)
            if destination_page(target) is None:
                errors.append({"unresolved_internal_link": key, "target": target})
        elif action.get("/S") == "/URI":
            external += 1

    solution_pages = {}
    aux = (ROOT / "build/haagerup_cft_textbook.aux").read_text()
    for line in aux.splitlines():
        if not line.startswith(r"\newlabel{sol:ex:"):
            continue
        key, body = groups(line)
        fields = groups(body)
        target = "u:" + fields[3]
        page = destination_page(target)
        solution_pages[key] = {"pdf_page": page, "printed_page": fields[1]}
        if page is None or target not in internal:
            errors.append({"missing_linked_solution_destination": key})
    document = json.loads((ROOT / "editorial/document_audit.json").read_text())
    expected = document["exercises"]
    if len(solution_pages) != expected:
        errors.append({"solution_anchor_count": len(solution_pages), "expected": expected})

    example_targets = set()
    example_list = ROOT / "build/haagerup_cft_textbook.loe"
    for line in example_list.read_text().splitlines():
        if not line.startswith(r"\contentsline"):
            continue
        fields = groups(line)
        if not fields or fields[0] != "workedexample":
            continue
        if len(fields) != 4:
            errors.append({"malformed_worked_example_entry": line})
            continue
        target = "u:" + fields[3]
        if target in example_targets:
            errors.append({"duplicate_worked_example_destination": target})
        example_targets.add(target)
        if destination_page(target) is None or target not in internal:
            errors.append({"missing_linked_worked_example": target})
    if len(example_targets) != document["worked_examples"]:
        errors.append({"worked_example_links": len(example_targets),
                       "expected": document["worked_examples"]})

    def outline_count(rows):
        count = 0
        for row in rows:
            count += 1
            if not 1 <= row.get("destpageposfrom1", 0) <= len(pages):
                errors.append({"invalid_bookmark": row.get("title")})
            count += outline_count(row.get("kids", []))
        return count

    bookmarks = outline_count(data["outlines"])
    report = {
        "scope": "PDF navigation and destination integrity; no mathematical certification or external-link verification",
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
        "pages": len(pages), "internal_links": len(internal),
        "external_links": external, "bookmarks": bookmarks,
        "top_level_bookmarks": [row["title"] for row in data["outlines"]],
        "linked_solution_anchors": len(solution_pages),
        "linked_worked_examples": len(example_targets),
        "solution_pages": solution_pages, "errors": errors,
    }
    (ROOT / "editorial/pdf_audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key != "solution_pages"}, indent=2))
    raise SystemExit(bool(errors))


if __name__ == "__main__":
    main()

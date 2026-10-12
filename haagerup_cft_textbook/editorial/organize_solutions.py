#!/usr/bin/env python3
"""Reorganize textbook solutions without changing any solution body.

This is a bounded, standard-library-only text transformation, not a numerical
research job. Coordinate with the chapter authors before either invocation:

    python editorial/organize_solutions.py --dry-run
    python editorial/organize_solutions.py --apply

The first command changes no book source. It writes a reviewable JSON report.
The second requires the exact source/plan fingerprint from that dry run.
Validation of the complete plan precedes all book-source mutations. Originals
are archived verbatim before aggregate inputs are removed. On an ordinary
write failure, the transaction restores all original source bytes.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
AGGREGATES = tuple(f"{letter}_solutions" for letter in ("r", "f", "c", "l"))
HEADING_NAMES = {"part", "chapter", "section", "subsection", "subsubsection",
                 "paragraph", "subparagraph"}
COMMAND_RE = re.compile(r"\\([A-Za-z@]+|.)", re.DOTALL)
SAFE_NAME_RE = re.compile(r"[A-Za-z0-9_]+\Z")
SAFE_LABEL_RE = re.compile(r"[A-Za-z0-9_:.-]+\Z")


class InvalidSource(ValueError):
    """A source ambiguity that must be resolved before moving text."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidSource(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def escaped(text: str, pos: int) -> bool:
    count = 0
    while pos > 0 and text[pos - 1] == "\\":
        count += 1
        pos -= 1
    return bool(count % 2)


def uncomment(text: str) -> str:
    """Mask comments with spaces while preserving every original offset."""
    chars = list(text)
    index = 0
    while index < len(text):
        if text[index] == "%" and not escaped(text, index):
            end = text.find("\n", index)
            if end < 0:
                end = len(text)
            chars[index:end] = " " * (end - index)
            index = end
        else:
            index += 1
    return "".join(chars)


def balanced(text: str, start: int, left: str = "{", right: str = "}") -> int:
    """Return one past a balanced argument, respecting escaped delimiters."""
    require(start < len(text) and text[start] == left,
            f"Expected {left!r} at offset {start}")
    depth = 1
    cursor = start + 1
    while cursor < len(text):
        char = text[cursor]
        if char == left and not escaped(text, cursor):
            depth += 1
        elif char == right and not escaped(text, cursor):
            depth -= 1
            if not depth:
                return cursor + 1
        cursor += 1
    raise InvalidSource(f"Unclosed {left!r} argument at offset {start}")


@dataclass(frozen=True)
class Command:
    name: str
    start: int
    end: int
    body_start: int
    body_end: int
    starred: bool = False
    optional: bool = False


def commands(text: str, names: set[str]) -> list[Command]:
    """Find named commands with balanced required arguments, not regex bodies."""
    masked = uncomment(text)
    result = []
    cursor = 0
    while match := COMMAND_RE.search(masked, cursor):
        cursor = match.end()
        name = match.group(1)
        if name not in names:
            continue
        starred = cursor < len(masked) and masked[cursor] == "*"
        cursor += int(starred)
        while cursor < len(masked) and masked[cursor].isspace():
            cursor += 1
        optional = cursor < len(masked) and masked[cursor] == "["
        if optional:
            cursor = balanced(masked, cursor, "[", "]")
            while cursor < len(masked) and masked[cursor].isspace():
                cursor += 1
        end = balanced(masked, cursor)
        result.append(Command(name, match.start(), end, cursor + 1, end - 1,
                              starred, optional))
        cursor = end
    return result


def argument(text: str, command: Command) -> str:
    return text[command.body_start:command.body_end]


def only_whitespace(text: str, context: str) -> None:
    # Strict on purpose: even an unattached comment is not silently discarded.
    require(not text.strip(), f"Unmatched text {context}: {text[:120]!r}")


def line_at(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


@dataclass(frozen=True)
class Exercise:
    label: str
    chapter: str
    order: int
    start: int
    end_start: int
    end: int


@dataclass(frozen=True)
class Solution:
    source: str
    line: int
    heading: str
    labels: tuple[str, ...]
    body: str


def extract_solutions(name: str, text: str) -> tuple[list[Solution], list[str]]:
    headings = commands(text, HEADING_NAMES)
    require(bool(headings), f"No solution headings in {name}")
    only_whitespace(text[:headings[0].start], f"before first heading in {name}")
    blocks, discarded_sections = [], []
    for index, heading in enumerate(headings):
        end = headings[index + 1].start if index + 1 < len(headings) else len(text)
        title = argument(text, heading)
        body = text[heading.end:end]
        context = f"{name}:{line_at(text, heading.start)}"
        require(not heading.optional, f"Optional heading not supported at {context}")
        is_solution = re.match(r"Exercises?\b", title) is not None
        if not is_solution:
            require(heading.name == "section", f"Unrecognized heading at {context}: {title}")
            only_whitespace(body, f"following section at {context}")
            discarded_sections.append(title)
            continue
        require(heading.name in {"paragraph", "subsection"},
                f"Unexpected solution heading level at {context}")
        refs = commands(title, {"ref"})
        labels = tuple(argument(title, ref) for ref in refs)
        require(bool(labels), f"No exercise references in solution heading at {context}")
        require(all(label.startswith("ex:") and SAFE_LABEL_RE.fullmatch(label) for label in labels),
                f"Non-exercise reference or unsafe label in heading at {context}")
        require(len(labels) == len(set(labels)), f"Repeated exercise in heading at {context}")
        require(title.startswith("Exercises") == (len(labels) > 1),
                f"Singular/plural solution heading disagrees with label count at {context}")
        require(bool(uncomment(body).strip()), f"Empty solution body at {context}")
        blocks.append(Solution(name, line_at(text, heading.start), title, labels, body))
    return blocks, discarded_sections


def extract_exercises(chapter: str, text: str) -> tuple[str, list[Exercise]]:
    chapter_commands = commands(text, {"chapter"})
    require(len(chapter_commands) == 1, f"Expected one chapter heading in {chapter}")
    chapter_labels = [argument(text, command) for command in commands(text, {"label"})
                      if argument(text, command).startswith("ch:")]
    require(len(chapter_labels) == 1, f"Expected one ch: label in {chapter}")
    chapter_label = chapter_labels[0]
    require(bool(SAFE_LABEL_RE.fullmatch(chapter_label)), f"Unsafe chapter label in {chapter}")
    tokens = commands(text, {"begin", "end"})
    exercises = []
    active = None
    for token in tokens:
        if argument(text, token) != "exercise":
            continue
        if token.name == "begin":
            require(active is None, f"Nested exercise in {chapter}")
            active = token
        else:
            require(active is not None, f"Unmatched exercise end in {chapter}")
            body = text[active.end:token.start]
            labels = [argument(body, label) for label in commands(body, {"label"})
                      if argument(body, label).startswith("ex:")]
            require(len(labels) == 1, f"Expected one exercise label at {chapter}:{line_at(text, active.start)}")
            require(bool(SAFE_LABEL_RE.fullmatch(labels[0])), f"Unsafe exercise label in {chapter}")
            require("sol:" not in body, f"Solution link already present in {chapter}: {labels[0]}")
            exercises.append(Exercise(labels[0], chapter, len(exercises),
                                      active.start, token.start, token.end))
            active = None
    require(active is None, f"Unclosed exercise in {chapter}")
    return chapter_label, exercises


def link_text(label: str) -> str:
    return ("\n\\par\\smallskip\\noindent{\\footnotesize\\normalfont\n"
            f"\\hyperref[sol:{label}]{{Solution on page~\\pageref*{{sol:{label}}}.}}}}\\par\n")


def build_plan(root: Path) -> tuple[dict, dict[Path, bytes], dict[Path, bytes], list[Path]]:
    snapshots: dict[Path, bytes] = {}

    def read(relative: str) -> str:
        path = root / relative
        require(path.is_file() and not path.is_symlink(), f"Missing or symlink source: {relative}")
        data = path.read_bytes()
        require(b"\r" not in data, f"Unexpected CR byte in {relative}")
        snapshots[path] = data
        return data.decode("utf-8")

    main_name = "haagerup_cft_textbook.tex"
    main = read(main_name)
    masked_main = uncomment(main)
    require(masked_main.count(r"\mainmatter") == 1 and masked_main.count(r"\appendix") == 1,
            "Main matter/appendix boundary is ambiguous")
    main_start, appendix_start = masked_main.index(r"\mainmatter"), masked_main.index(r"\appendix")
    require(main_start < appendix_start, "Appendix precedes main matter")
    inputs = commands(main, {"chapterinput"})
    chapter_order = [argument(main, item) for item in inputs if main_start < item.start < appendix_start]
    require(bool(chapter_order) and len(chapter_order) == len(set(chapter_order)),
            "Missing or duplicate main chapter inputs")
    require(all(SAFE_NAME_RE.fullmatch(name) for name in chapter_order), "Unsafe chapter basename")
    old_inputs = [item for item in inputs if argument(main, item) in AGGREGATES]
    require(Counter(argument(main, item) for item in old_inputs) == Counter(AGGREGATES),
            "Expected each original solution aggregate input exactly once")
    require(all(item.start > appendix_start for item in old_inputs), "Solution aggregate outside appendix")
    for first, second in zip(old_inputs, old_inputs[1:]):
        only_whitespace(main[first.end:second.start], "between aggregate solution inputs")

    all_exercises, chapter_labels, chapter_texts = {}, {}, {}
    for name in chapter_order:
        text = read(f"chapters/{name}.tex")
        chapter_texts[name] = text
        chapter_label, exercises = extract_exercises(name, text)
        chapter_labels[name] = chapter_label
        for exercise in exercises:
            require(exercise.label not in all_exercises, f"Duplicate exercise label: {exercise.label}")
            all_exercises[exercise.label] = exercise
    require(len(chapter_labels.values()) == len(set(chapter_labels.values())), "Duplicate chapter labels")

    blocks, removed_sections, outputs, deletes = [], {}, {}, []
    for name in AGGREGATES:
        relative = f"chapters/{name}.tex"
        text = read(relative)
        extracted, sections = extract_solutions(relative, text)
        blocks.extend(extracted)
        removed_sections[relative] = sections
        outputs[root / f"editorial/source_drafts/{name}.tex.txt"] = snapshots[root / relative]
        deletes.append(root / relative)

    counts = Counter(label for block in blocks for label in block.labels)
    require(not [label for label, count in counts.items() if count != 1],
            f"Duplicate solutions: {[label for label, count in counts.items() if count != 1]}")
    require(set(counts) == set(all_exercises),
            f"Solution/exercise mismatch; missing={sorted(set(all_exercises) - set(counts))}, "
            f"unknown={sorted(set(counts) - set(all_exercises))}")

    by_chapter = defaultdict(list)
    shared = []
    for block in blocks:
        chapters = {all_exercises[label].chapter for label in block.labels}
        require(len(chapters) == 1,
                f"Shared solution crosses chapters: {block.source}:{block.line}: {block.labels}")
        name = chapters.pop()
        by_chapter[name].append(block)
        if len(block.labels) > 1:
            orders = [all_exercises[label].order for label in block.labels]
            shared.append({"chapter": name, "labels": list(block.labels),
                           "placement": "earliest covered exercise",
                           "consecutive": sorted(orders) == list(range(min(orders), max(orders) + 1))})

    mappings, solution_inputs = [], []
    for name in chapter_order:
        chapter_blocks = sorted(by_chapter[name],
                                key=lambda block: min(all_exercises[label].order for label in block.labels))
        if not chapter_blocks:
            continue
        relative = f"solutions/{name}.tex"
        solution_inputs.append(r"\input{" + relative.removesuffix(".tex") + "}")
        generated = r"\section{Solutions for Chapter~\ref{" + chapter_labels[name] + "}}\n\n"
        for block in chapter_blocks:
            title = block.heading if block.heading.rstrip().endswith(".") else block.heading + "."
            generated += r"\paragraph{" + title + "}\n\\phantomsection\n"
            generated += "\n".join(r"\label{sol:" + label + "}" for label in block.labels)
            body_start = len(generated)
            generated += block.body
            body_end = len(generated)
            require(generated[body_start:body_end] == block.body, "Solution body preservation failed")
            generated += "\n\n"
            mappings.append({"exercise_labels": list(block.labels), "chapter": name,
                             "source": block.source, "source_line": block.line,
                             "source_heading": block.heading, "target": relative,
                             "body_sha256": digest(block.body.encode("utf-8")),
                             "body_characters": len(block.body),
                             "target_body_span_characters": [body_start, body_end]})
        generated_labels = [argument(generated, label) for label in commands(generated, {"label"})
                            if argument(generated, label).startswith("sol:")]
        expected = {"sol:" + label for block in chapter_blocks for label in block.labels}
        require(set(generated_labels) == expected and len(generated_labels) == len(expected),
                f"Anchor coverage failed for {relative}")
        outputs[root / relative] = generated.encode("utf-8")

        text = chapter_texts[name]
        exercises = sorted((ex for ex in all_exercises.values() if ex.chapter == name),
                           key=lambda ex: ex.end_start, reverse=True)
        changed = text
        for exercise in exercises:
            changed = changed[:exercise.end_start] + link_text(exercise.label) + changed[exercise.end_start:]
        restored = changed
        for exercise in exercises:
            require(restored.count(link_text(exercise.label)) == 1,
                    f"Backlink count failed for {exercise.label}")
            restored = restored.replace(link_text(exercise.label), "", 1)
        require(restored == text, f"Chapter preservation failed for {name}")
        outputs[root / f"chapters/{name}.tex"] = changed.encode("utf-8")

    new_main = main[:old_inputs[0].start] + "\n".join(solution_inputs) + main[old_inputs[-1].end:]
    outputs[root / main_name] = new_main.encode("utf-8")
    for path in outputs:
        require(not path.is_symlink(), f"Symlink output refused: {path}")
        if path not in snapshots:
            require(not path.exists(), f"New output already exists: {path.relative_to(root)}")
    for path, data in snapshots.items():
        labels = [argument(data.decode("utf-8"), item) for item in commands(data.decode("utf-8"), {"label"})]
        require(not any(label.startswith("sol:") for label in labels),
                f"Existing solution anchors in {path.relative_to(root)}")

    plan = {"scope": "Text-only solution reorganization; no mathematics or body wording changed",
            "main_chapter_order": chapter_order,
            "exercise_count": len(all_exercises), "solution_block_count": len(blocks),
            "solution_file_count": len(solution_inputs), "shared_solution_blocks": shared,
            "removed_grouping_headings": removed_sections, "solutions": mappings,
            "source_sha256": {str(path.relative_to(root)): digest(data) for path, data in snapshots.items()},
            "output_sha256": {str(path.relative_to(root)): digest(data) for path, data in outputs.items()},
            "delete_after_archiving": [str(path.relative_to(root)) for path in deletes],
            "script_sha256": digest(Path(__file__).read_bytes()),
            "checks": {"complete_exercise_coverage": True, "unique_solutions": True,
                       "no_unmatched_text": True, "same_chapter_shared_blocks": True,
                       "solution_bodies_preserved_verbatim": True,
                       "chapter_changes_are_only_solution_links": True,
                       "new_solution_anchors_unique_and_complete": True}}
    plan["plan_sha256"] = digest(json.dumps(plan, sort_keys=True).encode("utf-8"))
    return plan, snapshots, outputs, deletes


def write_report(path: Path, report: dict) -> None:
    require(not path.is_symlink(), f"Symlink report refused: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent,
                                     prefix=".solution-report-", delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(payload)
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def apply_plan(root: Path, snapshots: dict[Path, bytes], outputs: dict[Path, bytes],
               deletes: list[Path]) -> None:
    for path, original in snapshots.items():
        require(path.is_file() and path.read_bytes() == original,
                f"Source changed during planning: {path.relative_to(root)}")
    for path in outputs:
        if path not in snapshots:
            require(not path.exists(), f"Output appeared during planning: {path.relative_to(root)}")
    touched, created, removed = [], [], []
    with tempfile.TemporaryDirectory(prefix=".solution-stage-", dir=root / "editorial") as folder:
        stage = Path(folder)
        staged = {}
        for index, (path, data) in enumerate(outputs.items()):
            temporary = stage / str(index)
            temporary.write_bytes(data)
            staged[path] = temporary
        try:
            # Dict insertion order archives originals first and updates main last.
            for path, temporary in staged.items():
                path.parent.mkdir(parents=True, exist_ok=True)
                if path in snapshots:
                    require(path.read_bytes() == snapshots[path], f"Source changed before write: {path}")
                    touched.append(path)
                else:
                    require(not path.exists(), f"Output appeared before write: {path}")
                    created.append(path)
                os.replace(temporary, path)
            for path in deletes:
                require(path.read_bytes() == snapshots[path], f"Aggregate changed before removal: {path}")
                path.unlink()
                removed.append(path)
            for path, data in outputs.items():
                require(path.read_bytes() == data, f"Post-write verification failed: {path}")
        except BaseException:
            for path in touched + removed:
                path.write_bytes(snapshots[path])
            for path in created:
                path.unlink(missing_ok=True)
            raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true", help="Validate and report; do not edit book sources (default)")
    mode.add_argument("--apply", action="store_true", help="Apply only the exact previously dry-run plan")
    parser.add_argument("--root", type=Path, default=ROOT, help="Textbook root (for a copied fixture)")
    args = parser.parse_args()
    root = args.root.resolve()
    dry_path = root / "editorial/solution_reorganization_dry_run.json"
    applied_path = root / "editorial/solution_reorganization_applied.json"
    try:
        plan, snapshots, outputs, deletes = build_plan(root)
        if args.apply:
            require(dry_path.is_file(), "Run --dry-run and review its report before --apply")
            prior = json.loads(dry_path.read_text(encoding="utf-8"))
            require(prior.get("mode") == "dry-run" and prior.get("plan_sha256") == plan["plan_sha256"],
                    "Sources or script changed since dry run; repeat --dry-run and review the new report")
            require(not applied_path.exists(), "An applied transformation report already exists")
            apply_plan(root, snapshots, outputs, deletes)
        plan["mode"] = "applied" if args.apply else "dry-run"
        plan["timestamp_utc"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        report_path = applied_path if args.apply else dry_path
        write_report(report_path, plan)
        print(json.dumps({"mode": plan["mode"], "exercises": plan["exercise_count"],
                          "solution_blocks": plan["solution_block_count"],
                          "solution_files": plan["solution_file_count"],
                          "plan_sha256": plan["plan_sha256"],
                          "report": str(report_path)}, indent=2))
        return 0
    except (InvalidSource, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"Solution reorganization refused: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

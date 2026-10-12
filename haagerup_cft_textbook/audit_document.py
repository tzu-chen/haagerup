#!/usr/bin/env python3
"""Check textbook source integrity and cross-references; no research arithmetic."""
from collections import Counter
from pathlib import Path
import ast
import json
import re
import unicodedata

from build import source_hashes

ROOT = Path(__file__).resolve().parent


def uncomment(line):
    return re.split(r"(?<!\\)%", line, maxsplit=1)[0]


def command_bodies(text, names):
    """Read balanced-brace arguments, including nested reference commands."""
    pattern = re.compile(r"\\(?:" + "|".join(names) + r")\*?\{")
    for match in pattern.finditer(text):
        start = end = match.end()
        depth = 1
        while end < len(text) and depth:
            if text[end] == "{" and (end == 0 or text[end - 1] != "\\"):
                depth += 1
            elif text[end] == "}" and (end == 0 or text[end - 1] != "\\"):
                depth -= 1
            end += 1
        if depth:
            raise ValueError("Unclosed argument after " + match.group())
        yield text[start:end - 1]


def main():
    paths = sorted(ROOT.glob("*.tex"))
    for directory in ("chapters", "figures", "solutions"):
        paths.extend(sorted((ROOT / directory).glob("*.tex")))
    texts = {}
    errors = []
    for path in paths:
        data = path.read_bytes()
        bad = [(i, b) for i, b in enumerate(data) if b < 32 and b not in (9, 10)]
        if bad:
            errors.append({"file": str(path.relative_to(ROOT)), "control_bytes": bad})
        decoded = data.decode()
        invisible = [(i, f"U+{ord(c):04X}") for i, c in enumerate(decoded)
                     if unicodedata.category(c) == "Cf"]
        if invisible:
            errors.append({"file": str(path.relative_to(ROOT)),
                           "invisible_format_characters": invisible})
        texts[path] = "\n".join(uncomment(line) for line in decoded.splitlines())
    labels = Counter()
    refs = set()
    for path, text in texts.items():
        labels.update(re.findall(r"\\label\{([^}]+)\}", text))
        refs.update(re.findall(r"\\(?:eqref|ref|pageref|autoref)\*?\{([^}]+)\}", text))
        refs.update(re.findall(r"\\hyperref\[([^]]+)\]", text))
        for name in re.findall(r"\\chapterinput\{([^}]+)\}", text):
            if "#" not in name and not (ROOT / "chapters" / (name + ".tex")).is_file():
                errors.append({"file": str(path.relative_to(ROOT)), "missing_chapter": name})
        for name in re.findall(r"\\input\{([^}]+)\}", text):
            if "#" not in name and not (ROOT / (name + ".tex")).is_file():
                errors.append({"file": str(path.relative_to(ROOT)), "missing_input": name})
        for name in re.findall(r"\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}", text):
            if "#" not in name and not (ROOT / name).is_file():
                errors.append({"file": str(path.relative_to(ROOT)), "missing_figure": name})
    for label in sorted(refs - labels.keys()):
        errors.append({"undefined_reference": label})
    for label, count in labels.items():
        if count > 1:
            errors.append({"duplicate_label": label, "count": count})
    for path in ROOT.glob("*.py"):
        try:
            ast.parse(path.read_text(), filename=str(path))
        except SyntaxError as exc:
            errors.append({"python_syntax": str(exc)})
    all_text = "\n".join(texts.values())
    exercises = re.findall(r"\\begin\{exercise\}.*?\\end\{exercise\}", all_text, re.S)
    exercise_labels = []
    for exercise in exercises:
        found = re.search(r"\\label\{([^}]+)\}", exercise)
        if found:
            exercise_labels.append(found.group(1))
        else:
            errors.append({"exercise_without_label": exercise[:100]})
    solution_text = "\n".join(
        text for path, text in texts.items()
        if "solutions" in path.name or path.parent.name == "solutions")
    solution_headings = "\n".join(command_bodies(solution_text, ("paragraph", "subsection")))
    solved_labels = set(re.findall(r"\\ref\{(ex:[^}]+)\}", solution_headings))
    missing_solutions = sorted(set(exercise_labels) - solved_labels)
    if missing_solutions:
        errors.append({"exercises_without_dedicated_solution_heading": missing_solutions})
    main_text = texts[ROOT / "haagerup_cft_textbook.tex"]
    main_body = main_text.split(r"\mainmatter", 1)[1].split(r"\appendix", 1)[0]
    main_chapters = len(re.findall(r"\\chapterinput\{", main_body))
    included_chapters = set(re.findall(r"\\chapterinput\{([^}]+)\}", main_text))
    for path in (ROOT / "chapters").glob("*.tex"):
        if path.stem not in included_chapters:
            errors.append({"chapter_source_not_in_book": path.name})
    result = {
        "scope": "Text integrity and document structure only; no mathematical certification",
        "source_sha256": source_hashes(),
        "tex_files": len(paths),
        "chapters": sum(len(re.findall(r"\\chapter(?:\*)?\{", text)) for text in texts.values()),
        "main_chapters": main_chapters,
        "exercises": len(exercises),
        "worked_examples": len(re.findall(r"\\begin\{example\}", all_text)),
        "exercise_labels": len(exercise_labels),
        "exercises_with_dedicated_solutions": len(set(exercise_labels) & solved_labels),
        "exercise_labels_without_solution": missing_solutions,
        "label_count": len(labels),
        "reference_count": len(refs),
        "errors": errors,
    }
    (ROOT / "editorial/document_audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key != "source_sha256"}, indent=2))
    raise SystemExit(bool(errors))


if __name__ == "__main__":
    main()

"""Small, independent reader for the saved Gate 4 and Gate 5 witnesses.

Run ONLY through ~/.local/bin/research-safe-run from the repository root, with a 1024 MiB
address cap. No research module, numerical package, vertex-mode engine, or
linear solver is imported. Existing files are opened read-only; the sole
output must be new. Fraction arithmetic checks all 12 saved projected Gate 4
residuals. Gate 5 extraction checks the eight recorded lower-relation linear
combinations and the two bottom scalars, but DOES NOT recalculate VOA modes.

Allocation review: SQLite caches total at most 8 MiB, each decoded record is
capped at 8 MiB, each exact vector has at most 5000 states, and no vector cache
is retained. One target residual and one source vector are live at a time.
Expected RSS <192 MiB; fail at 384 MiB or 360 seconds. Root alone runs jobs.
"""

import argparse
from contextlib import ExitStack
from fractions import Fraction as Q
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic
import zlib


ROOT = Path(__file__).resolve().parents[1]
PRE = "hi_cft_20260923_"
MIB = 1024 ** 2
ZERO = (Q(0),) * 4
SOURCE_HASHES = {}
STARTED = monotonic()


def need(condition, message):
    if not condition:
        raise ValueError(message)


def boundary():
    need(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 384 * 1024,
         "384 MiB RSS review boundary")
    need(monotonic() - STARTED < 360, "360 second review boundary")


def sha(path):
    path = Path(path).resolve()
    global_guard = (Path.home() / ".local/bin/research-safe-run").resolve()
    need(path.is_relative_to(ROOT) or path == global_guard,
         "input outside repository or canonical resource guard")
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(MIB), b""):
            h.update(block)
            boundary()
    digest = h.hexdigest()
    SOURCE_HASHES[str(path if path == global_guard else path.relative_to(ROOT))] = digest
    return digest


def read_json(path):
    path = Path(path).resolve()
    need(path.stat().st_size <= 8 * MIB, "JSON size cap")
    sha(path)
    return json.loads(path.read_text())


def decode(blob, digest=None):
    need(len(blob) <= 8 * MIB, "compressed record cap")
    z = zlib.decompressobj()
    raw = z.decompress(blob, 8 * MIB + 1)
    need(len(raw) <= 8 * MIB and z.eof and not z.unconsumed_tail
         and not z.unused_data, "decoded record cap or trailing bytes")
    if digest is not None:
        need(hashlib.sha256(raw).hexdigest() == digest, "record digest")
    return json.loads(raw)


def database(stack, name):
    path = (ROOT / name).resolve()
    need(path.stat().st_size <= 512 * MIB, "database size cap")
    need(not any(Path(str(path) + s).exists() for s in ("-wal", "-journal")),
         "database must be closed")
    sha(path)
    db = sqlite3.connect(path.as_uri() + "?mode=ro&immutable=1", uri=True)
    stack.callback(db.close)
    db.execute("PRAGMA cache_size=-1024")
    db.execute("PRAGMA mmap_size=0")
    return db


def field(value):
    need(len(value) == 4 and all(isinstance(q, str) and len(q) < 2600 for q in value),
         "four bounded rational strings required")
    out = tuple(Q(q) for q in value)
    need(all(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) <= 8192
             for q in out), "rational coefficient size cap")
    return out


def multiply(a, b):
    out = [Q(0)] * 4
    # Basis bits encode s and t. A common s contributes 13, a common t -3.
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    common = i & j
                    out[i ^ j] += x * y * (13 if common & 1 else 1) * (-3 if common & 2 else 1)
    return tuple(out)


def add(target, key, value, sign=1):
    result = tuple(a + sign * b for a, b in zip(target.get(key, ZERO), value))
    if any(result):
        target[key] = result
    else:
        target.pop(key, None)


def packed(vector):
    return [[name, [str(q) for q in c]] for name, c in sorted(vector.items())]


def read_vector(db, name):
    found = db.execute("SELECT record,digest,terms,bits FROM vectors WHERE name=?", (name,)).fetchone()
    need(found is not None, "missing vector " + name)
    blob, digest, terms, bits = found
    rows = decode(blob, digest)
    need(len(rows) == terms <= 5000 and bits <= 2048, "projected vector bounds")
    result = {}
    for momentum, oscillators, coefficients in rows:
        need(len(momentum) == 8 and all(isinstance(v, int) for v in momentum), "momentum encoding")
        need(all(isinstance(v, int) and 0 <= v < 32 for v in oscillators), "oscillator encoding")
        key = (tuple(momentum), tuple(oscillators))
        value = field(coefficients)
        need(key not in result and any(value), "duplicate or zero state coefficient")
        result[key] = value
    return result


def gate4(stack):
    exact = database(stack, PRE + "c8two_h4_singlet_exact.sqlite")
    prime = database(stack, PRE + "c8two_h4_singlet_prime.sqlite")
    normal = database(stack, PRE + "next_n4_strong_skip_v2.sqlite")
    expected = [(0, "r3_000950"), (1, "r3_000916"), (1, "r3_000920"),
                (2, "r3_000916"), (2, "r3_000920"), (3, "r3_000922"),
                (4, "r3_000873"), (5, "r3_000879"), (5, "r3_000897"),
                (6, "r3_000882"), (6, "r3_000898"), (7, "r3_000902")]
    factors = [{"axis": axis, "higher_weight": h, "e": e, "f": f, "lambda": h * (h + 2) // 4}
               for axis, bound, e, f in (("LEFT", 4, 1, 2), ("RIGHT", 24, 4, 5))
               for h in range(2, bound + 1, 2)]
    normal_words = {}

    def normal_word(idx):
        if str(idx) not in normal_words:
            row = normal.execute("SELECT word FROM rows WHERE id=?", (idx,)).fetchone()
            need(row is not None, "missing original normal word")
            word = json.loads(row[0])
            need(word["kind"] in ("normal_descendant", "normal_S2_product", "current_lowering"), "normal word kind")
            if word["kind"] == "current_lowering":
                need(0 <= word["normal_row"] < idx and word["current"] in (2, 5)
                     and word["mode"] == 0, "acyclic current-lowering recipe")
                normal_word(word["normal_row"])
            normal_words[str(idx)] = word
        return normal_words[str(idx)]

    columns = {}
    for idx, word in prime.execute("SELECT id,word FROM rows ORDER BY id"):
        word = json.loads(word)
        need(word["factors"] == factors and word["recipe"]["kind"] == "normal", "projected column recipe")
        normal_word(word["recipe"]["column"])
        columns[str(idx)] = word
    need(set(columns) == {str(i) for i in range(21)}, "21 selected projected columns")
    answers = []
    for idx, blob, digest, passed in exact.execute("SELECT id,record,digest,passed FROM relations ORDER BY id"):
        need(idx == len(answers) and idx < 12 and passed == 1, "Gate 4 record numbering")
        record = decode(blob, digest)
        word = record["word"]
        need(word == json.loads(prime.execute("SELECT word FROM targets WHERE id=?", (idx,)).fetchone()[0]), "target recipe agreement")
        need(word["factors"] == factors and word["recipe"]["kind"] == "target", "target projector")
        need((word["recipe"]["operator"], word["recipe"]["input"]) == expected[idx], "target pair")
        need(record["source_target_id"] == idx and record["weight"] == [0, 0]
             and record["residual"] == [] and record["exact_residual_zero"], "record assertion")
        residual = read_vector(exact, "target:" + str(idx))
        target_terms = len(residual)
        need(target_terms == record["target_terms"], "target term count")
        coefficients = record["normal_column_coefficients"]
        need(len(coefficients) == len({j for j, _ in coefficients}) <= 21, "column coefficient uniqueness")
        for j, encoded in coefficients:
            need(str(j) in columns, "unknown projected column")
            c = field(encoded)
            source = read_vector(exact, "grade5:" + str(j))  # Historical prefix, actual grade FOUR.
            for state, value in source.items():
                add(residual, state, multiply(c, value), -1)
            del source
            boundary()
        need(not residual, "nonzero independent Fraction residual")
        answers.append({"id": idx, "operator": expected[idx][0], "input": expected[idx][1],
                        "target_terms": target_terms, "record_sha256": digest,
                        "normal_column_coefficients": coefficients,
                        "independent_fraction_residual_zero": True})
    need(len(answers) == 12, "all twelve projected residuals required")
    return {"projector_factors": factors, "projected_columns": columns,
            "original_normal_word_dag": normal_words, "identities": answers,
            "scope": "Full arithmetic replay against saved projected vectors. Ambient VOA modes, projector application, raising premises and saturation ranks are NOT recalculated."}


def gate5(stack):
    summary = read_json(ROOT / (PRE + "c8two_gate5_verified.json"))
    lower = database(stack, PRE + "next_structure_lower_closure.sqlite")
    h4 = database(stack, PRE + "c8two_targeted_h4_trimmed_v2/block_p0_m2.sqlite")
    pairs = [(0, 3, 537), (1, 3, 777), (2, 3, 1017), (3, 6, 1286),
             (4, 6, 1526), (5, 3, 1737), (6, 3, 1977), (7, 3, 2217)]
    need(len(summary["charged_pair_checks"]) == 8, "eight charged pairs")
    checks = []
    for saved, (a, b, idx) in zip(summary["charged_pair_checks"], pairs):
        need((saved["a"], saved["b"]) == (a, b), "charged pair order")
        decomposition = summary["primitive_decompositions"][str(b)]
        need(len(decomposition) == 1 and len(saved["lower_records"]) == 1, "one-term primitive coordinate")
        right, multiplier = decomposition[0]
        recipe, target_sha, relation, residual = lower.execute(
            "SELECT recipe,target_sha256,relation,residual FROM identities WHERE id=?", (idx,)).fetchone()
        need(json.loads(recipe) == ["weight_two", a, right, 0, 3], "lower product recipe")
        digest = hashlib.sha256(recipe.encode() + b"\0" + target_sha.encode() + b"\0" + relation + b"\0" + residual).hexdigest()
        need(digest == saved["lower_records"][0]["record_sha256"] and decode(residual) == [], "lower record integrity")
        answer = {}
        for name, c in decode(relation):
            add(answer, name, multiply(field(multiplier), field(c)))
        need(packed(answer) == saved["normal3_coefficients"], "exact lower relation combination")
        if (a, b) != (4, 6):
            need(not answer, "seven exactly zero brackets")
        else:
            need(answer == {"r3_000141": field(["0", "-54087/138650", "20899/138650", "0"]),
                            "r3_000150": field(["0", "6853/110920", "20779/110920", "0"])}, "printed nonzero bracket")
        checks.append(saved)
    for saved in summary["bottom_witnesses"]:
        blob, digest, passed = h4.execute("SELECT record,digest,passed FROM relations WHERE name=?", (saved["record_name"],)).fetchone()
        record = decode(blob, digest)
        need(passed == 1 and digest == saved["record_sha256"] and record["residual"] == []
             and record["exact_residual_zero"], "bottom witness record")
        negative = [(j, field(c)) for j, c in record["normal_word_coefficients"] if j < 0]
        need(negative == [(-3, field(saved["P4_minus_coefficient"]))]
             and any(negative[0][1]), "nonzero triplet coefficient")
    folder = ROOT / (PRE + "next_grade4_checkpoint/checkpoint_000024")
    manifest = read_json(folder / "manifest.json")
    block = folder / "grade3_weight_2_8.json.gz"
    need(sha(block) == manifest["files_sha256"][block.name], "checkpoint block binding")
    with gzip.open(block, "rb") as stream:
        raw = stream.read(8 * MIB + 1)
    need(len(raw) <= 8 * MIB, "checkpoint decoded size cap")
    rows = {row["id"]: row for row in json.loads(raw)["rows"]}
    recipes = {}
    for name, source, scale, elimination in (
            ("r3_000141", "source1", ["1/25", "0", "0", "4/25"], []),
            ("r3_000150", "source2", ["81/71", "0", "0", "-15/71"],
             [[["-7/20", "0", "0", "3/20"], "r3_000141"]])):
        row = rows[name]
        need(row["recipe"] == {"op": "mode", "left": "current1", "n": -1, "right": source}
             and row["scale"] == scale and row["elimination"] == elimination, "printed normal-product normalization")
        recipes[name] = {key: row[key] for key in ("recipe", "scale", "elimination")}
    return {"primitive_decompositions": summary["primitive_decompositions"],
            "charged_pair_checks": checks, "bottom_witnesses": summary["bottom_witnesses"],
            "normal_product_recipes": recipes,
            "scope": "Recombines eight saved exact lower identities, extracts two nonzero quotient scalars, and authenticates two printed normal-word recipes. Does NOT reconstruct their vertex-mode targets or reprove charged spanning."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    need(Path.cwd().resolve() == ROOT, "run from repository root")
    need(0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024 * MIB, "use guarded address cap <=1024 MiB")
    parent = Path("/proc") / str(os.getppid())
    argv = (parent / "cmdline").read_bytes().split(b"\0")
    need(len(argv) > 1, "missing launcher parent")
    launcher = Path(os.fsdecode(argv[1]))
    if not launcher.is_absolute():
        launcher = (parent / "cwd").resolve() / launcher
    need(launcher.resolve() == (Path.home() / ".local/bin/research-safe-run").resolve(),
         "global research-safe-run watchdog parent required")
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError("360 second cap")))
    signal.alarm(360)
    output = Path(args.output).resolve()
    need(output.is_relative_to(ROOT) and not output.exists(), "output must be new and inside repository")
    sha(Path(__file__))
    sha(Path.home() / ".local/bin/research-safe-run")
    with ExitStack() as stack:
        four = gate4(stack)
        five = gate5(stack)
    result = {"format": "human-readable-finite-witnesses-v1", "status": "all_requested_saved_data_checks_passed",
              "field_basis": ["1", "s", "t", "s*t"], "field_relations": {"s^2": 13, "t^2": -3},
              "gate4": four, "gate5": five, "source_sha256": SOURCE_HASHES,
              "seconds": monotonic() - STARTED,
              "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              "scope": "Independent saved-vector arithmetic and readable extraction only. The existing full source ledger and mathematical reduction lemmas remain required."}
    with output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "gate4_residuals": 12,
                      "gate5_lower_combinations": 8, "seconds": result["seconds"],
                      "peak_rss_KiB": result["peak_rss_KiB"]}), flush=True)


if __name__ == "__main__":
    main()

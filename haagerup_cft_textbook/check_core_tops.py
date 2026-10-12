#!/usr/bin/env python3
"""Reconstruct the fourteen displayed core tops with exact rational arithmetic.

Run only from this directory through the canonical shared guard:
  ~/.local/bin/research-safe-run --wait --limit-mib 128 --memory-mib 128 \
      --threads 1 -- timeout 30s python3 check_core_tops.py

This checks the minimization and bookkeeping formulas printed in c05. It
does not construct the core VOA, verify its lattice embedding, or certify
the representation-theoretic premises of the universal top bound.

Allocation estimate: 25 new candidate rows of small Fractions plus at most
11 retained minimizers from the preceding row, 14 result rows, and short
integer coefficient arrays. Arithmetic storage
is below 1 MiB; standard-library interpreter and JSON output below 32 MiB RSS.
The 128 MiB AS/whole-job budget leaves mapping and file-cache headroom. No
scientific libraries, subprocesses, workers, or large certificates.
"""
from datetime import datetime, timezone
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import os
import resource
import time


def main():
    if not __debug__:
        raise SystemExit("Do not use Python optimization; checks require assertions.")
    if not os.environ.get("RESEARCH_SAFE_RUN_ACTIVE"):
        raise SystemExit("Use the canonical research-safe-run.")
    root = Path(__file__).resolve().parent
    if Path.cwd().resolve() != root or len(os.sched_getaffinity(0)) != 1:
        raise SystemExit("Run in the textbook directory with --threads 1.")
    start = time.monotonic()

    # Rows are (ordinary top dimension, actual lowest weight, 4680 W).
    expected = {
        "x": [(1, F(0), 0), (1, F(2,15), 600), (5, F(2,5), 10440),
              (9, F(4,5), 56640), (2, F(1,3), 5520), (14, F(1), 148560),
              (6, F(4,5), 54240)],
        "y": [(1, F(2,5), 7800), (7, F(8,15), 36960), (15, F(4,5), 110880),
              (2, F(1,5), 4080), (14, F(11,15), 81480), (6, F(2,5), 18240),
              (2, F(1,5), 4920)],
    }
    rows = {}
    for family in ("x", "y"):
        for a in range(7):
            candidates = []
            for m in range(-12, 13):
                # One representative k of -5m mod13 in [-6,6].
                k = (-5*m + 6) % 13 - 6
                left = F(m % 2, 4)
                potts = (F(0) if m % 3 == 0 else F(2,3)) if family == "x" else (
                    F(2,5) if m % 3 == 0 else F(1,15))
                pf = F(a*(a+1), 15) - F(k*k, 13) + max(0, abs(k)-a)
                assert pf >= 0
                h = F(m*m, 156) + left + potts + pf
                multiplicity = 2 if m % 2 else 1
                candidates.append((h, m, multiplicity, left, potts, pf))
            lowest = min(row[0] for row in candidates)
            minimizers = [row for row in candidates if row[0] == lowest]
            dimension = sum(row[2] for row in minimizers)
            L = sum(row[2]*row[3] for row in minimizers)
            P = sum(row[2]*row[4] for row in minimizers)
            Z = sum(row[2]*row[5] for row in minimizers)
            Q = sum(row[2]*row[1]**2 for row in minimizers)
            W = L + F(83,6084)*Q + F(25,6)*P + F(25,26)*Z
            assert (dimension, lowest, 4680*W) == expected[family][a], (
                family, a, dimension, lowest, 4680*W)
            rows[f"{family}{a}"] = {
                "dimension": dimension, "lowest_weight": str(lowest),
                "charges_with_multiplicities": [[row[1], row[2]] for row in minimizers],
                "L": str(L), "P": str(P), "Z": str(Z), "Q": Q,
                "W": str(W), "4680_W": int(4680*W),
            }

    # The finite cutoff is justified charge by charge: a small representative
    # bounds the lattice--Potts contribution, independent of its PF summand.
    for family in ("x", "y"):
        for m in range(-6, 7):
            potts = (F(0) if m % 3 == 0 else F(2,3)) if family == "x" else (
                F(2,5) if m % 3 == 0 else F(1,15))
            assert F(m*m,156) + F(m % 2,4) + potts <= F(14,13)
    assert F(13*13,156) > F(14,13)

    # Check both representation-theoretic inequality vectors against the
    # enumerated positive Cartan-charge multiplicities, without assuming that
    # an individual core top is itself a complete right-current multiplet.
    def charge_count(label, charge):
        return sum(mult for m,mult in rows[label]["charges_with_multiplicities"] if m == charge)

    for label in rows:
        assert charge_count(label, 12) == int(label == "x5")
        assert charge_count(label, 10) == int(label == "y2")
        assert charge_count(label, 9) == 2*int(label in ("x5", "x6"))
        assert charge_count(label, 7) == 2*int(label == "y4")

    # Coefficients of the displayed nonnegative remainder after the two
    # multiples of y2-x5 and y4-x5-x6 have been extracted.
    positive = {
        "x0":7956, "x1":7356, "x2":29340, "x3":14964,
        "x4":10392, "x5":0, "x6":22212,
        "y0":156, "y1":18732, "y2":0, "y3":11832,
        "y4":1188, "y5":29496, "y6":10992,
    }
    for label, row in rows.items():
        left = F(4680*17,10)*row["dimension"] - row["4680_W"]
        right = positive[label]
        right += 8460*(int(label == "y2") - int(label == "x5"))
        right += 28716*(int(label == "y4") - int(label in ("x5", "x6")))
        assert left == right, (label, left, right)
        assert positive[label] >= 0

    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    report = {
        "scope": "Exact core-top minimization, charge multiplicities and 17/10 trace certificate from the printed formulas; no VOA embedding verification",
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "script_sha256": sha(Path(__file__)),
        "chapter_sha256_at_check": sha(root / "chapters/c05_branching.tex"),
        "guard_sha256": sha(Path.home() / ".local/bin/research-safe-run"),
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "elapsed_seconds": time.monotonic()-start,
        "max_rss_mib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024,
        "measurement_scope": "Elapsed time and process high-water RSS sampled before final report serialization",
        "rows": rows,
        "finite_cutoff_checked": True,
        "charge_inequality_coefficients_checked": True,
        "nonnegative_trace_certificate_checked": True,
        "all_checks_passed": True,
    }
    output = root / "editorial/core_top_check_results.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"result": str(output.relative_to(root)),
                      "core_tops": len(rows), "all_checks_passed": True,
                      "elapsed_seconds": report["elapsed_seconds"],
                      "max_rss_mib": report["max_rss_mib"]}, indent=2))


if __name__ == "__main__":
    main()

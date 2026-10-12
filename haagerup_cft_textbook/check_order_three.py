#!/usr/bin/env python3
"""Check the small order-three coefficient example by exact integer algebra.

Run from this directory, only through the canonical shared guard:
  ~/.local/bin/research-safe-run --wait --limit-mib 128 --memory-mib 128 \
      --threads 1 -- timeout 30s python3 check_order_three.py

Allocation estimate: one 3-by-3 matrix of four-integer normal forms, short
products, and four 3-by-3 diagnostic tables; arithmetic storage below 1 MiB.
Standard-library interpreter and output are conservatively below 32 MiB RSS.
A 128 MiB address-space and whole-job budget includes additional mapping
and charged-cache headroom. No libraries, workers, floating arithmetic,
eigensolvers, analytic-function evaluation, or large certificates are used.
"""

from datetime import datetime, timezone
import hashlib
import itertools
import json
import os
from pathlib import Path
import resource
import time


def qmul(x, y):
    """Multiply a+b*delta using delta**2=3*delta+1."""
    a, b = x
    c, d = y
    return (a*c + b*d, a*d + b*c + 3*b*d)


class R:
    """Z[delta,p]/(delta^2-3delta-1,p^2-p+delta).

    The ordered basis is (1,delta,p,delta*p). Monic relations make this
    a free rank-four integer algebra; a zero normal form proves an identity
    at every simultaneous complex root, without choosing an embedding.
    """
    __slots__ = ("a",)

    def __init__(self, value=0):
        if isinstance(value, R):
            self.a = value.a
        elif isinstance(value, int):
            self.a = (value, 0, 0, 0)
        else:
            if len(value) != 4 or not all(isinstance(x, int) for x in value):
                raise TypeError("A normal form has four integer coefficients")
            self.a = tuple(value)

    def __add__(self, other):
        return R(tuple(x+y for x,y in zip(self.a, R(other).a)))

    __radd__ = __add__

    def __neg__(self):
        return R(tuple(-x for x in self.a))

    def __sub__(self, other):
        return self + (-R(other))

    def __rsub__(self, other):
        return R(other) - self

    def __mul__(self, other):
        # (A+Bp)(C+Dp) = AC-delta*BD + (AD+BC+BD)p.
        x, y = self.a, R(other).a
        ac = qmul(x[:2], y[:2])
        bd = qmul(x[2:], y[2:])
        dbd = qmul((0, 1), bd)
        ad = qmul(x[:2], y[2:])
        bc = qmul(x[2:], y[:2])
        return R((ac[0]-dbd[0], ac[1]-dbd[1],
                  ad[0]+bc[0]+bd[0], ad[1]+bc[1]+bd[1]))

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.a == R(other).a


def main():
    if not __debug__:
        raise SystemExit("Do not use Python optimization; checks require assertions.")
    if not os.environ.get("RESEARCH_SAFE_RUN_ACTIVE"):
        raise SystemExit("Use the canonical research-safe-run.")
    root = Path(__file__).resolve().parent
    if Path.cwd().resolve() != root:
        raise SystemExit("Run from the textbook directory.")
    if len(os.sched_getaffinity(0)) != 1:
        raise SystemExit("Use --threads 1 and the guard's one-CPU affinity.")
    started = time.monotonic()
    delta, p = R((0, 1, 0, 0)), R((0, 0, 1, 0))
    q, tau = 1-p, delta-1
    B = [[delta-2, R(-1), R(-1)],
         [R(-1), R(-1), p], [R(-1), q, R(-1)]]

    def b(i, j):
        return B[i % 3][j % 3]

    # Auxiliary identities also used to clear the displayed denominators.
    assert p+q == 1 and p*q == delta
    assert tau*tau == delta+2
    assert delta*(delta-3) == 1
    assert tau*tau*tau*(delta-3) == 7-delta
    assert tau*(delta-2) == 3  # In particular tau is invertible over Q.

    for g,h in itertools.product(range(3), repeat=2):
        assert b(g,h) == b(-h,g-h) == b(h-g,-g), (g,h)
    assert sum(b(h,0) for h in range(3)) == -tau*(delta-3)

    for g,h in itertools.product(range(3), repeat=2):
        lhs = sum(b(m+g,h)*b(h,m) for m in range(3))
        rhs = (delta+2)*int(g == 0) - (2*delta-5)*int(h == 0)
        assert lhs == rhs, ("quadratic", g,h,lhs.a,rhs.a)

    representative_tables = {}
    for g,h,k,ell in itertools.product(range(3), repeat=4):
        lhs = sum(b(m,g+h)*b(g,m+k)*b(h,m+ell) for m in range(3))
        rhs = tau*b(g+ell,k)*b(h+k,ell) - (7-delta)*int(g == h == 0)
        assert lhs == rhs, ("cubic",g,h,k,ell,lhs.a,rhs.a)
        if (g,h) in ((0,0),(0,1),(1,1),(1,2)):
            table = representative_tables.setdefault(f"{g},{h}", [[None]*3 for _ in range(3)])
            table[k][ell] = list(lhs.a)

    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    report = {
        "scope": "Exact order-three polynomial coefficient identities only; no unitary reconstruction or CFT verification",
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "coefficient_algebra": "Z[delta,p]/(delta^2-3delta-1,p^2-p+delta)",
        "basis": ["1", "delta", "p", "delta*p"],
        "rotation_triples": 9,
        "axis_sums": 1,
        "quadratic_equations": 9,
        "cubic_equations": 81,
        "all_residual_normal_forms_zero": True,
        "representative_cubic_lhs_tables_rows_k_columns_l": representative_tables,
        "script_sha256": sha(Path(__file__)),
        "chapter_source_at_check_sha256": sha(root / "chapters/f05_arithmetic.tex"),
        "guard_sha256": sha(Path.home() / ".local/bin/research-safe-run"),
        "guard_unit": os.environ["RESEARCH_SAFE_RUN_ACTIVE"],
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "max_rss_mib_linux": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024,
        "seconds": time.monotonic() - started,
    }
    (root / "editorial/order_three_check_results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key,value in report.items()
                      if key != "representative_cubic_lhs_tables_rows_k_columns_l"}, indent=2))


if __name__ == "__main__":
    main()

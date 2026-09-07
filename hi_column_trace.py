"""Numerical tests of the scalar completion and periodic trace conjectures.

Construction uses only the one-column barrier. Further Q and trace checks
are numerical, and an orthant scan covers one fixed Fourier-sign chamber,
not the entire set of one-column solutions.
"""

import argparse
import itertools
import mpmath as mp

from hi_column_barrier import barrier_solution
from hi_shintani_ghost import quadratic_residual


def traces(delta, w, A):
    n = len(w)
    phase_sum = mp.fsum(w) / (delta - 1)
    operator_trace = mp.fsum(A[a][2 * a % n] for a in range(n))
    return phase_sum, operator_trace, phase_sum ** 2 + operator_trace - 2


def predicted_sum(n):
    # The formula is periodic modulo 40; multiples of 5 have exact target 0.
    if n % 5 == 0:
        return mp.mpf(0)
    residue = n % 40
    return (mp.sqrt(2) * mp.sin(mp.pi * residue / 4)
            * mp.sin(mp.pi * residue / 5) / mp.sin(2 * mp.pi / 5))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+",
                        default=[3, 5, 7, 9, 11, 13, 15, 17, 19, 25, 31, 51, 79])
    parser.add_argument("--scan", type=int, nargs="*", default=[5, 7, 9, 11, 13, 15, 17])
    parser.add_argument("--digits", type=int, default=80)
    args = parser.parse_args()
    mp.mp.dps = args.digits + 40
    tolerance = mp.power(10, -args.digits + 20)
    print("NUMERICAL TRACE TESTS; no uniform completion theorem is asserted.", flush=True)
    for n in args.orders:
        delta, w, A, *_ = barrier_solution(n, args.digits)
        s, tr, defect = traces(delta, w, A)
        print(f"n={n}: S={mp.nstr(s, 16)}; Tr(R)={mp.nstr(tr, 16)}; "
              f"scalar defect={mp.nstr(abs(defect), 6)}; "
              f"period-40 defect={mp.nstr(abs(s-predicted_sum(n)), 6)}", flush=True)

    for n in args.scan:
        counts = [0, 0, 0, 0]
        largest_accepted_q = mp.mpf(0)
        largest_rejected_q = mp.mpf(0)
        for signs in itertools.product((-1, 1), repeat=(n - 1) // 2):
            delta, w, A, *_ = barrier_solution(n, args.digits, signs)
            q = quadratic_residual(A, delta)
            s, tr, defect = traces(delta, w, A)
            q_pass, trace_pass = q < tolerance, abs(defect) < tolerance
            counts[2 * q_pass + trace_pass] += 1
            if trace_pass:
                largest_accepted_q = max(largest_accepted_q, q)
            else:
                largest_rejected_q = max(largest_rejected_q, q)
            if q_pass != trace_pass:
                print(f"  DISAGREEMENT n={n}, signs={signs}, Q={mp.nstr(q, 10)}, "
                      f"scalar={mp.nstr(defect, 10)}, S={mp.nstr(s, 16)}", flush=True)
        print(f"n={n}, {2**((n-1)//2)} orthants in ONE Fourier chamber: "
              f"neither/trace-only/Q-only/both={counts}; "
              f"max Q accepted={mp.nstr(largest_accepted_q, 6)}, "
              f"max Q rejected={mp.nstr(largest_rejected_q, 6)}", flush=True)
    print("NUMERICAL TRACE TESTS FINISHED", flush=True)


if __name__ == "__main__":
    main()
